import V185TrunkScan23Chunk0042

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_255181 : List Nat := [1, 6, 2, 2, 2, 1, 2, 2, 1, 4]
def baseStart_255181 : Nat := 118140960795 + 255181 * 2 ^ 59
def prefixEnd_255181 : Nat := 4983230072969 + 3 ^ 40 * 255181 * 2
def baseEnd_255181 : Nat := 43676835631690445621317

theorem tailTrace_255181 : CollatzResearch.WordTrace tailWord_255181 prefixEnd_255181 43676835631690445621317 := by
  unfold tailWord_255181
  simp only [CollatzResearch.WordTrace]
  refine ⟨9307215688530293290213397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6204810459020195526808931 9307215688530293290213397)
  ·
    refine ⟨436275735399857497978753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 9307215688530293290213397 436275735399857497978753)
    ·
      refine ⟨327206801549893123484065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 436275735399857497978753 327206801549893123484065)
      ·
        refine ⟨245405101162419842613049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 327206801549893123484065 245405101162419842613049)
        ·
          refine ⟨184053825871814881959787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 245405101162419842613049 184053825871814881959787)
          ·
            refine ⟨276080738807722322939681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184053825871814881959787 276080738807722322939681)
            ·
              refine ⟨207060554105791742204761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 276080738807722322939681 207060554105791742204761)
              ·
                refine ⟨155295415579343806653571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 207060554105791742204761 155295415579343806653571)
                ·
                  refine ⟨232943123369015709980357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 155295415579343806653571 232943123369015709980357)
                  ·
                    refine ⟨43676835631690445621317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 232943123369015709980357 43676835631690445621317)
                    ·
                      rfl

theorem cell23_255181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 1, 2, 2, 1, 4].length) (baseStart_255181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_255181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_255181 prefixEnd_255181 := by exact prefixLift 255181
  have htrace : WordTrace (prefixWord ++ tailWord_255181) baseStart_255181 baseEnd_255181 := by
    simpa [prefixWord, tailWord_255181, baseEnd_255181] using wordTrace_append hprefix tailTrace_255181
  have hstable : (prefixWord ++ tailWord_255181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_255181).length < 2 ^ (prefixWord ++ tailWord_255181).sum := by decide
  have hdescent : baseEnd_255181 < baseStart_255181 := by decide
  rcases family_descends (prefixWord ++ tailWord_255181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_255182 : List Nat := [4, 1, 1, 1, 16]
def baseStart_255182 : Nat := 118140960795 + 255182 * 2 ^ 59
def prefixEnd_255182 : Nat := 4983230072969 + 3 ^ 40 * 255182 * 2
def baseEnd_255182 : Nat := 179740768690981938205

theorem tailTrace_255182 : CollatzResearch.WordTrace tailWord_255182 prefixEnd_255182 179740768690981938205 := by
  unfold tailWord_255182
  simp only [CollatzResearch.WordTrace]
  refine ⟨1163406520190833807624975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6204834774351113640666533 1163406520190833807624975)
  ·
    refine ⟨1745109780286250711437463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1163406520190833807624975 1745109780286250711437463)
    ·
      refine ⟨2617664670429376067156195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1745109780286250711437463 2617664670429376067156195)
      ·
        refine ⟨3926497005644064100734293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2617664670429376067156195 3926497005644064100734293)
        ·
          refine ⟨179740768690981938205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 16 3926497005644064100734293 179740768690981938205)
          ·
            rfl

theorem cell23_255182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 16].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 16].length) (baseStart_255182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_255182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_255182 prefixEnd_255182 := by exact prefixLift 255182
  have htrace : WordTrace (prefixWord ++ tailWord_255182) baseStart_255182 baseEnd_255182 := by
    simpa [prefixWord, tailWord_255182, baseEnd_255182] using wordTrace_append hprefix tailTrace_255182
  have hstable : (prefixWord ++ tailWord_255182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_255182).length < 2 ^ (prefixWord ++ tailWord_255182).sum := by decide
  have hdescent : baseEnd_255182 < baseStart_255182 := by decide
  rcases family_descends (prefixWord ++ tailWord_255182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_255226 : List Nat := [3, 1, 1, 1, 1, 4, 2, 2, 4, 1, 3]
def baseStart_255226 : Nat := 118140960795 + 255226 * 2 ^ 59
def prefixEnd_255226 : Nat := 4983230072969 + 3 ^ 40 * 255226 * 2
def baseEnd_255226 : Nat := 131053613524523660801243

theorem tailTrace_255226 : CollatzResearch.WordTrace tailWord_255226 prefixEnd_255226 131053613524523660801243 := by
  unfold tailWord_255226
  simp only [CollatzResearch.WordTrace]
  refine ⟨2327214243341816493900383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6205904648911510650401021 2327214243341816493900383)
  ·
    refine ⟨3490821365012724740850575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2327214243341816493900383 3490821365012724740850575)
    ·
      refine ⟨5236232047519087111275863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3490821365012724740850575 5236232047519087111275863)
      ·
        refine ⟨7854348071278630666913795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5236232047519087111275863 7854348071278630666913795)
        ·
          refine ⟨11781522106917946000370693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7854348071278630666913795 11781522106917946000370693)
          ·
            refine ⟨2209035395047114875069505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11781522106917946000370693 2209035395047114875069505)
            ·
              refine ⟨1656776546285336156302129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2209035395047114875069505 1656776546285336156302129)
              ·
                refine ⟨1242582409714002117226597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1656776546285336156302129 1242582409714002117226597)
                ·
                  refine ⟨232984201821375396979987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1242582409714002117226597 232984201821375396979987)
                  ·
                    refine ⟨349476302732063095469981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 232984201821375396979987 349476302732063095469981)
                    ·
                      refine ⟨131053613524523660801243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 349476302732063095469981 131053613524523660801243)
                      ·
                        rfl

theorem cell23_255226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 2, 4, 1, 3].length) (baseStart_255226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_255226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_255226 prefixEnd_255226 := by exact prefixLift 255226
  have htrace : WordTrace (prefixWord ++ tailWord_255226) baseStart_255226 baseEnd_255226 := by
    simpa [prefixWord, tailWord_255226, baseEnd_255226] using wordTrace_append hprefix tailTrace_255226
  have hstable : (prefixWord ++ tailWord_255226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_255226).length < 2 ^ (prefixWord ++ tailWord_255226).sum := by decide
  have hdescent : baseEnd_255226 < baseStart_255226 := by decide
  rcases family_descends (prefixWord ++ tailWord_255226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_255230 : List Nat := [4, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3]
def baseStart_255230 : Nat := 118140960795 + 255230 * 2 ^ 59
def prefixEnd_255230 : Nat := 4983230072969 + 3 ^ 40 * 255230 * 2
def baseEnd_255230 : Nat := 131055667447141645151225

theorem tailTrace_255230 : CollatzResearch.WordTrace tailWord_255230 prefixEnd_255230 131055667447141645151225 := by
  unfold tailWord_255230
  simp only [CollatzResearch.WordTrace]
  refine ⟨1163625358169096832343393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6206001910235183105831429 1163625358169096832343393)
  ·
    refine ⟨872719018626822624257545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1163625358169096832343393 872719018626822624257545)
    ·
      refine ⟨654539263970116968193159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 872719018626822624257545 654539263970116968193159)
      ·
        refine ⟨981808895955175452289739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 654539263970116968193159 981808895955175452289739)
        ·
          refine ⟨1472713343932763178434609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 981808895955175452289739 1472713343932763178434609)
          ·
            refine ⟨1104535007949572383825957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1472713343932763178434609 1104535007949572383825957)
            ·
              refine ⟨207100313990544821967367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1104535007949572383825957 207100313990544821967367)
              ·
                refine ⟨310650470985817232951051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 207100313990544821967367 310650470985817232951051)
                ·
                  refine ⟨465975706478725849426577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 310650470985817232951051 465975706478725849426577)
                  ·
                    refine ⟨349481779859044387069933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 465975706478725849426577 349481779859044387069933)
                    ·
                      refine ⟨131055667447141645151225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 349481779859044387069933 131055667447141645151225)
                      ·
                        rfl

theorem cell23_255230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3].length) (baseStart_255230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_255230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_255230 prefixEnd_255230 := by exact prefixLift 255230
  have htrace : WordTrace (prefixWord ++ tailWord_255230) baseStart_255230 baseEnd_255230 := by
    simpa [prefixWord, tailWord_255230, baseEnd_255230] using wordTrace_append hprefix tailTrace_255230
  have hstable : (prefixWord ++ tailWord_255230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_255230).length < 2 ^ (prefixWord ++ tailWord_255230).sum := by decide
  have hdescent : baseEnd_255230 < baseStart_255230 := by decide
  rcases family_descends (prefixWord ++ tailWord_255230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_255243 : List Nat := [1, 1, 1, 1, 5, 3, 3, 2, 2, 1, 3]
def baseStart_255243 : Nat := 118140960795 + 255243 * 2 ^ 59
def prefixEnd_255243 : Nat := 4983230072969 + 3 ^ 40 * 255243 * 2
def baseEnd_255243 : Nat := 131062342695650094288665

theorem tailTrace_255243 : CollatzResearch.WordTrace tailWord_255243 prefixEnd_255243 131062342695650094288665 := by
  unfold tailWord_255243
  simp only [CollatzResearch.WordTrace]
  refine ⟨9309477014305677878970383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6206318009537118585980255 9309477014305677878970383)
  ·
    refine ⟨13964215521458516818455575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9309477014305677878970383 13964215521458516818455575)
    ·
      refine ⟨20946323282187775227683363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13964215521458516818455575 20946323282187775227683363)
      ·
        refine ⟨31419484923281662841525045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20946323282187775227683363 31419484923281662841525045)
        ·
          refine ⟨2945576711557655891392973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 31419484923281662841525045 2945576711557655891392973)
          ·
            refine ⟨1104591266834120959272365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2945576711557655891392973 1104591266834120959272365)
            ·
              refine ⟨414221725062795359727137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1104591266834120959272365 414221725062795359727137)
              ·
                refine ⟨310666293797096519795353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 414221725062795359727137 310666293797096519795353)
                ·
                  refine ⟨232999720347822389846515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 310666293797096519795353 232999720347822389846515)
                  ·
                    refine ⟨349499580521733584769773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 232999720347822389846515 349499580521733584769773)
                    ·
                      refine ⟨131062342695650094288665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 349499580521733584769773 131062342695650094288665)
                      ·
                        rfl

theorem cell23_255243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 3, 2, 2, 1, 3].length) (baseStart_255243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_255243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_255243 prefixEnd_255243 := by exact prefixLift 255243
  have htrace : WordTrace (prefixWord ++ tailWord_255243) baseStart_255243 baseEnd_255243 := by
    simpa [prefixWord, tailWord_255243, baseEnd_255243] using wordTrace_append hprefix tailTrace_255243
  have hstable : (prefixWord ++ tailWord_255243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_255243).length < 2 ^ (prefixWord ++ tailWord_255243).sum := by decide
  have hdescent : baseEnd_255243 < baseStart_255243 := by decide
  rcases family_descends (prefixWord ++ tailWord_255243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_255283 : List Nat := [1, 1, 1, 2, 5, 2, 1, 2, 4, 2, 2]
def baseStart_255283 : Nat := 118140960795 + 255283 * 2 ^ 59
def prefixEnd_255283 : Nat := 4983230072969 + 3 ^ 40 * 255283 * 2
def baseEnd_255283 : Nat := 131082881921829937788481

theorem tailTrace_255283 : CollatzResearch.WordTrace tailWord_255283 prefixEnd_255283 131082881921829937788481 := by
  unfold tailWord_255283
  simp only [CollatzResearch.WordTrace]
  refine ⟨9310935934160764710426503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6207290622773843140284335 9310935934160764710426503)
  ·
    refine ⟨13966403901241147065639755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9310935934160764710426503 13966403901241147065639755)
    ·
      refine ⟨20949605851861720598459633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13966403901241147065639755 20949605851861720598459633)
      ·
        refine ⟨15712204388896290448844725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20949605851861720598459633 15712204388896290448844725)
        ·
          refine ⟨1473019161459027229579193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15712204388896290448844725 1473019161459027229579193)
          ·
            refine ⟨1104764371094270422184395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1473019161459027229579193 1104764371094270422184395)
            ·
              refine ⟨1657146556641405633276593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1104764371094270422184395 1657146556641405633276593)
              ·
                refine ⟨1242859917481054224957445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1657146556641405633276593 1242859917481054224957445)
                ·
                  refine ⟨233036234527697667179521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1242859917481054224957445 233036234527697667179521)
                  ·
                    refine ⟨174777175895773250384641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 233036234527697667179521 174777175895773250384641)
                    ·
                      refine ⟨131082881921829937788481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 174777175895773250384641 131082881921829937788481)
                      ·
                        rfl

theorem cell23_255283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 2, 4, 2, 2].length) (baseStart_255283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_255283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_255283 prefixEnd_255283 := by exact prefixLift 255283
  have htrace : WordTrace (prefixWord ++ tailWord_255283) baseStart_255283 baseEnd_255283 := by
    simpa [prefixWord, tailWord_255283, baseEnd_255283] using wordTrace_append hprefix tailTrace_255283
  have hstable : (prefixWord ++ tailWord_255283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_255283).length < 2 ^ (prefixWord ++ tailWord_255283).sum := by decide
  have hdescent : baseEnd_255283 < baseStart_255283 := by decide
  rcases family_descends (prefixWord ++ tailWord_255283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_255306 : List Nat := [3, 1, 2, 1, 1, 1, 1, 8, 5]
def baseStart_255306 : Nat := 118140960795 + 255306 * 2 ^ 59
def prefixEnd_255306 : Nat := 4983230072969 + 3 ^ 40 * 255306 * 2
def baseEnd_255306 : Nat := 14566076886320371977875

theorem tailTrace_255306 : CollatzResearch.WordTrace tailWord_255306 prefixEnd_255306 14566076886320371977875 := by
  unfold tailWord_255306
  simp only [CollatzResearch.WordTrace]
  refine ⟨2327943703269359909628443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6207849875384959759009181 2327943703269359909628443)
  ·
    refine ⟨3491915554904039864442665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2327943703269359909628443 3491915554904039864442665)
    ·
      refine ⟨2618936666178029898331999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3491915554904039864442665 2618936666178029898331999)
      ·
        refine ⟨3928404999267044847497999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2618936666178029898331999 3928404999267044847497999)
        ·
          refine ⟨5892607498900567271246999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3928404999267044847497999 5892607498900567271246999)
          ·
            refine ⟨8838911248350850906870499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5892607498900567271246999 8838911248350850906870499)
            ·
              refine ⟨13258366872526276360305749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8838911248350850906870499 13258366872526276360305749)
              ·
                refine ⟨155371486787417301097333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13258366872526276360305749 155371486787417301097333)
                ·
                  refine ⟨14566076886320371977875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 155371486787417301097333 14566076886320371977875)
                  ·
                    rfl

theorem cell23_255306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 8, 5].length) (baseStart_255306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_255306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_255306 prefixEnd_255306 := by exact prefixLift 255306
  have htrace : WordTrace (prefixWord ++ tailWord_255306) baseStart_255306 baseEnd_255306 := by
    simpa [prefixWord, tailWord_255306, baseEnd_255306] using wordTrace_append hprefix tailTrace_255306
  have hstable : (prefixWord ++ tailWord_255306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_255306).length < 2 ^ (prefixWord ++ tailWord_255306).sum := by decide
  have hdescent : baseEnd_255306 < baseStart_255306 := by decide
  rcases family_descends (prefixWord ++ tailWord_255306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_255316 : List Nat := [2, 4, 1, 1, 2, 1, 2, 1, 1, 5, 3]
def baseStart_255316 : Nat := 118140960795 + 255316 * 2 ^ 59
def prefixEnd_255316 : Nat := 4983230072969 + 3 ^ 40 * 255316 * 2
def baseEnd_255316 : Nat := 131099826783428308675829

theorem tailTrace_255316 : CollatzResearch.WordTrace tailWord_255316 prefixEnd_255316 131099826783428308675829 := by
  unfold tailWord_255316
  simp only [CollatzResearch.WordTrace]
  refine ⟨4656069771520605673188901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6208093028694140897585201 4656069771520605673188901)
  ·
    refine ⟨873013082160113563722919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4656069771520605673188901 873013082160113563722919)
    ·
      refine ⟨1309519623240170345584379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 873013082160113563722919 1309519623240170345584379)
      ·
        refine ⟨1964279434860255518376569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1309519623240170345584379 1964279434860255518376569)
        ·
          refine ⟨1473209576145191638782427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1964279434860255518376569 1473209576145191638782427)
          ·
            refine ⟨2209814364217787458173641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1473209576145191638782427 2209814364217787458173641)
            ·
              refine ⟨1657360773163340593630231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2209814364217787458173641 1657360773163340593630231)
              ·
                refine ⟨2486041159745010890445347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1657360773163340593630231 2486041159745010890445347)
                ·
                  refine ⟨3729061739617516335668021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2486041159745010890445347 3729061739617516335668021)
                  ·
                    refine ⟨349599538089142156468877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3729061739617516335668021 349599538089142156468877)
                    ·
                      refine ⟨131099826783428308675829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 349599538089142156468877 131099826783428308675829)
                      ·
                        rfl

theorem cell23_255316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 1, 1, 5, 3].length) (baseStart_255316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_255316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_255316 prefixEnd_255316 := by exact prefixLift 255316
  have htrace : WordTrace (prefixWord ++ tailWord_255316) baseStart_255316 baseEnd_255316 := by
    simpa [prefixWord, tailWord_255316, baseEnd_255316] using wordTrace_append hprefix tailTrace_255316
  have hstable : (prefixWord ++ tailWord_255316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_255316).length < 2 ^ (prefixWord ++ tailWord_255316).sum := by decide
  have hdescent : baseEnd_255316 < baseStart_255316 := by decide
  rcases family_descends (prefixWord ++ tailWord_255316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_255317 : List Nat := [1, 3, 2, 2, 3, 1, 4, 1, 2, 2, 2]
def baseStart_255317 : Nat := 118140960795 + 255317 * 2 ^ 59
def prefixEnd_255317 : Nat := 4983230072969 + 3 ^ 40 * 255317 * 2
def baseEnd_255317 : Nat := 131100340264082804763325

theorem tailTrace_255317 : CollatzResearch.WordTrace tailWord_255317 prefixEnd_255317 131100340264082804763325 := by
  unfold tailWord_255317
  simp only [CollatzResearch.WordTrace]
  refine ⟨9312176016037588517164205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6208117344025059011442803 9312176016037588517164205)
  ·
    refine ⟨3492066006014095693936577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9312176016037588517164205 3492066006014095693936577)
    ·
      refine ⟨2619049504510571770452433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3492066006014095693936577 2619049504510571770452433)
      ·
        refine ⟨1964287128382928827839325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2619049504510571770452433 1964287128382928827839325)
        ·
          refine ⟨736607673143598310439747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1964287128382928827839325 736607673143598310439747)
          ·
            refine ⟨1104911509715397465659621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 736607673143598310439747 1104911509715397465659621)
            ·
              refine ⟨207170908071637024811179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1104911509715397465659621 207170908071637024811179)
              ·
                refine ⟨310756362107455537216769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 207170908071637024811179 310756362107455537216769)
                ·
                  refine ⟨233067271580591652912577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 310756362107455537216769 233067271580591652912577)
                  ·
                    refine ⟨174800453685443739684433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 233067271580591652912577 174800453685443739684433)
                    ·
                      refine ⟨131100340264082804763325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 174800453685443739684433 131100340264082804763325)
                      ·
                        rfl

theorem cell23_255317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 4, 1, 2, 2, 2].length) (baseStart_255317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_255317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_255317 prefixEnd_255317 := by exact prefixLift 255317
  have htrace : WordTrace (prefixWord ++ tailWord_255317) baseStart_255317 baseEnd_255317 := by
    simpa [prefixWord, tailWord_255317, baseEnd_255317] using wordTrace_append hprefix tailTrace_255317
  have hstable : (prefixWord ++ tailWord_255317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_255317).length < 2 ^ (prefixWord ++ tailWord_255317).sum := by decide
  have hdescent : baseEnd_255317 < baseStart_255317 := by decide
  rcases family_descends (prefixWord ++ tailWord_255317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_255356 : List Nat := [2, 2, 2, 1, 1, 1, 3, 4, 2, 1, 4]
def baseStart_255356 : Nat := 118140960795 + 255356 * 2 ^ 59
def prefixEnd_255356 : Nat := 4983230072969 + 3 ^ 40 * 255356 * 2
def baseEnd_255356 : Nat := 131120366009608152175645

theorem tailTrace_255356 : CollatzResearch.WordTrace tailWord_255356 prefixEnd_255356 131120366009608152175645 := by
  unfold tailWord_255356
  simp only [CollatzResearch.WordTrace]
  refine ⟨4656799231448149088916961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6209065641930865451889281 4656799231448149088916961)
  ·
    refine ⟨3492599423586111816687721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4656799231448149088916961 3492599423586111816687721)
    ·
      refine ⟨2619449567689583862515791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3492599423586111816687721 2619449567689583862515791)
      ·
        refine ⟨3929174351534375793773687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2619449567689583862515791 3929174351534375793773687)
        ·
          refine ⟨5893761527301563690660531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3929174351534375793773687 5893761527301563690660531)
          ·
            refine ⟨8840642290952345535990797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5893761527301563690660531 8840642290952345535990797)
            ·
              refine ⟨3315240859107129575996549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8840642290952345535990797 3315240859107129575996549)
              ·
                refine ⟨621607661082586795499353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3315240859107129575996549 621607661082586795499353)
                ·
                  refine ⟨466205745811940096624515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 621607661082586795499353 466205745811940096624515)
                  ·
                    refine ⟨699308618717910144936773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 466205745811940096624515 699308618717910144936773)
                    ·
                      refine ⟨131120366009608152175645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 699308618717910144936773 131120366009608152175645)
                      ·
                        rfl

theorem cell23_255356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 4, 2, 1, 4].length) (baseStart_255356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_255356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_255356 prefixEnd_255356 := by exact prefixLift 255356
  have htrace : WordTrace (prefixWord ++ tailWord_255356) baseStart_255356 baseEnd_255356 := by
    simpa [prefixWord, tailWord_255356, baseEnd_255356] using wordTrace_append hprefix tailTrace_255356
  have hstable : (prefixWord ++ tailWord_255356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_255356).length < 2 ^ (prefixWord ++ tailWord_255356).sum := by decide
  have hdescent : baseEnd_255356 < baseStart_255356 := by decide
  rcases family_descends (prefixWord ++ tailWord_255356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_255390 : List Nat := [4, 3, 1, 2, 2, 1, 1, 1, 1, 3, 4]
def baseStart_255390 : Nat := 118140960795 + 255390 * 2 ^ 59
def prefixEnd_255390 : Nat := 4983230072969 + 3 ^ 40 * 255390 * 2
def baseEnd_255390 : Nat := 131137824351861019150489

theorem tailTrace_255390 : CollatzResearch.WordTrace tailWord_255390 prefixEnd_255390 131137824351861019150489 := by
  unfold tailWord_255390
  simp only [CollatzResearch.WordTrace]
  refine ⟨1164354818096640248071453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6209892363182081323047749 1164354818096640248071453)
  ·
    refine ⟨436633056786240093026795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1164354818096640248071453 436633056786240093026795)
    ·
      refine ⟨654949585179360139540193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 436633056786240093026795 654949585179360139540193)
      ·
        refine ⟨491212188884520104655145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 654949585179360139540193 491212188884520104655145)
        ·
          refine ⟨368409141663390078491359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 491212188884520104655145 368409141663390078491359)
          ·
            refine ⟨552613712495085117737039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 368409141663390078491359 552613712495085117737039)
            ·
              refine ⟨828920568742627676605559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 552613712495085117737039 828920568742627676605559)
              ·
                refine ⟨1243380853113941514908339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 828920568742627676605559 1243380853113941514908339)
                ·
                  refine ⟨1865071279670912272362509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1243380853113941514908339 1865071279670912272362509)
                  ·
                    refine ⟨699401729876592102135941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1865071279670912272362509 699401729876592102135941)
                    ·
                      refine ⟨131137824351861019150489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 699401729876592102135941 131137824351861019150489)
                      ·
                        rfl

theorem cell23_255390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 1, 1, 1, 3, 4].length) (baseStart_255390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_255390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_255390 prefixEnd_255390 := by exact prefixLift 255390
  have htrace : WordTrace (prefixWord ++ tailWord_255390) baseStart_255390 baseEnd_255390 := by
    simpa [prefixWord, tailWord_255390, baseEnd_255390] using wordTrace_append hprefix tailTrace_255390
  have hstable : (prefixWord ++ tailWord_255390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_255390).length < 2 ^ (prefixWord ++ tailWord_255390).sum := by decide
  have hdescent : baseEnd_255390 < baseStart_255390 := by decide
  rcases family_descends (prefixWord ++ tailWord_255390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_255413 : List Nat := [1, 3, 3, 2, 2, 1, 3, 2, 6]
def baseStart_255413 : Nat := 118140960795 + 255413 * 2 ^ 59
def prefixEnd_255413 : Nat := 4983230072969 + 3 ^ 40 * 255413 * 2
def baseEnd_255413 : Nat := 14572181600768269906987

theorem tailTrace_255413 : CollatzResearch.WordTrace tailWord_255413 prefixEnd_255413 14572181600768269906987 := by
  unfold tailWord_255413
  simp only [CollatzResearch.WordTrace]
  refine ⟨9315677423689796912658893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6210451615793197941772595 9315677423689796912658893)
  ·
    refine ⟨3493379033883673842247085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9315677423689796912658893 3493379033883673842247085)
    ·
      refine ⟨1310017137706377690842657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3493379033883673842247085 1310017137706377690842657)
      ·
        refine ⟨982512853279783268131993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1310017137706377690842657 982512853279783268131993)
        ·
          refine ⟨736884639959837451098995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 982512853279783268131993 736884639959837451098995)
          ·
            refine ⟨1105326959939756176648493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 736884639959837451098995 1105326959939756176648493)
            ·
              refine ⟨414497609977408566243185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1105326959939756176648493 414497609977408566243185)
              ·
                refine ⟨310873207483056424682389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 414497609977408566243185 310873207483056424682389)
                ·
                  refine ⟨14572181600768269906987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 310873207483056424682389 14572181600768269906987)
                  ·
                    rfl

theorem cell23_255413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 3, 2, 6].length) (baseStart_255413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_255413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_255413 prefixEnd_255413 := by exact prefixLift 255413
  have htrace : WordTrace (prefixWord ++ tailWord_255413) baseStart_255413 baseEnd_255413 := by
    simpa [prefixWord, tailWord_255413, baseEnd_255413] using wordTrace_append hprefix tailTrace_255413
  have hstable : (prefixWord ++ tailWord_255413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_255413).length < 2 ^ (prefixWord ++ tailWord_255413).sum := by decide
  have hdescent : baseEnd_255413 < baseStart_255413 := by decide
  rcases family_descends (prefixWord ++ tailWord_255413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_255457 : List Nat := [1, 2, 3, 1, 2, 3, 3, 3, 1, 1, 3]
def baseStart_255457 : Nat := 118140960795 + 255457 * 2 ^ 59
def prefixEnd_255457 : Nat := 4983230072969 + 3 ^ 40 * 255457 * 2
def baseEnd_255457 : Nat := 131172227555712257012681

theorem tailTrace_255457 : CollatzResearch.WordTrace tailWord_255457 prefixEnd_255457 131172227555712257012681 := by
  unfold tailWord_255457
  simp only [CollatzResearch.WordTrace]
  refine ⟨9317282235530392427260625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6211521490353594951507083 9317282235530392427260625)
  ·
    refine ⟨6987961676647794320445469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9317282235530392427260625 6987961676647794320445469)
    ·
      refine ⟨2620485628742922870167051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6987961676647794320445469 2620485628742922870167051)
      ·
        refine ⟨3930728443114384305250577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2620485628742922870167051 3930728443114384305250577)
        ·
          refine ⟨2948046332335788228937933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3930728443114384305250577 2948046332335788228937933)
          ·
            refine ⟨1105517374625920585851725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2948046332335788228937933 1105517374625920585851725)
            ·
              refine ⟨414569015484720219694397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1105517374625920585851725 414569015484720219694397)
              ·
                refine ⟨155463380806770082385399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 414569015484720219694397 155463380806770082385399)
                ·
                  refine ⟨233195071210155123578099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 155463380806770082385399 233195071210155123578099)
                  ·
                    refine ⟨349792606815232685367149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 233195071210155123578099 349792606815232685367149)
                    ·
                      refine ⟨131172227555712257012681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 349792606815232685367149 131172227555712257012681)
                      ·
                        rfl

theorem cell23_255457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 3, 3, 1, 1, 3].length) (baseStart_255457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_255457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_255457 prefixEnd_255457 := by exact prefixLift 255457
  have htrace : WordTrace (prefixWord ++ tailWord_255457) baseStart_255457 baseEnd_255457 := by
    simpa [prefixWord, tailWord_255457, baseEnd_255457] using wordTrace_append hprefix tailTrace_255457
  have hstable : (prefixWord ++ tailWord_255457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_255457).length < 2 ^ (prefixWord ++ tailWord_255457).sum := by decide
  have hdescent : baseEnd_255457 < baseStart_255457 := by decide
  rcases family_descends (prefixWord ++ tailWord_255457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_255473 : List Nat := [1, 2, 2, 2, 3, 2, 2, 1, 4, 4]
def baseStart_255473 : Nat := 118140960795 + 255473 * 2 ^ 59
def prefixEnd_255473 : Nat := 4983230072969 + 3 ^ 40 * 255473 * 2
def baseEnd_255473 : Nat := 43726814415394731470869

theorem tailTrace_255473 : CollatzResearch.WordTrace tailWord_255473 prefixEnd_255473 43726814415394731470869 := by
  unfold tailWord_255473
  simp only [CollatzResearch.WordTrace]
  refine ⟨9317865803472427159843073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6211910535648284773228715 9317865803472427159843073)
  ·
    refine ⟨6988399352604320369882305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9317865803472427159843073 6988399352604320369882305)
    ·
      refine ⟨5241299514453240277411729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6988399352604320369882305 5241299514453240277411729)
      ·
        refine ⟨3930974635839930208058797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5241299514453240277411729 3930974635839930208058797)
        ·
          refine ⟨1474115488439973828022049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3930974635839930208058797 1474115488439973828022049)
          ·
            refine ⟨1105586616329980371016537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1474115488439973828022049 1105586616329980371016537)
            ·
              refine ⟨829189962247485278262403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1105586616329980371016537 829189962247485278262403)
              ·
                refine ⟨1243784943371227917393605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 829189962247485278262403 1243784943371227917393605)
                ·
                  refine ⟨233209676882105234511301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1243784943371227917393605 233209676882105234511301)
                  ·
                    refine ⟨43726814415394731470869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 233209676882105234511301 43726814415394731470869)
                    ·
                      rfl

theorem cell23_255473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 2, 1, 4, 4].length) (baseStart_255473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_255473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_255473 prefixEnd_255473 := by exact prefixLift 255473
  have htrace : WordTrace (prefixWord ++ tailWord_255473) baseStart_255473 baseEnd_255473 := by
    simpa [prefixWord, tailWord_255473, baseEnd_255473] using wordTrace_append hprefix tailTrace_255473
  have hstable : (prefixWord ++ tailWord_255473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_255473).length < 2 ^ (prefixWord ++ tailWord_255473).sum := by decide
  have hdescent : baseEnd_255473 < baseStart_255473 := by decide
  rcases family_descends (prefixWord ++ tailWord_255473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_255494 : List Nat := [6, 2, 1, 1, 2, 1, 1, 1, 3, 5]
def baseStart_255494 : Nat := 118140960795 + 255494 * 2 ^ 59
def prefixEnd_255494 : Nat := 4983230072969 + 3 ^ 40 * 255494 * 2
def baseEnd_255494 : Nat := 43730408779976204083337

theorem tailTrace_255494 : CollatzResearch.WordTrace tailWord_255494 prefixEnd_255494 43730408779976204083337 := by
  unfold tailWord_255494
  simp only [CollatzResearch.WordTrace]
  refine ⟨291207241762385867073673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 6212421157597565164238357 291207241762385867073673)
  ·
    refine ⟨218405431321789400305255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 291207241762385867073673 218405431321789400305255)
    ·
      refine ⟨327608146982684100457883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218405431321789400305255 327608146982684100457883)
      ·
        refine ⟨491412220474026150686825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 327608146982684100457883 491412220474026150686825)
        ·
          refine ⟨368559165355519613015119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 491412220474026150686825 368559165355519613015119)
          ·
            refine ⟨552838748033279419522679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 368559165355519613015119 552838748033279419522679)
            ·
              refine ⟨829258122049919129284019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 552838748033279419522679 829258122049919129284019)
              ·
                refine ⟨1243887183074878693926029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 829258122049919129284019 1243887183074878693926029)
                ·
                  refine ⟨466457693653079510222261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1243887183074878693926029 466457693653079510222261)
                  ·
                    refine ⟨43730408779976204083337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 466457693653079510222261 43730408779976204083337)
                    ·
                      rfl

theorem cell23_255494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 1, 1, 3, 5].length) (baseStart_255494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_255494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_255494 prefixEnd_255494 := by exact prefixLift 255494
  have htrace : WordTrace (prefixWord ++ tailWord_255494) baseStart_255494 baseEnd_255494 := by
    simpa [prefixWord, tailWord_255494, baseEnd_255494] using wordTrace_append hprefix tailTrace_255494
  have hstable : (prefixWord ++ tailWord_255494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_255494).length < 2 ^ (prefixWord ++ tailWord_255494).sum := by decide
  have hdescent : baseEnd_255494 < baseStart_255494 := by decide
  rcases family_descends (prefixWord ++ tailWord_255494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_255500 : List Nat := [2, 2, 1, 2, 5, 1, 1, 1, 3, 2, 3]
def baseStart_255500 : Nat := 118140960795 + 255500 * 2 ^ 59
def prefixEnd_255500 : Nat := 4983230072969 + 3 ^ 40 * 255500 * 2
def baseEnd_255500 : Nat := 131194307223855588774983

theorem tailTrace_255500 : CollatzResearch.WordTrace tailWord_255500 prefixEnd_255500 131194307223855588774983 := by
  unfold tailWord_255500
  simp only [CollatzResearch.WordTrace]
  refine ⟨4659425287187305385537977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6212567049583073847383969 4659425287187305385537977)
  ·
    refine ⟨3494568965390479039153483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4659425287187305385537977 3494568965390479039153483)
    ·
      refine ⟨5241853448085718558730225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3494568965390479039153483 5241853448085718558730225)
      ·
        refine ⟨3931390086064288919047669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5241853448085718558730225 3931390086064288919047669)
        ·
          refine ⟨368567820568527086160719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3931390086064288919047669 368567820568527086160719)
          ·
            refine ⟨552851730852790629241079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 368567820568527086160719 552851730852790629241079)
            ·
              refine ⟨829277596279185943861619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 552851730852790629241079 829277596279185943861619)
              ·
                refine ⟨1243916394418778915792429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 829277596279185943861619 1243916394418778915792429)
                ·
                  refine ⟨466468647907042093422161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1243916394418778915792429 466468647907042093422161)
                  ·
                    refine ⟨349851485930281570066621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 466468647907042093422161 349851485930281570066621)
                    ·
                      refine ⟨131194307223855588774983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 349851485930281570066621 131194307223855588774983)
                      ·
                        rfl

theorem cell23_255500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 1, 1, 3, 2, 3].length) (baseStart_255500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_255500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_255500 prefixEnd_255500 := by exact prefixLift 255500
  have htrace : WordTrace (prefixWord ++ tailWord_255500) baseStart_255500 baseEnd_255500 := by
    simpa [prefixWord, tailWord_255500, baseEnd_255500] using wordTrace_append hprefix tailTrace_255500
  have hstable : (prefixWord ++ tailWord_255500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_255500).length < 2 ^ (prefixWord ++ tailWord_255500).sum := by decide
  have hdescent : baseEnd_255500 < baseStart_255500 := by decide
  rcases family_descends (prefixWord ++ tailWord_255500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_255501 : List Nat := [1, 7, 1, 1, 2, 1, 2, 1, 2, 3, 2]
def baseStart_255501 : Nat := 118140960795 + 255501 * 2 ^ 59
def prefixEnd_255501 : Nat := 4983230072969 + 3 ^ 40 * 255501 * 2
def baseEnd_255501 : Nat := 131194820704510084862479

theorem tailTrace_255501 : CollatzResearch.WordTrace tailWord_255501 prefixEnd_255501 131194820704510084862479 := by
  unfold tailWord_255501
  simp only [CollatzResearch.WordTrace]
  refine ⟨9318887047370987941862357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6212591364913991961241571 9318887047370987941862357)
  ·
    refine ⟨218411415172757529887399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 9318887047370987941862357 218411415172757529887399)
    ·
      refine ⟨327617122759136294831099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218411415172757529887399 327617122759136294831099)
      ·
        refine ⟨491425684138704442246649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 327617122759136294831099 491425684138704442246649)
        ·
          refine ⟨368569263104028331684987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 491425684138704442246649 368569263104028331684987)
          ·
            refine ⟨552853894656042497527481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 368569263104028331684987 552853894656042497527481)
            ·
              refine ⟨414640420992031873145611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 552853894656042497527481 414640420992031873145611)
              ·
                refine ⟨621960631488047809718417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 414640420992031873145611 621960631488047809718417)
                ·
                  refine ⟨466470473616035857288813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 621960631488047809718417 466470473616035857288813)
                  ·
                    refine ⟨174926427606013446483305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 466470473616035857288813 174926427606013446483305)
                    ·
                      refine ⟨131194820704510084862479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 174926427606013446483305 131194820704510084862479)
                      ·
                        rfl

theorem cell23_255501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 2, 1, 2, 3, 2].length) (baseStart_255501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_255501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_255501 prefixEnd_255501 := by exact prefixLift 255501
  have htrace : WordTrace (prefixWord ++ tailWord_255501) baseStart_255501 baseEnd_255501 := by
    simpa [prefixWord, tailWord_255501, baseEnd_255501] using wordTrace_append hprefix tailTrace_255501
  have hstable : (prefixWord ++ tailWord_255501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_255501).length < 2 ^ (prefixWord ++ tailWord_255501).sum := by decide
  have hdescent : baseEnd_255501 < baseStart_255501 := by decide
  rcases family_descends (prefixWord ++ tailWord_255501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_255517 : List Nat := [1, 4, 2, 2, 1, 1, 5, 1, 1, 2, 3]
def baseStart_255517 : Nat := 118140960795 + 255517 * 2 ^ 59
def prefixEnd_255517 : Nat := 4983230072969 + 3 ^ 40 * 255517 * 2
def baseEnd_255517 : Nat := 131203036394982022262405

theorem tailTrace_255517 : CollatzResearch.WordTrace tailWord_255517 prefixEnd_255517 131203036394982022262405 := by
  unfold tailWord_255517
  simp only [CollatzResearch.WordTrace]
  refine ⟨9319470615313022674444805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6212980410208681782963203 9319470615313022674444805)
  ·
    refine ⟨1747400740371191751458401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9319470615313022674444805 1747400740371191751458401)
    ·
      refine ⟨1310550555278393813593801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1747400740371191751458401 1310550555278393813593801)
      ·
        refine ⟨982912916458795360195351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1310550555278393813593801 982912916458795360195351)
        ·
          refine ⟨1474369374688193040293027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 982912916458795360195351 1474369374688193040293027)
          ·
            refine ⟨2211554062032289560439541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1474369374688193040293027 2211554062032289560439541)
            ·
              refine ⟨207333193315527146291207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2211554062032289560439541 207333193315527146291207)
              ·
                refine ⟨310999789973290719436811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 207333193315527146291207 310999789973290719436811)
                ·
                  refine ⟨466499684959936079155217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 310999789973290719436811 466499684959936079155217)
                  ·
                    refine ⟨349874763719952059366413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 466499684959936079155217 349874763719952059366413)
                    ·
                      refine ⟨131203036394982022262405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 349874763719952059366413 131203036394982022262405)
                      ·
                        rfl

theorem cell23_255517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 5, 1, 1, 2, 3].length) (baseStart_255517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_255517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_255517 prefixEnd_255517 := by exact prefixLift 255517
  have htrace : WordTrace (prefixWord ++ tailWord_255517) baseStart_255517 baseEnd_255517 := by
    simpa [prefixWord, tailWord_255517, baseEnd_255517] using wordTrace_append hprefix tailTrace_255517
  have hstable : (prefixWord ++ tailWord_255517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_255517).length < 2 ^ (prefixWord ++ tailWord_255517).sum := by decide
  have hdescent : baseEnd_255517 < baseStart_255517 := by decide
  rcases family_descends (prefixWord ++ tailWord_255517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_255553 : List Nat := [1, 2, 5, 1, 1, 1, 1, 2, 2, 3, 4]
def baseStart_255553 : Nat := 118140960795 + 255553 * 2 ^ 59
def prefixEnd_255553 : Nat := 4983230072969 + 3 ^ 40 * 255553 * 2
def baseEnd_255553 : Nat := 131221521698543881412239

theorem tailTrace_255553 : CollatzResearch.WordTrace tailWord_255553 prefixEnd_255553 131221521698543881412239 := by
  unfold tailWord_255553
  simp only [CollatzResearch.WordTrace]
  refine ⟨9320783643182600822755313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6213855762121733881836875 9320783643182600822755313)
  ·
    refine ⟨6990587732386950617066485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9320783643182600822755313 6990587732386950617066485)
    ·
      refine ⟨655367599911276620349983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6990587732386950617066485 655367599911276620349983)
      ·
        refine ⟨983051399866914930524975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 655367599911276620349983 983051399866914930524975)
        ·
          refine ⟨1474577099800372395787463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 983051399866914930524975 1474577099800372395787463)
          ·
            refine ⟨2211865649700558593681195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1474577099800372395787463 2211865649700558593681195)
            ·
              refine ⟨3317798474550837890521793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2211865649700558593681195 3317798474550837890521793)
              ·
                refine ⟨2488348855913128417891345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3317798474550837890521793 2488348855913128417891345)
                ·
                  refine ⟨1866261641934846313418509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2488348855913128417891345 1866261641934846313418509)
                  ·
                    refine ⟨699848115725567367531941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1866261641934846313418509 699848115725567367531941)
                    ·
                      refine ⟨131221521698543881412239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 699848115725567367531941 131221521698543881412239)
                      ·
                        rfl

theorem cell23_255553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 2, 2, 3, 4].length) (baseStart_255553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_255553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_255553 prefixEnd_255553 := by exact prefixLift 255553
  have htrace : WordTrace (prefixWord ++ tailWord_255553) baseStart_255553 baseEnd_255553 := by
    simpa [prefixWord, tailWord_255553, baseEnd_255553] using wordTrace_append hprefix tailTrace_255553
  have hstable : (prefixWord ++ tailWord_255553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_255553).length < 2 ^ (prefixWord ++ tailWord_255553).sum := by decide
  have hdescent : baseEnd_255553 < baseStart_255553 := by decide
  rcases family_descends (prefixWord ++ tailWord_255553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_255576 : List Nat := [2, 1, 2, 2, 1, 2, 1, 1, 11]
def baseStart_255576 : Nat := 118140960795 + 255576 * 2 ^ 59
def prefixEnd_255576 : Nat := 4983230072969 + 3 ^ 40 * 255576 * 2
def baseEnd_255576 : Nat := 14581481305955254602737

theorem tailTrace_255576 : CollatzResearch.WordTrace tailWord_255576 prefixEnd_255576 14581481305955254602737 := by
  unfold tailWord_255576
  simp only [CollatzResearch.WordTrace]
  refine ⟨4660811261049637875421291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6214415014732850500561721 4660811261049637875421291)
  ·
    refine ⟨6991216891574456813131937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4660811261049637875421291 6991216891574456813131937)
    ·
      refine ⟨5243412668680842609848953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6991216891574456813131937 5243412668680842609848953)
      ·
        refine ⟨3932559501510631957386715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5243412668680842609848953 3932559501510631957386715)
        ·
          refine ⟨5898839252265947936080073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3932559501510631957386715 5898839252265947936080073)
          ·
            refine ⟨4424129439199460952060055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5898839252265947936080073 4424129439199460952060055)
            ·
              refine ⟨6636194158799191428090083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4424129439199460952060055 6636194158799191428090083)
              ·
                refine ⟨9954291238198787142135125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6636194158799191428090083 9954291238198787142135125)
                ·
                  refine ⟨14581481305955254602737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 9954291238198787142135125 14581481305955254602737)
                  ·
                    rfl

theorem cell23_255576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 1, 11].length) (baseStart_255576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_255576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_255576 prefixEnd_255576 := by exact prefixLift 255576
  have htrace : WordTrace (prefixWord ++ tailWord_255576) baseStart_255576 baseEnd_255576 := by
    simpa [prefixWord, tailWord_255576, baseEnd_255576] using wordTrace_append hprefix tailTrace_255576
  have hstable : (prefixWord ++ tailWord_255576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_255576).length < 2 ^ (prefixWord ++ tailWord_255576).sum := by decide
  have hdescent : baseEnd_255576 < baseStart_255576 := by decide
  rcases family_descends (prefixWord ++ tailWord_255576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_255587 : List Nat := [1, 1, 1, 5, 1, 4, 1, 1, 4, 2, 2]
def baseStart_255587 : Nat := 118140960795 + 255587 * 2 ^ 59
def prefixEnd_255587 : Nat := 4983230072969 + 3 ^ 40 * 255587 * 2
def baseEnd_255587 : Nat := 131238980040796748387083

theorem tailTrace_255587 : CollatzResearch.WordTrace tailWord_255587 prefixEnd_255587 131238980040796748387083 := by
  unfold tailWord_255587
  simp only [CollatzResearch.WordTrace]
  refine ⟨9322023725059424629493015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6214682483372949752995343 9322023725059424629493015)
  ·
    refine ⟨13983035587589136944239523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9322023725059424629493015 13983035587589136944239523)
    ·
      refine ⟨20974553381383705416359285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13983035587589136944239523 20974553381383705416359285)
      ·
        refine ⟨1966364379504722382783683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 20974553381383705416359285 1966364379504722382783683)
        ·
          refine ⟨2949546569257083574175525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1966364379504722382783683 2949546569257083574175525)
          ·
            refine ⟨553039981735703170157911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2949546569257083574175525 553039981735703170157911)
            ·
              refine ⟨829559972603554755236867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 553039981735703170157911 829559972603554755236867)
              ·
                refine ⟨1244339958905332132855301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 829559972603554755236867 1244339958905332132855301)
                ·
                  refine ⟨233313742294749774910369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1244339958905332132855301 233313742294749774910369)
                  ·
                    refine ⟨174985306721062331182777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 233313742294749774910369 174985306721062331182777)
                    ·
                      refine ⟨131238980040796748387083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 174985306721062331182777 131238980040796748387083)
                      ·
                        rfl

theorem cell23_255587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 1, 1, 4, 2, 2].length) (baseStart_255587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_255587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_255587 prefixEnd_255587 := by exact prefixLift 255587
  have htrace : WordTrace (prefixWord ++ tailWord_255587) baseStart_255587 baseEnd_255587 := by
    simpa [prefixWord, tailWord_255587, baseEnd_255587] using wordTrace_append hprefix tailTrace_255587
  have hstable : (prefixWord ++ tailWord_255587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_255587).length < 2 ^ (prefixWord ++ tailWord_255587).sum := by decide
  have hdescent : baseEnd_255587 < baseStart_255587 := by decide
  rcases family_descends (prefixWord ++ tailWord_255587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_255623 : List Nat := [1, 1, 4, 2, 1, 3, 2, 1, 1, 7]
def baseStart_255623 : Nat := 118140960795 + 255623 * 2 ^ 59
def prefixEnd_255623 : Nat := 4983230072969 + 3 ^ 40 * 255623 * 2
def baseEnd_255623 : Nat := 43752488448119535845639

theorem tailTrace_255623 : CollatzResearch.WordTrace tailWord_255623 prefixEnd_255623 43752488448119535845639 := by
  unfold tailWord_255623
  simp only [CollatzResearch.WordTrace]
  refine ⟨9323336752929002777803523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6215557835286001851869015 9323336752929002777803523)
  ·
    refine ⟨13985005129393504166705285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9323336752929002777803523 13985005129393504166705285)
    ·
      refine ⟨2622188461761282031257241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13985005129393504166705285 2622188461761282031257241)
      ·
        refine ⟨1966641346320961523442931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2622188461761282031257241 1966641346320961523442931)
        ·
          refine ⟨2949962019481442285164397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1966641346320961523442931 2949962019481442285164397)
          ·
            refine ⟨1106235757305540856936649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2949962019481442285164397 1106235757305540856936649)
            ·
              refine ⟨829676817979155642702487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1106235757305540856936649 829676817979155642702487)
              ·
                refine ⟨1244515226968733464053731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 829676817979155642702487 1244515226968733464053731)
                ·
                  refine ⟨1866772840453100196080597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1244515226968733464053731 1866772840453100196080597)
                  ·
                    refine ⟨43752488448119535845639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1866772840453100196080597 43752488448119535845639)
                    ·
                      rfl

theorem cell23_255623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 2, 1, 1, 7].length) (baseStart_255623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_255623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_255623 prefixEnd_255623 := by exact prefixLift 255623
  have htrace : WordTrace (prefixWord ++ tailWord_255623) baseStart_255623 baseEnd_255623 := by
    simpa [prefixWord, tailWord_255623, baseEnd_255623] using wordTrace_append hprefix tailTrace_255623
  have hstable : (prefixWord ++ tailWord_255623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_255623).length < 2 ^ (prefixWord ++ tailWord_255623).sum := by decide
  have hdescent : baseEnd_255623 < baseStart_255623 := by decide
  rcases family_descends (prefixWord ++ tailWord_255623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_255640 : List Nat := [2, 1, 2, 4, 1, 3, 1, 2, 2, 5]
def baseStart_255640 : Nat := 118140960795 + 255640 * 2 ^ 59
def prefixEnd_255640 : Nat := 4983230072969 + 3 ^ 40 * 255640 * 2
def baseEnd_255640 : Nat := 43755398171828347008113

theorem tailTrace_255640 : CollatzResearch.WordTrace tailWord_255640 prefixEnd_255640 43755398171828347008113 := by
  unfold tailWord_255640
  simp only [CollatzResearch.WordTrace]
  refine ⟨4661978396933707340586187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6215971195911609787448249 4661978396933707340586187)
  ·
    refine ⟨6992967595400561010879281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4661978396933707340586187 6992967595400561010879281)
    ·
      refine ⟨5244725696550420758159461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6992967595400561010879281 5244725696550420758159461)
      ·
        refine ⟨983386068103203892154899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5244725696550420758159461 983386068103203892154899)
        ·
          refine ⟨1475079102154805838232349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 983386068103203892154899 1475079102154805838232349)
          ·
            refine ⟨553154663308052189337131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1475079102154805838232349 553154663308052189337131)
            ·
              refine ⟨829731994962078284005697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 553154663308052189337131 829731994962078284005697)
              ·
                refine ⟨622298996221558713004273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 829731994962078284005697 622298996221558713004273)
                ·
                  refine ⟨466724247166169034753205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 622298996221558713004273 466724247166169034753205)
                  ·
                    refine ⟨43755398171828347008113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 466724247166169034753205 43755398171828347008113)
                    ·
                      rfl

theorem cell23_255640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 1, 2, 2, 5].length) (baseStart_255640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_255640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_255640 prefixEnd_255640 := by exact prefixLift 255640
  have htrace : WordTrace (prefixWord ++ tailWord_255640) baseStart_255640 baseEnd_255640 := by
    simpa [prefixWord, tailWord_255640, baseEnd_255640] using wordTrace_append hprefix tailTrace_255640
  have hstable : (prefixWord ++ tailWord_255640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_255640).length < 2 ^ (prefixWord ++ tailWord_255640).sum := by decide
  have hdescent : baseEnd_255640 < baseStart_255640 := by decide
  rcases family_descends (prefixWord ++ tailWord_255640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_255644 : List Nat := [2, 2, 3, 2, 3, 1, 3, 2, 5]
def baseStart_255644 : Nat := 118140960795 + 255644 * 2 ^ 59
def prefixEnd_255644 : Nat := 4983230072969 + 3 ^ 40 * 255644 * 2
def baseEnd_255644 : Nat := 14585360937567002819369

theorem tailTrace_255644 : CollatzResearch.WordTrace tailWord_255644 prefixEnd_255644 14585360937567002819369 := by
  unfold tailWord_255644
  simp only [CollatzResearch.WordTrace]
  refine ⟨4662051342926461682158993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6216068457235282242878657 4662051342926461682158993)
  ·
    refine ⟨3496538507194846261619245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4662051342926461682158993 3496538507194846261619245)
    ·
      refine ⟨1311201940198067348107217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3496538507194846261619245 1311201940198067348107217)
      ·
        refine ⟨983401455148550511080413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1311201940198067348107217 983401455148550511080413)
        ·
          refine ⟨368775545680706441655155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 983401455148550511080413 368775545680706441655155)
          ·
            refine ⟨553163318521059662482733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 368775545680706441655155 553163318521059662482733)
            ·
              refine ⟨207436244445397373431025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 553163318521059662482733 207436244445397373431025)
              ·
                refine ⟨155577183334048030073269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 207436244445397373431025 155577183334048030073269)
                ·
                  refine ⟨14585360937567002819369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 155577183334048030073269 14585360937567002819369)
                  ·
                    rfl

theorem cell23_255644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 3, 2, 5].length) (baseStart_255644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_255644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_255644 prefixEnd_255644 := by exact prefixLift 255644
  have htrace : WordTrace (prefixWord ++ tailWord_255644) baseStart_255644 baseEnd_255644 := by
    simpa [prefixWord, tailWord_255644, baseEnd_255644] using wordTrace_append hprefix tailTrace_255644
  have hstable : (prefixWord ++ tailWord_255644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_255644).length < 2 ^ (prefixWord ++ tailWord_255644).sum := by decide
  have hdescent : baseEnd_255644 < baseStart_255644 := by decide
  rcases family_descends (prefixWord ++ tailWord_255644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_255673 : List Nat := [1, 2, 1, 4, 1, 1, 2, 1, 2, 4, 4]
def baseStart_255673 : Nat := 118140960795 + 255673 * 2 ^ 59
def prefixEnd_255673 : Nat := 4983230072969 + 3 ^ 40 * 255673 * 2
def baseEnd_255673 : Nat := 131283139377083411911687

theorem tailTrace_255673 : CollatzResearch.WordTrace tailWord_255673 prefixEnd_255673 131283139377083411911687 := by
  unfold tailWord_255673
  simp only [CollatzResearch.WordTrace]
  refine ⟨9325160402747861317123673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6216773601831907544749115 9325160402747861317123673)
  ·
    refine ⟨6993870302060895987842755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9325160402747861317123673 6993870302060895987842755)
    ·
      refine ⟨10490805453091343981764133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6993870302060895987842755 10490805453091343981764133)
      ·
        refine ⟨1967026022454626996580775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10490805453091343981764133 1967026022454626996580775)
        ·
          refine ⟨2950539033681940494871163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1967026022454626996580775 2950539033681940494871163)
          ·
            refine ⟨4425808550522910742306745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2950539033681940494871163 4425808550522910742306745)
            ·
              refine ⟨3319356412892183056730059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4425808550522910742306745 3319356412892183056730059)
              ·
                refine ⟨4979034619338274585095089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3319356412892183056730059 4979034619338274585095089)
                ·
                  refine ⟨3734275964503705938821317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4979034619338274585095089 3734275964503705938821317)
                  ·
                    refine ⟨700176743344444863528997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3734275964503705938821317 700176743344444863528997)
                    ·
                      refine ⟨131283139377083411911687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 700176743344444863528997 131283139377083411911687)
                      ·
                        rfl

theorem cell23_255673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 1, 2, 4, 4].length) (baseStart_255673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_255673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_255673 prefixEnd_255673 := by exact prefixLift 255673
  have htrace : WordTrace (prefixWord ++ tailWord_255673) baseStart_255673 baseEnd_255673 := by
    simpa [prefixWord, tailWord_255673, baseEnd_255673] using wordTrace_append hprefix tailTrace_255673
  have hstable : (prefixWord ++ tailWord_255673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_255673).length < 2 ^ (prefixWord ++ tailWord_255673).sum := by decide
  have hdescent : baseEnd_255673 < baseStart_255673 := by decide
  rcases family_descends (prefixWord ++ tailWord_255673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_255687 : List Nat := [1, 1, 4, 1, 1, 1, 4, 5, 1, 4]
def baseStart_255687 : Nat := 118140960795 + 255687 * 2 ^ 59
def prefixEnd_255687 : Nat := 4983230072969 + 3 ^ 40 * 255687 * 2
def baseEnd_255687 : Nat := 43763442702082119045541

theorem tailTrace_255687 : CollatzResearch.WordTrace tailWord_255687 prefixEnd_255687 43763442702082119045541 := by
  unfold tailWord_255687
  simp only [CollatzResearch.WordTrace]
  refine ⟨9325671024697141708133315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6217114016464761138755543 9325671024697141708133315)
  ·
    refine ⟨13988506537045712562199973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9325671024697141708133315 13988506537045712562199973)
    ·
      refine ⟨2622844975696071105412495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13988506537045712562199973 2622844975696071105412495)
      ·
        refine ⟨3934267463544106658118743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2622844975696071105412495 3934267463544106658118743)
        ·
          refine ⟨5901401195316159987178115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3934267463544106658118743 5901401195316159987178115)
          ·
            refine ⟨8852101792974239980767173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5901401195316159987178115 8852101792974239980767173)
            ·
              refine ⟨1659769086182669996393845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8852101792974239980767173 1659769086182669996393845)
              ·
                refine ⟨155603351829625312161923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1659769086182669996393845 155603351829625312161923)
                ·
                  refine ⟨233405027744437968242885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 155603351829625312161923 233405027744437968242885)
                  ·
                    refine ⟨43763442702082119045541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 233405027744437968242885 43763442702082119045541)
                    ·
                      rfl

theorem cell23_255687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 5, 1, 4].length) (baseStart_255687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_255687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_255687 prefixEnd_255687 := by exact prefixLift 255687
  have htrace : WordTrace (prefixWord ++ tailWord_255687) baseStart_255687 baseEnd_255687 := by
    simpa [prefixWord, tailWord_255687, baseEnd_255687] using wordTrace_append hprefix tailTrace_255687
  have hstable : (prefixWord ++ tailWord_255687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_255687).length < 2 ^ (prefixWord ++ tailWord_255687).sum := by decide
  have hdescent : baseEnd_255687 < baseStart_255687 := by decide
  rcases family_descends (prefixWord ++ tailWord_255687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_255703 : List Nat := [1, 1, 3, 2, 1, 3, 2, 1, 1, 2, 6]
def baseStart_255703 : Nat := 118140960795 + 255703 * 2 ^ 59
def prefixEnd_255703 : Nat := 4983230072969 + 3 ^ 40 * 255703 * 2
def baseEnd_255703 : Nat := 131298543796718294536549

theorem tailTrace_255703 : CollatzResearch.WordTrace tailWord_255703 prefixEnd_255703 131298543796718294536549 := by
  unfold tailWord_255703
  simp only [CollatzResearch.WordTrace]
  refine ⟨9326254592639176440715763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6217503061759450960477175 9326254592639176440715763)
  ·
    refine ⟨13989381888958764661073645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9326254592639176440715763 13989381888958764661073645)
    ·
      refine ⟨5246018208359536747902617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13989381888958764661073645 5246018208359536747902617)
      ·
        refine ⟨3934513656269652560926963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5246018208359536747902617 3934513656269652560926963)
        ·
          refine ⟨5901770484404478841390445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3934513656269652560926963 5901770484404478841390445)
          ·
            refine ⟨2213163931651679565521417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5901770484404478841390445 2213163931651679565521417)
            ·
              refine ⟨1659872948738759674141063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2213163931651679565521417 1659872948738759674141063)
              ·
                refine ⟨2489809423108139511211595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1659872948738759674141063 2489809423108139511211595)
                ·
                  refine ⟨3734714134662209266817393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2489809423108139511211595 3734714134662209266817393)
                  ·
                    refine ⟨2801035600996656950113045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3734714134662209266817393 2801035600996656950113045)
                    ·
                      refine ⟨131298543796718294536549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 2801035600996656950113045 131298543796718294536549)
                      ·
                        rfl

theorem cell23_255703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 1, 1, 2, 6].length) (baseStart_255703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_255703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_255703 prefixEnd_255703 := by exact prefixLift 255703
  have htrace : WordTrace (prefixWord ++ tailWord_255703) baseStart_255703 baseEnd_255703 := by
    simpa [prefixWord, tailWord_255703, baseEnd_255703] using wordTrace_append hprefix tailTrace_255703
  have hstable : (prefixWord ++ tailWord_255703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_255703).length < 2 ^ (prefixWord ++ tailWord_255703).sum := by decide
  have hdescent : baseEnd_255703 < baseStart_255703 := by decide
  rcases family_descends (prefixWord ++ tailWord_255703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_255727 : List Nat := [1, 1, 2, 1, 5, 1, 3, 2, 3, 1, 3]
def baseStart_255727 : Nat := 118140960795 + 255727 * 2 ^ 59
def prefixEnd_255727 : Nat := 4983230072969 + 3 ^ 40 * 255727 * 2
def baseEnd_255727 : Nat := 131310867332426200636439

theorem tailTrace_255727 : CollatzResearch.WordTrace tailWord_255727 prefixEnd_255727 131310867332426200636439 := by
  unfold tailWord_255727
  simp only [CollatzResearch.WordTrace]
  refine ⟨9327129944552228539589435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6218086629701485693059623 9327129944552228539589435)
  ·
    refine ⟨13990694916828342809384153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9327129944552228539589435 13990694916828342809384153)
    ·
      refine ⟨10493021187621257107038115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13990694916828342809384153 10493021187621257107038115)
      ·
        refine ⟨15739531781431885660557173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10493021187621257107038115 15739531781431885660557173)
        ·
          refine ⟨1475581104509239280677235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15739531781431885660557173 1475581104509239280677235)
          ·
            refine ⟨2213371656763858921015853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1475581104509239280677235 2213371656763858921015853)
            ·
              refine ⟨830014371286447095380945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2213371656763858921015853 830014371286447095380945)
              ·
                refine ⟨622510778464835321535709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 830014371286447095380945 622510778464835321535709)
                ·
                  refine ⟨233441541924313245575891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 622510778464835321535709 233441541924313245575891)
                  ·
                    refine ⟨350162312886469868363837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 233441541924313245575891 350162312886469868363837)
                    ·
                      refine ⟨131310867332426200636439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 350162312886469868363837 131310867332426200636439)
                      ·
                        rfl

theorem cell23_255727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 3, 2, 3, 1, 3].length) (baseStart_255727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_255727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_255727 prefixEnd_255727 := by exact prefixLift 255727
  have htrace : WordTrace (prefixWord ++ tailWord_255727) baseStart_255727 baseEnd_255727 := by
    simpa [prefixWord, tailWord_255727, baseEnd_255727] using wordTrace_append hprefix tailTrace_255727
  have hstable : (prefixWord ++ tailWord_255727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_255727).length < 2 ^ (prefixWord ++ tailWord_255727).sum := by decide
  have hdescent : baseEnd_255727 < baseStart_255727 := by decide
  rcases family_descends (prefixWord ++ tailWord_255727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_255730 : List Nat := [3, 2, 1, 3, 1, 1, 1, 3, 3, 5]
def baseStart_255730 : Nat := 118140960795 + 255730 * 2 ^ 59
def prefixEnd_255730 : Nat := 4983230072969 + 3 ^ 40 * 255730 * 2
def baseEnd_255730 : Nat := 43770802591463229632975

theorem tailTrace_255730 : CollatzResearch.WordTrace tailWord_255730 prefixEnd_255730 43770802591463229632975 := by
  unfold tailWord_255730
  simp only [CollatzResearch.WordTrace]
  refine ⟨2331809840885340012987161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6218159575694240034632429 2331809840885340012987161)
  ·
    refine ⟨1748857380664005009740371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2331809840885340012987161 1748857380664005009740371)
    ·
      refine ⟨2623286070996007514610557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1748857380664005009740371 2623286070996007514610557)
      ·
        refine ⟨983732276623502817978959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2623286070996007514610557 983732276623502817978959)
        ·
          refine ⟨1475598414935254226968439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 983732276623502817978959 1475598414935254226968439)
          ·
            refine ⟨2213397622402881340452659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1475598414935254226968439 2213397622402881340452659)
            ·
              refine ⟨3320096433604322010678989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2213397622402881340452659 3320096433604322010678989)
              ·
                refine ⟨1245036162601620754004621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3320096433604322010678989 1245036162601620754004621)
                ·
                  refine ⟨466888560975607782751733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1245036162601620754004621 466888560975607782751733)
                  ·
                    refine ⟨43770802591463229632975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 466888560975607782751733 43770802591463229632975)
                    ·
                      rfl

theorem cell23_255730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 3, 3, 5].length) (baseStart_255730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_255730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_255730 prefixEnd_255730 := by exact prefixLift 255730
  have htrace : WordTrace (prefixWord ++ tailWord_255730) baseStart_255730 baseEnd_255730 := by
    simpa [prefixWord, tailWord_255730, baseEnd_255730] using wordTrace_append hprefix tailTrace_255730
  have hstable : (prefixWord ++ tailWord_255730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_255730).length < 2 ^ (prefixWord ++ tailWord_255730).sum := by decide
  have hdescent : baseEnd_255730 < baseStart_255730 := by decide
  rcases family_descends (prefixWord ++ tailWord_255730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_255747 : List Nat := [1, 1, 1, 3, 2, 2, 6, 1, 1, 5]
def baseStart_255747 : Nat := 118140960795 + 255747 * 2 ^ 59
def prefixEnd_255747 : Nat := 4983230072969 + 3 ^ 40 * 255747 * 2
def baseEnd_255747 : Nat := 43773712315172040795449

theorem tailTrace_255747 : CollatzResearch.WordTrace tailWord_255747 prefixEnd_255747 43773712315172040795449 := by
  unfold tailWord_255747
  simp only [CollatzResearch.WordTrace]
  refine ⟨9327859404479771955317495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6218572936319847970211663 9327859404479771955317495)
  ·
    refine ⟨13991789106719657932976243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9327859404479771955317495 13991789106719657932976243)
    ·
      refine ⟨20987683660079486899464365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13991789106719657932976243 20987683660079486899464365)
      ·
        refine ⟨7870381372529807587299137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20987683660079486899464365 7870381372529807587299137)
        ·
          refine ⟨5902786029397355690474353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7870381372529807587299137 5902786029397355690474353)
          ·
            refine ⟨4427089522048016767855765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5902786029397355690474353 4427089522048016767855765)
            ·
              refine ⟨207519821346000785993239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 4427089522048016767855765 207519821346000785993239)
              ·
                refine ⟨311279732019001178989859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 207519821346000785993239 311279732019001178989859)
                ·
                  refine ⟨466919598028501768484789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 311279732019001178989859 466919598028501768484789)
                  ·
                    refine ⟨43773712315172040795449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 466919598028501768484789 43773712315172040795449)
                    ·
                      rfl

theorem cell23_255747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 6, 1, 1, 5].length) (baseStart_255747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_255747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_255747 prefixEnd_255747 := by exact prefixLift 255747
  have htrace : WordTrace (prefixWord ++ tailWord_255747) baseStart_255747 baseEnd_255747 := by
    simpa [prefixWord, tailWord_255747, baseEnd_255747] using wordTrace_append hprefix tailTrace_255747
  have hstable : (prefixWord ++ tailWord_255747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_255747).length < 2 ^ (prefixWord ++ tailWord_255747).sum := by decide
  have hdescent : baseEnd_255747 < baseStart_255747 := by decide
  rcases family_descends (prefixWord ++ tailWord_255747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_255770 : List Nat := [3, 1, 1, 3, 2, 2, 1, 1, 3, 1, 5]
def baseStart_255770 : Nat := 118140960795 + 255770 * 2 ^ 59
def prefixEnd_255770 : Nat := 4983230072969 + 3 ^ 40 * 255770 * 2
def baseEnd_255770 : Nat := 131332947000569532398741

theorem tailTrace_255770 : CollatzResearch.WordTrace tailWord_255770 prefixEnd_255770 131332947000569532398741 := by
  unfold tailWord_255770
  simp only [CollatzResearch.WordTrace]
  refine ⟨2332174570849111720851191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6219132188930964588936509 2332174570849111720851191)
  ·
    refine ⟨3498261856273667581276787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2332174570849111720851191 3498261856273667581276787)
    ·
      refine ⟨5247392784410501371915181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3498261856273667581276787 5247392784410501371915181)
      ·
        refine ⟨1967772294153938014468193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5247392784410501371915181 1967772294153938014468193)
        ·
          refine ⟨1475829220615453510851145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1967772294153938014468193 1475829220615453510851145)
          ·
            refine ⟨1106871915461590133138359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1475829220615453510851145 1106871915461590133138359)
            ·
              refine ⟨1660307873192385199707539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1106871915461590133138359 1660307873192385199707539)
              ·
                refine ⟨2490461809788577799561309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1660307873192385199707539 2490461809788577799561309)
                ·
                  refine ⟨933923178670716674835491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2490461809788577799561309 933923178670716674835491)
                  ·
                    refine ⟨1400884768006075012253237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 933923178670716674835491 1400884768006075012253237)
                    ·
                      refine ⟨131332947000569532398741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1400884768006075012253237 131332947000569532398741)
                      ·
                        rfl

theorem cell23_255770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 1, 3, 1, 5].length) (baseStart_255770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_255770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_255770 prefixEnd_255770 := by exact prefixLift 255770
  have htrace : WordTrace (prefixWord ++ tailWord_255770) baseStart_255770 baseEnd_255770 := by
    simpa [prefixWord, tailWord_255770, baseEnd_255770] using wordTrace_append hprefix tailTrace_255770
  have hstable : (prefixWord ++ tailWord_255770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_255770).length < 2 ^ (prefixWord ++ tailWord_255770).sum := by decide
  have hdescent : baseEnd_255770 < baseStart_255770 := by decide
  rcases family_descends (prefixWord ++ tailWord_255770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_255777 : List Nat := [1, 2, 3, 2, 1, 5, 1, 1, 1, 6]
def baseStart_255777 : Nat := 118140960795 + 255777 * 2 ^ 59
def prefixEnd_255777 : Nat := 4983230072969 + 3 ^ 40 * 255777 * 2
def baseEnd_255777 : Nat := 43778847121717001670403

theorem tailTrace_255777 : CollatzResearch.WordTrace tailWord_255777 prefixEnd_255777 43778847121717001670403 := by
  unfold tailWord_255777
  simp only [CollatzResearch.WordTrace]
  refine ⟨9328953594371087078909585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6219302396247391385939723 9328953594371087078909585)
  ·
    refine ⟨6996715195778315309182189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9328953594371087078909585 6996715195778315309182189)
    ·
      refine ⟨2623768198416868240943321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6996715195778315309182189 2623768198416868240943321)
      ·
        refine ⟨1967826148812651180707491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2623768198416868240943321 1967826148812651180707491)
        ·
          refine ⟨2951739223218976771061237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1967826148812651180707491 2951739223218976771061237)
          ·
            refine ⟨276725552176779072286991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2951739223218976771061237 276725552176779072286991)
            ·
              refine ⟨415088328265168608430487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 276725552176779072286991 415088328265168608430487)
              ·
                refine ⟨622632492397752912645731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 415088328265168608430487 622632492397752912645731)
                ·
                  refine ⟨933948738596629368968597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 622632492397752912645731 933948738596629368968597)
                  ·
                    refine ⟨43778847121717001670403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 933948738596629368968597 43778847121717001670403)
                    ·
                      rfl

theorem cell23_255777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 5, 1, 1, 1, 6].length) (baseStart_255777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_255777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_255777 prefixEnd_255777 := by exact prefixLift 255777
  have htrace : WordTrace (prefixWord ++ tailWord_255777) baseStart_255777 baseEnd_255777 := by
    simpa [prefixWord, tailWord_255777, baseEnd_255777] using wordTrace_append hprefix tailTrace_255777
  have hstable : (prefixWord ++ tailWord_255777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_255777).length < 2 ^ (prefixWord ++ tailWord_255777).sum := by decide
  have hdescent : baseEnd_255777 < baseStart_255777 := by decide
  rcases family_descends (prefixWord ++ tailWord_255777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_255784 : List Nat := [2, 1, 5, 1, 1, 3, 2, 2, 1, 1, 4]
def baseStart_255784 : Nat := 118140960795 + 255784 * 2 ^ 59
def prefixEnd_255784 : Nat := 4983230072969 + 3 ^ 40 * 255784 * 2
def baseEnd_255784 : Nat := 131340135729732477623677

theorem tailTrace_255784 : CollatzResearch.WordTrace tailWord_255784 prefixEnd_255784 131340135729732477623677 := by
  unfold tailWord_255784
  simp only [CollatzResearch.WordTrace]
  refine ⟨4664604452672863637207203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6219472603563818182942937 4664604452672863637207203)
  ·
    refine ⟨6996906679009295455810805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4664604452672863637207203 6996906679009295455810805)
    ·
      refine ⟨655960001157121448982263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6996906679009295455810805 655960001157121448982263)
      ·
        refine ⟨983940001735682173473395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 655960001157121448982263 983940001735682173473395)
        ·
          refine ⟨1475910002603523260210093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 983940001735682173473395 1475910002603523260210093)
          ·
            refine ⟨553466250976321222578785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1475910002603523260210093 553466250976321222578785)
            ·
              refine ⟨415099688232240916934089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 553466250976321222578785 415099688232240916934089)
              ·
                refine ⟨311324766174180687700567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 415099688232240916934089 311324766174180687700567)
                ·
                  refine ⟨466987149261271031550851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 311324766174180687700567 466987149261271031550851)
                  ·
                    refine ⟨700480723891906547326277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 466987149261271031550851 700480723891906547326277)
                    ·
                      refine ⟨131340135729732477623677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 700480723891906547326277 131340135729732477623677)
                      ·
                        rfl

theorem cell23_255784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 2, 2, 1, 1, 4].length) (baseStart_255784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_255784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_255784 prefixEnd_255784 := by exact prefixLift 255784
  have htrace : WordTrace (prefixWord ++ tailWord_255784) baseStart_255784 baseEnd_255784 := by
    simpa [prefixWord, tailWord_255784, baseEnd_255784] using wordTrace_append hprefix tailTrace_255784
  have hstable : (prefixWord ++ tailWord_255784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_255784).length < 2 ^ (prefixWord ++ tailWord_255784).sum := by decide
  have hdescent : baseEnd_255784 < baseStart_255784 := by decide
  rcases family_descends (prefixWord ++ tailWord_255784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_255807 : List Nat := [1, 1, 2, 2, 7, 1, 9]
def baseStart_255807 : Nat := 118140960795 + 255807 * 2 ^ 59
def prefixEnd_255807 : Nat := 4983230072969 + 3 ^ 40 * 255807 * 2
def baseEnd_255807 : Nat := 1621628960305998612791

theorem tailTrace_255807 : CollatzResearch.WordTrace tailWord_255807 prefixEnd_255807 1621628960305998612791 := by
  unfold tailWord_255807
  simp only [CollatzResearch.WordTrace]
  refine ⟨9330047784262402202501675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6220031856174934801667783 9330047784262402202501675)
  ·
    refine ⟨13995071676393603303752513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9330047784262402202501675 13995071676393603303752513)
    ·
      refine ⟨10496303757295202477814385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13995071676393603303752513 10496303757295202477814385)
      ·
        refine ⟨7872227817971401858360789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10496303757295202477814385 7872227817971401858360789)
        ·
          refine ⟨184505339483704731055331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 7872227817971401858360789 184505339483704731055331)
          ·
            refine ⟨276758009225557096582997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184505339483704731055331 276758009225557096582997)
            ·
              refine ⟨1621628960305998612791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 276758009225557096582997 1621628960305998612791)
              ·
                rfl

theorem cell23_255807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 1, 9].length) (baseStart_255807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_255807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_255807 prefixEnd_255807 := by exact prefixLift 255807
  have htrace : WordTrace (prefixWord ++ tailWord_255807) baseStart_255807 baseEnd_255807 := by
    simpa [prefixWord, tailWord_255807, baseEnd_255807] using wordTrace_append hprefix tailTrace_255807
  have hstable : (prefixWord ++ tailWord_255807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_255807).length < 2 ^ (prefixWord ++ tailWord_255807).sum := by decide
  have hdescent : baseEnd_255807 < baseStart_255807 := by decide
  rcases family_descends (prefixWord ++ tailWord_255807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_255814 : List Nat := [6, 1, 1, 2, 1, 1, 1, 2, 1, 1, 6]
def baseStart_255814 : Nat := 118140960795 + 255814 * 2 ^ 59
def prefixEnd_255814 : Nat := 4983230072969 + 3 ^ 40 * 255814 * 2
def baseEnd_255814 : Nat := 131355540149367360248539

theorem tailTrace_255814 : CollatzResearch.WordTrace tailWord_255814 prefixEnd_255814 131355540149367360248539 := by
  unfold tailWord_255814
  simp only [CollatzResearch.WordTrace]
  refine ⟨291571971726157574937703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 6220202063491361598670997 291571971726157574937703)
  ·
    refine ⟨437357957589236362406555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291571971726157574937703 437357957589236362406555)
    ·
      refine ⟨656036936383854543609833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 437357957589236362406555 656036936383854543609833)
      ·
        refine ⟨492027702287890907707375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 656036936383854543609833 492027702287890907707375)
        ·
          refine ⟨738041553431836361561063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 492027702287890907707375 738041553431836361561063)
          ·
            refine ⟨1107062330147754542341595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 738041553431836361561063 1107062330147754542341595)
            ·
              refine ⟨1660593495221631813512393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1107062330147754542341595 1660593495221631813512393)
              ·
                refine ⟨1245445121416223860134295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1660593495221631813512393 1245445121416223860134295)
                ·
                  refine ⟨1868167682124335790201443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1245445121416223860134295 1868167682124335790201443)
                  ·
                    refine ⟨2802251523186503685302165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1868167682124335790201443 2802251523186503685302165)
                    ·
                      refine ⟨131355540149367360248539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 2802251523186503685302165 131355540149367360248539)
                      ·
                        rfl

theorem cell23_255814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 2, 1, 1, 6].length) (baseStart_255814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_255814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_255814 prefixEnd_255814 := by exact prefixLift 255814
  have htrace : WordTrace (prefixWord ++ tailWord_255814) baseStart_255814 baseEnd_255814 := by
    simpa [prefixWord, tailWord_255814, baseEnd_255814] using wordTrace_append hprefix tailTrace_255814
  have hstable : (prefixWord ++ tailWord_255814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_255814).length < 2 ^ (prefixWord ++ tailWord_255814).sum := by decide
  have hdescent : baseEnd_255814 < baseStart_255814 := by decide
  rcases family_descends (prefixWord ++ tailWord_255814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_255817 : List Nat := [1, 2, 1, 1, 2, 4, 1, 3, 4, 1, 3]
def baseStart_255817 : Nat := 118140960795 + 255817 * 2 ^ 59
def prefixEnd_255817 : Nat := 4983230072969 + 3 ^ 40 * 255817 * 2
def baseEnd_255817 : Nat := 131357080591330848511025

theorem tailTrace_255817 : CollatzResearch.WordTrace tailWord_255817 prefixEnd_255817 131357080591330848511025 := by
  unfold tailWord_255817
  simp only [CollatzResearch.WordTrace]
  refine ⟨9330412514226173910365705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6220275009484115940243803 9330412514226173910365705)
  ·
    refine ⟨6997809385669630432774279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9330412514226173910365705 6997809385669630432774279)
    ·
      refine ⟨10496714078504445649161419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6997809385669630432774279 10496714078504445649161419)
      ·
        refine ⟨15745071117756668473742129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10496714078504445649161419 15745071117756668473742129)
        ·
          refine ⟨11808803338317501355306597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15745071117756668473742129 11808803338317501355306597)
          ·
            refine ⟨2214150625934531504119987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11808803338317501355306597 2214150625934531504119987)
            ·
              refine ⟨3321225938901797256179981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2214150625934531504119987 3321225938901797256179981)
              ·
                refine ⟨1245459727088173971067493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3321225938901797256179981 1245459727088173971067493)
                ·
                  refine ⟨233523698829032619575155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1245459727088173971067493 233523698829032619575155)
                  ·
                    refine ⟨350285548243548929362733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 233523698829032619575155 350285548243548929362733)
                    ·
                      refine ⟨131357080591330848511025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 350285548243548929362733 131357080591330848511025)
                      ·
                        rfl

theorem cell23_255817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 3, 4, 1, 3].length) (baseStart_255817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_255817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_255817 prefixEnd_255817 := by exact prefixLift 255817
  have htrace : WordTrace (prefixWord ++ tailWord_255817) baseStart_255817 baseEnd_255817 := by
    simpa [prefixWord, tailWord_255817, baseEnd_255817] using wordTrace_append hprefix tailTrace_255817
  have hstable : (prefixWord ++ tailWord_255817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_255817).length < 2 ^ (prefixWord ++ tailWord_255817).sum := by decide
  have hdescent : baseEnd_255817 < baseStart_255817 := by decide
  rcases family_descends (prefixWord ++ tailWord_255817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_255818 : List Nat := [3, 1, 2, 1, 1, 1, 7, 2, 1, 2, 2]
def baseStart_255818 : Nat := 118140960795 + 255818 * 2 ^ 59
def prefixEnd_255818 : Nat := 4983230072969 + 3 ^ 40 * 255818 * 2
def baseEnd_255818 : Nat := 131357594071985344598521

theorem tailTrace_255818 : CollatzResearch.WordTrace tailWord_255818 prefixEnd_255818 131357594071985344598521 := by
  unfold tailWord_255818
  simp only [CollatzResearch.WordTrace]
  refine ⟨2332612246805637770288027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6220299324815034054101405 2332612246805637770288027)
  ·
    refine ⟨3498918370208456655432041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2332612246805637770288027 3498918370208456655432041)
    ·
      refine ⟨2624188777656342491574031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3498918370208456655432041 2624188777656342491574031)
      ·
        refine ⟨3936283166484513737361047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2624188777656342491574031 3936283166484513737361047)
        ·
          refine ⟨5904424749726770606041571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3936283166484513737361047 5904424749726770606041571)
          ·
            refine ⟨8856637124590155909062357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5904424749726770606041571 8856637124590155909062357)
            ·
              refine ⟨207577432607581779118649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 8856637124590155909062357 207577432607581779118649)
              ·
                refine ⟨155683074455686334338987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 207577432607581779118649 155683074455686334338987)
                ·
                  refine ⟨233524611683529501508481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 155683074455686334338987 233524611683529501508481)
                  ·
                    refine ⟨175143458762647126131361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 233524611683529501508481 175143458762647126131361)
                    ·
                      refine ⟨131357594071985344598521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 175143458762647126131361 131357594071985344598521)
                      ·
                        rfl

theorem cell23_255818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 7, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 7, 2, 1, 2, 2].length) (baseStart_255818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_255818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_255818 prefixEnd_255818 := by exact prefixLift 255818
  have htrace : WordTrace (prefixWord ++ tailWord_255818) baseStart_255818 baseEnd_255818 := by
    simpa [prefixWord, tailWord_255818, baseEnd_255818] using wordTrace_append hprefix tailTrace_255818
  have hstable : (prefixWord ++ tailWord_255818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_255818).length < 2 ^ (prefixWord ++ tailWord_255818).sum := by decide
  have hdescent : baseEnd_255818 < baseStart_255818 := by decide
  rcases family_descends (prefixWord ++ tailWord_255818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_255834 : List Nat := [3, 1, 1, 2, 1, 3, 3, 3, 2, 1, 3]
def baseStart_255834 : Nat := 118140960795 + 255834 * 2 ^ 59
def prefixEnd_255834 : Nat := 4983230072969 + 3 ^ 40 * 255834 * 2
def baseEnd_255834 : Nat := 131365809762457281998447

theorem tailTrace_255834 : CollatzResearch.WordTrace tailWord_255834 prefixEnd_255834 131365809762457281998447 := by
  unfold tailWord_255834
  simp only [CollatzResearch.WordTrace]
  refine ⟨2332758138791146453433639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6220688370109723875823037 2332758138791146453433639)
  ·
    refine ⟨3499137208186719680150459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2332758138791146453433639 3499137208186719680150459)
    ·
      refine ⟨5248705812280079520225689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3499137208186719680150459 5248705812280079520225689)
      ·
        refine ⟨3936529359210059640169267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5248705812280079520225689 3936529359210059640169267)
        ·
          refine ⟨5904794038815089460253901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3936529359210059640169267 5904794038815089460253901)
          ·
            refine ⟨2214297764555658547595213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5904794038815089460253901 2214297764555658547595213)
            ·
              refine ⟨830361661708371955348205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2214297764555658547595213 830361661708371955348205)
              ·
                refine ⟨311385623140639483255577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 830361661708371955348205 311385623140639483255577)
                ·
                  refine ⟨233539217355479612441683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 311385623140639483255577 233539217355479612441683)
                  ·
                    refine ⟨350308826033219418662525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 233539217355479612441683 350308826033219418662525)
                    ·
                      refine ⟨131365809762457281998447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 350308826033219418662525 131365809762457281998447)
                      ·
                        rfl

theorem cell23_255834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 3, 3, 2, 1, 3].length) (baseStart_255834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_255834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_255834 prefixEnd_255834 := by exact prefixLift 255834
  have htrace : WordTrace (prefixWord ++ tailWord_255834) baseStart_255834 baseEnd_255834 := by
    simpa [prefixWord, tailWord_255834, baseEnd_255834] using wordTrace_append hprefix tailTrace_255834
  have hstable : (prefixWord ++ tailWord_255834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_255834).length < 2 ^ (prefixWord ++ tailWord_255834).sum := by decide
  have hdescent : baseEnd_255834 < baseStart_255834 := by decide
  rcases family_descends (prefixWord ++ tailWord_255834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_255912 : List Nat := [2, 1, 6, 2, 1, 2, 2, 1, 1, 3, 2]
def baseStart_255912 : Nat := 118140960795 + 255912 * 2 ^ 59
def prefixEnd_255912 : Nat := 4983230072969 + 3 ^ 40 * 255912 * 2
def baseEnd_255912 : Nat := 131405861253507976823089

theorem tailTrace_255912 : CollatzResearch.WordTrace tailWord_255912 prefixEnd_255912 131405861253507976823089 := by
  unfold tailWord_255912
  simp only [CollatzResearch.WordTrace]
  refine ⟨4666938724441002567536995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6222584965921336756715993 4666938724441002567536995)
  ·
    refine ⟨7000408086661503851305493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4666938724441002567536995 7000408086661503851305493)
    ·
      refine ⟨328144129062257993029945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 7000408086661503851305493 328144129062257993029945)
      ·
        refine ⟨246108096796693494772459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 328144129062257993029945 246108096796693494772459)
        ·
          refine ⟨369162145195040242158689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246108096796693494772459 369162145195040242158689)
          ·
            refine ⟨276871608896280181619017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 369162145195040242158689 276871608896280181619017)
            ·
              refine ⟨207653706672210136214263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 276871608896280181619017 207653706672210136214263)
              ·
                refine ⟨311480560008315204321395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 207653706672210136214263 311480560008315204321395)
                ·
                  refine ⟨467220840012472806482093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 311480560008315204321395 467220840012472806482093)
                  ·
                    refine ⟨175207815004677302430785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 467220840012472806482093 175207815004677302430785)
                    ·
                      refine ⟨131405861253507976823089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 175207815004677302430785 131405861253507976823089)
                      ·
                        rfl

theorem cell23_255912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 2, 2, 1, 1, 3, 2].length) (baseStart_255912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_255912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_255912 prefixEnd_255912 := by exact prefixLift 255912
  have htrace : WordTrace (prefixWord ++ tailWord_255912) baseStart_255912 baseEnd_255912 := by
    simpa [prefixWord, tailWord_255912, baseEnd_255912] using wordTrace_append hprefix tailTrace_255912
  have hstable : (prefixWord ++ tailWord_255912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_255912).length < 2 ^ (prefixWord ++ tailWord_255912).sum := by decide
  have hdescent : baseEnd_255912 < baseStart_255912 := by decide
  rcases family_descends (prefixWord ++ tailWord_255912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_256048 : List Nat := [2, 1, 1, 1, 2, 6, 1, 4, 1, 1, 3]
def baseStart_256048 : Nat := 118140960795 + 256048 * 2 ^ 59
def prefixEnd_256048 : Nat := 4983230072969 + 3 ^ 40 * 256048 * 2
def baseEnd_256048 : Nat := 131475694622519444722463

theorem tailTrace_256048 : CollatzResearch.WordTrace tailWord_256048 prefixEnd_256048 131475694622519444722463 := by
  unfold tailWord_256048
  simp only [CollatzResearch.WordTrace]
  refine ⟨4669418888194650181012399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6225891850926200241349865 4669418888194650181012399)
  ·
    refine ⟨7004128332291975271518599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4669418888194650181012399 7004128332291975271518599)
    ·
      refine ⟨10506192498437962907277899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7004128332291975271518599 10506192498437962907277899)
      ·
        refine ⟨15759288747656944360916849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10506192498437962907277899 15759288747656944360916849)
        ·
          refine ⟨11819466560742708270687637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15759288747656944360916849 11819466560742708270687637)
          ·
            refine ⟨554037495034814450188483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 11819466560742708270687637 554037495034814450188483)
            ·
              refine ⟨831056242552221675282725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 554037495034814450188483 831056242552221675282725)
              ·
                refine ⟨155823045478541564115511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 831056242552221675282725 155823045478541564115511)
                ·
                  refine ⟨233734568217812346173267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 155823045478541564115511 233734568217812346173267)
                  ·
                    refine ⟨350601852326718519259901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 233734568217812346173267 350601852326718519259901)
                    ·
                      refine ⟨131475694622519444722463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 350601852326718519259901 131475694622519444722463)
                      ·
                        rfl

theorem cell23_256048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 1, 4, 1, 1, 3].length) (baseStart_256048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_256048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_256048 prefixEnd_256048 := by exact prefixLift 256048
  have htrace : WordTrace (prefixWord ++ tailWord_256048) baseStart_256048 baseEnd_256048 := by
    simpa [prefixWord, tailWord_256048, baseEnd_256048] using wordTrace_append hprefix tailTrace_256048
  have hstable : (prefixWord ++ tailWord_256048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_256048).length < 2 ^ (prefixWord ++ tailWord_256048).sum := by decide
  have hdescent : baseEnd_256048 < baseStart_256048 := by decide
  rcases family_descends (prefixWord ++ tailWord_256048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_256064 : List Nat := [2, 1, 1, 2, 2, 5, 2, 1, 1, 6]
def baseStart_256064 : Nat := 118140960795 + 256064 * 2 ^ 59
def prefixEnd_256064 : Nat := 4983230072969 + 3 ^ 40 * 256064 * 2
def baseEnd_256064 : Nat := 43827970104330460707463

theorem tailTrace_256064 : CollatzResearch.WordTrace tailWord_256064 prefixEnd_256064 43827970104330460707463 := by
  unfold tailWord_256064
  simp only [CollatzResearch.WordTrace]
  refine ⟨4669710672165667547303623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6226280896220890063071497 4669710672165667547303623)
  ·
    refine ⟨7004566008248501320955435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4669710672165667547303623 7004566008248501320955435)
    ·
      refine ⟨10506849012372751981433153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7004566008248501320955435 10506849012372751981433153)
      ·
        refine ⟨7880136759279563986074865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10506849012372751981433153 7880136759279563986074865)
        ·
          refine ⟨5910102569459672989556149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7880136759279563986074865 5910102569459672989556149)
          ·
            refine ⟨554072115886844342770889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5910102569459672989556149 554072115886844342770889)
            ·
              refine ⟨415554086915133257078167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 554072115886844342770889 415554086915133257078167)
              ·
                refine ⟨623331130372699885617251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 415554086915133257078167 623331130372699885617251)
                ·
                  refine ⟨934996695559049828425877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 623331130372699885617251 934996695559049828425877)
                  ·
                    refine ⟨43827970104330460707463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 934996695559049828425877 43827970104330460707463)
                    ·
                      rfl

theorem cell23_256064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 2, 1, 1, 6].length) (baseStart_256064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_256064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_256064 prefixEnd_256064 := by exact prefixLift 256064
  have htrace : WordTrace (prefixWord ++ tailWord_256064) baseStart_256064 baseEnd_256064 := by
    simpa [prefixWord, tailWord_256064, baseEnd_256064] using wordTrace_append hprefix tailTrace_256064
  have hstable : (prefixWord ++ tailWord_256064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_256064).length < 2 ^ (prefixWord ++ tailWord_256064).sum := by decide
  have hdescent : baseEnd_256064 < baseStart_256064 := by decide
  rcases family_descends (prefixWord ++ tailWord_256064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_256088 : List Nat := [2, 1, 2, 2, 1, 6, 2, 1, 1, 1, 4]
def baseStart_256088 : Nat := 118140960795 + 256088 * 2 ^ 59
def prefixEnd_256088 : Nat := 4983230072969 + 3 ^ 40 * 256088 * 2
def baseEnd_256088 : Nat := 131496233848699288222279

theorem tailTrace_256088 : CollatzResearch.WordTrace tailWord_256088 prefixEnd_256088 131496233848699288222279 := by
  unfold tailWord_256088
  simp only [CollatzResearch.WordTrace]
  refine ⟨4670148348122193596740459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6226864464162924795653945 4670148348122193596740459)
  ·
    refine ⟨7005222522183290395110689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4670148348122193596740459 7005222522183290395110689)
    ·
      refine ⟨5253916891637467796333017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7005222522183290395110689 5253916891637467796333017)
      ·
        refine ⟨3940437668728100847249763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5253916891637467796333017 3940437668728100847249763)
        ·
          refine ⟨5910656503092151270874645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3940437668728100847249763 5910656503092151270874645)
          ·
            refine ⟨277062023582444590822249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 5910656503092151270874645 277062023582444590822249)
            ·
              refine ⟨207796517686833443116687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 277062023582444590822249 207796517686833443116687)
              ·
                refine ⟨311694776530250164675031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 207796517686833443116687 311694776530250164675031)
                ·
                  refine ⟨467542164795375247012547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 311694776530250164675031 467542164795375247012547)
                  ·
                    refine ⟨701313247193062870518821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 467542164795375247012547 701313247193062870518821)
                    ·
                      refine ⟨131496233848699288222279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 701313247193062870518821 131496233848699288222279)
                      ·
                        rfl

theorem cell23_256088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 6, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 6, 2, 1, 1, 1, 4].length) (baseStart_256088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_256088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_256088 prefixEnd_256088 := by exact prefixLift 256088
  have htrace : WordTrace (prefixWord ++ tailWord_256088) baseStart_256088 baseEnd_256088 := by
    simpa [prefixWord, tailWord_256088, baseEnd_256088] using wordTrace_append hprefix tailTrace_256088
  have hstable : (prefixWord ++ tailWord_256088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_256088).length < 2 ^ (prefixWord ++ tailWord_256088).sum := by decide
  have hdescent : baseEnd_256088 < baseStart_256088 := by decide
  rcases family_descends (prefixWord ++ tailWord_256088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_256097 : List Nat := [1, 2, 3, 1, 1, 2, 1, 2, 2, 2, 6]
def baseStart_256097 : Nat := 118140960795 + 256097 * 2 ^ 59
def prefixEnd_256097 : Nat := 4983230072969 + 3 ^ 40 * 256097 * 2
def baseEnd_256097 : Nat := 131500855174589753009737

theorem tailTrace_256097 : CollatzResearch.WordTrace tailWord_256097 prefixEnd_256097 131500855174589753009737 := by
  unfold tailWord_256097
  simp only [CollatzResearch.WordTrace]
  refine ⟨9340624953211781730558545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6227083302141187820372363 9340624953211781730558545)
  ·
    refine ⟨7005468714908836297918909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9340624953211781730558545 7005468714908836297918909)
    ·
      refine ⟨2627050768090813611719591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7005468714908836297918909 2627050768090813611719591)
      ·
        refine ⟨3940576152136220417579387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2627050768090813611719591 3940576152136220417579387)
        ·
          refine ⟨5910864228204330626369081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3940576152136220417579387 5910864228204330626369081)
          ·
            refine ⟨4433148171153247969776811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5910864228204330626369081 4433148171153247969776811)
            ·
              refine ⟨6649722256729871954665217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4433148171153247969776811 6649722256729871954665217)
              ·
                refine ⟨4987291692547403965998913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6649722256729871954665217 4987291692547403965998913)
                ·
                  refine ⟨3740468769410552974499185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4987291692547403965998913 3740468769410552974499185)
                  ·
                    refine ⟨2805351577057914730874389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3740468769410552974499185 2805351577057914730874389)
                    ·
                      refine ⟨131500855174589753009737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 2805351577057914730874389 131500855174589753009737)
                      ·
                        rfl

theorem cell23_256097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 2, 2, 2, 6].length) (baseStart_256097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_256097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_256097 prefixEnd_256097 := by exact prefixLift 256097
  have htrace : WordTrace (prefixWord ++ tailWord_256097) baseStart_256097 baseEnd_256097 := by
    simpa [prefixWord, tailWord_256097, baseEnd_256097] using wordTrace_append hprefix tailTrace_256097
  have hstable : (prefixWord ++ tailWord_256097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_256097).length < 2 ^ (prefixWord ++ tailWord_256097).sum := by decide
  have hdescent : baseEnd_256097 < baseStart_256097 := by decide
  rcases family_descends (prefixWord ++ tailWord_256097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_256098 : List Nat := [3, 3, 2, 2, 2, 1, 1, 1, 4, 4]
def baseStart_256098 : Nat := 118140960795 + 256098 * 2 ^ 59
def prefixEnd_256098 : Nat := 4983230072969 + 3 ^ 40 * 256098 * 2
def baseEnd_256098 : Nat := 43833789551748083032411

theorem tailTrace_256098 : CollatzResearch.WordTrace tailWord_256098 prefixEnd_256098 43833789551748083032411 := by
  unfold tailWord_256098
  simp only [CollatzResearch.WordTrace]
  refine ⟨2335165356552039725336237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6227107617472105934229965 2335165356552039725336237)
  ·
    refine ⟨875687008707014897001089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2335165356552039725336237 875687008707014897001089)
    ·
      refine ⟨656765256530261172750817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 875687008707014897001089 656765256530261172750817)
      ·
        refine ⟨492573942397695879563113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 656765256530261172750817 492573942397695879563113)
        ·
          refine ⟨369430456798271909672335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 492573942397695879563113 369430456798271909672335)
          ·
            refine ⟨554145685197407864508503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 369430456798271909672335 554145685197407864508503)
            ·
              refine ⟨831218527796111796762755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 554145685197407864508503 831218527796111796762755)
              ·
                refine ⟨1246827791694167695144133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 831218527796111796762755 1246827791694167695144133)
                ·
                  refine ⟨233780210942656442839525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1246827791694167695144133 233780210942656442839525)
                  ·
                    refine ⟨43833789551748083032411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 233780210942656442839525 43833789551748083032411)
                    ·
                      rfl

theorem cell23_256098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 1, 1, 4, 4].length) (baseStart_256098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_256098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_256098 prefixEnd_256098 := by exact prefixLift 256098
  have htrace : WordTrace (prefixWord ++ tailWord_256098) baseStart_256098 baseEnd_256098 := by
    simpa [prefixWord, tailWord_256098, baseEnd_256098] using wordTrace_append hprefix tailTrace_256098
  have hstable : (prefixWord ++ tailWord_256098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_256098).length < 2 ^ (prefixWord ++ tailWord_256098).sum := by decide
  have hdescent : baseEnd_256098 < baseStart_256098 := by decide
  rcases family_descends (prefixWord ++ tailWord_256098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_256118 : List Nat := [5, 1, 1, 2, 1, 4, 1, 1, 1, 2, 4]
def baseStart_256118 : Nat := 118140960795 + 256118 * 2 ^ 59
def prefixEnd_256118 : Nat := 4983230072969 + 3 ^ 40 * 256118 * 2
def baseEnd_256118 : Nat := 131511638268334170847141

theorem tailTrace_256118 : CollatzResearch.WordTrace tailWord_256118 prefixEnd_256118 131511638268334170847141 := by
  unfold tailWord_256118
  simp only [CollatzResearch.WordTrace]
  refine ⟨583836930383481394817063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6227593924090468211382005 583836930383481394817063)
  ·
    refine ⟨875755395575222092225595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 583836930383481394817063 875755395575222092225595)
    ·
      refine ⟨1313633093362833138338393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 875755395575222092225595 1313633093362833138338393)
      ·
        refine ⟨985224820022124853753795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1313633093362833138338393 985224820022124853753795)
        ·
          refine ⟨1477837230033187280630693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 985224820022124853753795 1477837230033187280630693)
          ·
            refine ⟨277094480631222615118255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1477837230033187280630693 277094480631222615118255)
            ·
              refine ⟨415641720946833922677383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 277094480631222615118255 415641720946833922677383)
              ·
                refine ⟨623462581420250884016075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 415641720946833922677383 623462581420250884016075)
                ·
                  refine ⟨935193872130376326024113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 623462581420250884016075 935193872130376326024113)
                  ·
                    refine ⟨701395404097782244518085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 935193872130376326024113 701395404097782244518085)
                    ·
                      refine ⟨131511638268334170847141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 701395404097782244518085 131511638268334170847141)
                      ·
                        rfl

theorem cell23_256118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 4, 1, 1, 1, 2, 4].length) (baseStart_256118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_256118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_256118 prefixEnd_256118 := by exact prefixLift 256118
  have htrace : WordTrace (prefixWord ++ tailWord_256118) baseStart_256118 baseEnd_256118 := by
    simpa [prefixWord, tailWord_256118, baseEnd_256118] using wordTrace_append hprefix tailTrace_256118
  have hstable : (prefixWord ++ tailWord_256118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_256118).length < 2 ^ (prefixWord ++ tailWord_256118).sum := by decide
  have hdescent : baseEnd_256118 < baseStart_256118 := by decide
  rcases family_descends (prefixWord ++ tailWord_256118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_256121 : List Nat := [1, 2, 1, 3, 4, 1, 3, 1, 1, 3, 3]
def baseStart_256121 : Nat := 118140960795 + 256121 * 2 ^ 59
def prefixEnd_256121 : Nat := 4983230072969 + 3 ^ 40 * 256121 * 2
def baseEnd_256121 : Nat := 131513178710297659109627

theorem tailTrace_256121 : CollatzResearch.WordTrace tailWord_256121 prefixEnd_256121 131513178710297659109627 := by
  unfold tailWord_256121
  simp only [CollatzResearch.WordTrace]
  refine ⟨9341500305124833829432217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6227666870083222552954811 9341500305124833829432217)
  ·
    refine ⟨7006125228843625372074163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9341500305124833829432217 7006125228843625372074163)
    ·
      refine ⟨10509187843265438058111245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7006125228843625372074163 10509187843265438058111245)
      ·
        refine ⟨3940945441224539271791717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10509187843265438058111245 3940945441224539271791717)
        ·
          refine ⟨738927270229601113460947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3940945441224539271791717 738927270229601113460947)
          ·
            refine ⟨1108390905344401670191421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 738927270229601113460947 1108390905344401670191421)
            ·
              refine ⟨415646589504150626321783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1108390905344401670191421 415646589504150626321783)
              ·
                refine ⟨623469884256225939482675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 415646589504150626321783 623469884256225939482675)
                ·
                  refine ⟨935204826384338909224013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 623469884256225939482675 935204826384338909224013)
                  ·
                    refine ⟨350701809894127090959005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 935204826384338909224013 350701809894127090959005)
                    ·
                      refine ⟨131513178710297659109627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 350701809894127090959005 131513178710297659109627)
                      ·
                        rfl

theorem cell23_256121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 3, 1, 1, 3, 3].length) (baseStart_256121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_256121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_256121 prefixEnd_256121 := by exact prefixLift 256121
  have htrace : WordTrace (prefixWord ++ tailWord_256121) baseStart_256121 baseEnd_256121 := by
    simpa [prefixWord, tailWord_256121, baseEnd_256121] using wordTrace_append hprefix tailTrace_256121
  have hstable : (prefixWord ++ tailWord_256121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_256121).length < 2 ^ (prefixWord ++ tailWord_256121).sum := by decide
  have hdescent : baseEnd_256121 < baseStart_256121 := by decide
  rcases family_descends (prefixWord ++ tailWord_256121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_256218 : List Nat := [3, 1, 1, 2, 2, 1, 6, 2, 5]
def baseStart_256218 : Nat := 118140960795 + 256218 * 2 ^ 59
def prefixEnd_256218 : Nat := 4983230072969 + 3 ^ 40 * 256218 * 2
def baseEnd_256218 : Nat := 14618109592642642177409

theorem tailTrace_256218 : CollatzResearch.WordTrace tailWord_256218 prefixEnd_256218 14618109592642642177409 := by
  unfold tailWord_256218
  simp only [CollatzResearch.WordTrace]
  refine ⟨2336259546443354848928327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6230025457182279597142205 2336259546443354848928327)
  ·
    refine ⟨3504389319665032273392491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2336259546443354848928327 3504389319665032273392491)
    ·
      refine ⟨5256583979497548410088737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3504389319665032273392491 5256583979497548410088737)
      ·
        refine ⟨3942437984623161307566553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5256583979497548410088737 3942437984623161307566553)
        ·
          refine ⟨2956828488467370980674915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3942437984623161307566553 2956828488467370980674915)
          ·
            refine ⟨4435242732701056471012373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2956828488467370980674915 4435242732701056471012373)
            ·
              refine ⟨207902003095362022078705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 4435242732701056471012373 207902003095362022078705)
              ·
                refine ⟨155926502321521516559029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 207902003095362022078705 155926502321521516559029)
                ·
                  refine ⟨14618109592642642177409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 155926502321521516559029 14618109592642642177409)
                  ·
                    rfl

theorem cell23_256218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 6, 2, 5].length) (baseStart_256218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_256218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_256218 prefixEnd_256218 := by exact prefixLift 256218
  have htrace : WordTrace (prefixWord ++ tailWord_256218) baseStart_256218 baseEnd_256218 := by
    simpa [prefixWord, tailWord_256218, baseEnd_256218] using wordTrace_append hprefix tailTrace_256218
  have hstable : (prefixWord ++ tailWord_256218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_256218).length < 2 ^ (prefixWord ++ tailWord_256218).sum := by decide
  have hdescent : baseEnd_256218 < baseStart_256218 := by decide
  rcases family_descends (prefixWord ++ tailWord_256218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_256224 : List Nat := [2, 1, 1, 3, 1, 3, 1, 3, 1, 2, 5]
def baseStart_256224 : Nat := 118140960795 + 256224 * 2 ^ 59
def prefixEnd_256224 : Nat := 4983230072969 + 3 ^ 40 * 256224 * 2
def baseEnd_256224 : Nat := 131566067217710756121653

theorem tailTrace_256224 : CollatzResearch.WordTrace tailWord_256224 prefixEnd_256224 131566067217710756121653 := by
  unfold tailWord_256224
  simp only [CollatzResearch.WordTrace]
  refine ⟨4672628511875841210215863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6230171349167788280287817 4672628511875841210215863)
  ·
    refine ⟨7008942767813761815323795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4672628511875841210215863 7008942767813761815323795)
    ·
      refine ⟨10513414151720642722985693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7008942767813761815323795 10513414151720642722985693)
      ·
        refine ⟨3942530306895241021119635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10513414151720642722985693 3942530306895241021119635)
        ·
          refine ⟨5913795460342861531679453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3942530306895241021119635 5913795460342861531679453)
          ·
            refine ⟨2217673297628573074379795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5913795460342861531679453 2217673297628573074379795)
            ·
              refine ⟨3326509946442859611569693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2217673297628573074379795 3326509946442859611569693)
              ·
                refine ⟨1247441229916072354338635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3326509946442859611569693 1247441229916072354338635)
                ·
                  refine ⟨1871161844874108531507953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1247441229916072354338635 1871161844874108531507953)
                  ·
                    refine ⟨1403371383655581398630965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1871161844874108531507953 1403371383655581398630965)
                    ·
                      refine ⟨131566067217710756121653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1403371383655581398630965 131566067217710756121653)
                      ·
                        rfl

theorem cell23_256224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 3, 1, 2, 5].length) (baseStart_256224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_256224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_256224 prefixEnd_256224 := by exact prefixLift 256224
  have htrace : WordTrace (prefixWord ++ tailWord_256224) baseStart_256224 baseEnd_256224 := by
    simpa [prefixWord, tailWord_256224, baseEnd_256224] using wordTrace_append hprefix tailTrace_256224
  have hstable : (prefixWord ++ tailWord_256224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_256224).length < 2 ^ (prefixWord ++ tailWord_256224).sum := by decide
  have hdescent : baseEnd_256224 < baseStart_256224 := by decide
  rcases family_descends (prefixWord ++ tailWord_256224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_256271 : List Nat := [1, 1, 2, 1, 1, 1, 3, 6, 2, 2, 3]
def baseStart_256271 : Nat := 118140960795 + 256271 * 2 ^ 59
def prefixEnd_256271 : Nat := 4983230072969 + 3 ^ 40 * 256271 * 2
def baseEnd_256271 : Nat := 131590200808472072233937

theorem tailTrace_256271 : CollatzResearch.WordTrace tailWord_256271 prefixEnd_256271 131590200808472072233937 := by
  unfold tailWord_256271
  simp only [CollatzResearch.WordTrace]
  refine ⟨9346971254581409447392667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6231314169720939631595111 9346971254581409447392667)
  ·
    refine ⟨14020456881872114171089001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9346971254581409447392667 14020456881872114171089001)
    ·
      refine ⟨10515342661404085628316751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14020456881872114171089001 10515342661404085628316751)
      ·
        refine ⟨15773013992106128442475127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10515342661404085628316751 15773013992106128442475127)
        ·
          refine ⟨23659520988159192663712691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15773013992106128442475127 23659520988159192663712691)
          ·
            refine ⟨35489281482238788995569037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23659520988159192663712691 35489281482238788995569037)
            ·
              refine ⟨13308480555839545873338389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35489281482238788995569037 13308480555839545873338389)
              ·
                refine ⟨623835026054978712812737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 13308480555839545873338389 623835026054978712812737)
                ·
                  refine ⟨467876269541234034609553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 623835026054978712812737 467876269541234034609553)
                  ·
                    refine ⟨350907202155925525957165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 467876269541234034609553 350907202155925525957165)
                    ·
                      refine ⟨131590200808472072233937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 350907202155925525957165 131590200808472072233937)
                      ·
                        rfl

theorem cell23_256271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 6, 2, 2, 3].length) (baseStart_256271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_256271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_256271 prefixEnd_256271 := by exact prefixLift 256271
  have htrace : WordTrace (prefixWord ++ tailWord_256271) baseStart_256271 baseEnd_256271 := by
    simpa [prefixWord, tailWord_256271, baseEnd_256271] using wordTrace_append hprefix tailTrace_256271
  have hstable : (prefixWord ++ tailWord_256271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_256271).length < 2 ^ (prefixWord ++ tailWord_256271).sum := by decide
  have hdescent : baseEnd_256271 < baseStart_256271 := by decide
  rcases family_descends (prefixWord ++ tailWord_256271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_256328 : List Nat := [2, 1, 3, 1, 1, 2, 3, 1, 4, 3, 2]
def baseStart_256328 : Nat := 118140960795 + 256328 * 2 ^ 59
def prefixEnd_256328 : Nat := 4983230072969 + 3 ^ 40 * 256328 * 2
def baseEnd_256328 : Nat := 131619469205778349221175

theorem tailTrace_256328 : CollatzResearch.WordTrace tailWord_256328 prefixEnd_256328 131619469205778349221175 := by
  unfold tailWord_256328
  simp only [CollatzResearch.WordTrace]
  refine ⟨4674525107687454091108819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6232700143583272121478425 4674525107687454091108819)
  ·
    refine ⟨7011787661531181136663229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4674525107687454091108819 7011787661531181136663229)
    ·
      refine ⟨2629420373074192926248711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7011787661531181136663229 2629420373074192926248711)
      ·
        refine ⟨3944130559611289389373067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2629420373074192926248711 3944130559611289389373067)
        ·
          refine ⟨5916195839416934084059601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3944130559611289389373067 5916195839416934084059601)
          ·
            refine ⟨4437146879562700563044701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5916195839416934084059601 4437146879562700563044701)
            ·
              refine ⟨1663930079836012711141763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4437146879562700563044701 1663930079836012711141763)
              ·
                refine ⟨2495895119754019066712645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1663930079836012711141763 2495895119754019066712645)
                ·
                  refine ⟨467980334953878575008621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2495895119754019066712645 467980334953878575008621)
                  ·
                    refine ⟨175492625607704465628233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 467980334953878575008621 175492625607704465628233)
                    ·
                      refine ⟨131619469205778349221175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 175492625607704465628233 131619469205778349221175)
                      ·
                        rfl

theorem cell23_256328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 1, 4, 3, 2].length) (baseStart_256328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_256328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_256328 prefixEnd_256328 := by exact prefixLift 256328
  have htrace : WordTrace (prefixWord ++ tailWord_256328) baseStart_256328 baseEnd_256328 := by
    simpa [prefixWord, tailWord_256328, baseEnd_256328] using wordTrace_append hprefix tailTrace_256328
  have hstable : (prefixWord ++ tailWord_256328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_256328).length < 2 ^ (prefixWord ++ tailWord_256328).sum := by decide
  have hdescent : baseEnd_256328 < baseStart_256328 := by decide
  rcases family_descends (prefixWord ++ tailWord_256328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_256362 : List Nat := [3, 1, 3, 3, 1, 2, 2, 1, 2, 3, 2]
def baseStart_256362 : Nat := 118140960795 + 256362 * 2 ^ 59
def prefixEnd_256362 : Nat := 4983230072969 + 3 ^ 40 * 256362 * 2
def baseEnd_256362 : Nat := 131636927548031216196019

theorem tailTrace_256362 : CollatzResearch.WordTrace tailWord_256362 prefixEnd_256362 131636927548031216196019 := by
  unfold tailWord_256362
  simp only [CollatzResearch.WordTrace]
  refine ⟨2337572574312932997238835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6233526864834487992636893 2337572574312932997238835)
  ·
    refine ⟨3506358861469399495858253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2337572574312932997238835 3506358861469399495858253)
    ·
      refine ⟨1314884573051024810946845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3506358861469399495858253 1314884573051024810946845)
      ·
        refine ⟨493081714894134304105067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1314884573051024810946845 493081714894134304105067)
        ·
          refine ⟨739622572341201456157601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 493081714894134304105067 739622572341201456157601)
          ·
            refine ⟨554716929255901092118201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 739622572341201456157601 554716929255901092118201)
            ·
              refine ⟨416037696941925819088651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 554716929255901092118201 416037696941925819088651)
              ·
                refine ⟨624056545412888728632977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 416037696941925819088651 624056545412888728632977)
                ·
                  refine ⟨468042409059666546474733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 624056545412888728632977 468042409059666546474733)
                  ·
                    refine ⟨175515903397374954928025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 468042409059666546474733 175515903397374954928025)
                    ·
                      refine ⟨131636927548031216196019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 175515903397374954928025 131636927548031216196019)
                      ·
                        rfl

theorem cell23_256362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 2, 1, 2, 3, 2].length) (baseStart_256362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_256362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_256362 prefixEnd_256362 := by exact prefixLift 256362
  have htrace : WordTrace (prefixWord ++ tailWord_256362) baseStart_256362 baseEnd_256362 := by
    simpa [prefixWord, tailWord_256362, baseEnd_256362] using wordTrace_append hprefix tailTrace_256362
  have hstable : (prefixWord ++ tailWord_256362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_256362).length < 2 ^ (prefixWord ++ tailWord_256362).sum := by decide
  have hdescent : baseEnd_256362 < baseStart_256362 := by decide
  rcases family_descends (prefixWord ++ tailWord_256362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_256371 : List Nat := [1, 1, 1, 2, 2, 1, 2, 6, 1, 2, 4]
def baseStart_256371 : Nat := 118140960795 + 256371 * 2 ^ 59
def prefixEnd_256371 : Nat := 4983230072969 + 3 ^ 40 * 256371 * 2
def baseEnd_256371 : Nat := 131641548873921680983477

theorem tailTrace_256371 : CollatzResearch.WordTrace tailWord_256371 prefixEnd_256371 131641548873921680983477 := by
  unfold tailWord_256371
  simp only [CollatzResearch.WordTrace]
  refine ⟨9350618554219126526032967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6233745702812751017355311 9350618554219126526032967)
  ·
    refine ⟨14025927831328689789049451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9350618554219126526032967 14025927831328689789049451)
    ·
      refine ⟨21038891746993034683574177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14025927831328689789049451 21038891746993034683574177)
      ·
        refine ⟨15779168810244776012680633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21038891746993034683574177 15779168810244776012680633)
        ·
          refine ⟨11834376607683582009510475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15779168810244776012680633 11834376607683582009510475)
          ·
            refine ⟨17751564911525373014265713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11834376607683582009510475 17751564911525373014265713)
            ·
              refine ⟨13313673683644029760699285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17751564911525373014265713 13313673683644029760699285)
              ·
                refine ⟨624078453920813895032779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 13313673683644029760699285 624078453920813895032779)
                ·
                  refine ⟨936117680881220842549169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 624078453920813895032779 936117680881220842549169)
                  ·
                    refine ⟨702088260660915631911877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 936117680881220842549169 702088260660915631911877)
                    ·
                      refine ⟨131641548873921680983477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 702088260660915631911877 131641548873921680983477)
                      ·
                        rfl

theorem cell23_256371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 6, 1, 2, 4].length) (baseStart_256371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_256371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_256371 prefixEnd_256371 := by exact prefixLift 256371
  have htrace : WordTrace (prefixWord ++ tailWord_256371) baseStart_256371 baseEnd_256371 := by
    simpa [prefixWord, tailWord_256371, baseEnd_256371] using wordTrace_append hprefix tailTrace_256371
  have hstable : (prefixWord ++ tailWord_256371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_256371).length < 2 ^ (prefixWord ++ tailWord_256371).sum := by decide
  have hdescent : baseEnd_256371 < baseStart_256371 := by decide
  rcases family_descends (prefixWord ++ tailWord_256371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_256385 : List Nat := [1, 2, 4, 3, 1, 1, 1, 4, 2, 4]
def baseStart_256385 : Nat := 118140960795 + 256385 * 2 ^ 59
def prefixEnd_256385 : Nat := 4983230072969 + 3 ^ 40 * 256385 * 2
def baseEnd_256385 : Nat := 43882912534361542069471

theorem tailTrace_256385 : CollatzResearch.WordTrace tailWord_256385 prefixEnd_256385 43882912534361542069471 := by
  unfold tailWord_256385
  simp only [CollatzResearch.WordTrace]
  refine ⟨9351129176168406917042609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6234086117445604611361739 9351129176168406917042609)
  ·
    refine ⟨7013346882126305187781957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9351129176168406917042609 7013346882126305187781957)
    ·
      refine ⟨1315002540398682222709117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7013346882126305187781957 1315002540398682222709117)
      ·
        refine ⟨493125952649505833515919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1315002540398682222709117 493125952649505833515919)
        ·
          refine ⟨739688928974258750273879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 493125952649505833515919 739688928974258750273879)
          ·
            refine ⟨1109533393461388125410819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 739688928974258750273879 1109533393461388125410819)
            ·
              refine ⟨1664300090192082188116229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1109533393461388125410819 1664300090192082188116229)
              ·
                refine ⟨312056266911015410271793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1664300090192082188116229 312056266911015410271793)
                ·
                  refine ⟨234042200183261557703845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 312056266911015410271793 234042200183261557703845)
                  ·
                    refine ⟨43882912534361542069471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 234042200183261557703845 43882912534361542069471)
                    ·
                      rfl

theorem cell23_256385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 4, 2, 4].length) (baseStart_256385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_256385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_256385 prefixEnd_256385 := by exact prefixLift 256385
  have htrace : WordTrace (prefixWord ++ tailWord_256385) baseStart_256385 baseEnd_256385 := by
    simpa [prefixWord, tailWord_256385, baseEnd_256385] using wordTrace_append hprefix tailTrace_256385
  have hstable : (prefixWord ++ tailWord_256385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_256385).length < 2 ^ (prefixWord ++ tailWord_256385).sum := by decide
  have hdescent : baseEnd_256385 < baseStart_256385 := by decide
  rcases family_descends (prefixWord ++ tailWord_256385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_256386 : List Nat := [3, 4, 2, 1, 2, 1, 1, 4, 1, 1, 3]
def baseStart_256386 : Nat := 118140960795 + 256386 * 2 ^ 59
def prefixEnd_256386 : Nat := 4983230072969 + 3 ^ 40 * 256386 * 2
def baseEnd_256386 : Nat := 131649251083739122295909

theorem tailTrace_256386 : CollatzResearch.WordTrace tailWord_256386 prefixEnd_256386 131649251083739122295909 := by
  unfold tailWord_256386
  simp only [CollatzResearch.WordTrace]
  refine ⟨2337791412291196021957253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6234110432776522725219341 2337791412291196021957253)
  ·
    refine ⟨438335889804599254116985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2337791412291196021957253 438335889804599254116985)
    ·
      refine ⟨328751917353449440587739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 438335889804599254116985 328751917353449440587739)
      ·
        refine ⟨493127876030174160881609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 328751917353449440587739 493127876030174160881609)
        ·
          refine ⟨369845907022630620661207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 493127876030174160881609 369845907022630620661207)
          ·
            refine ⟨554768860533945930991811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 369845907022630620661207 554768860533945930991811)
            ·
              refine ⟨832153290800918896487717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 554768860533945930991811 832153290800918896487717)
              ·
                refine ⟨156028742025172293091447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 832153290800918896487717 156028742025172293091447)
                ·
                  refine ⟨234043113037758439637171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 156028742025172293091447 234043113037758439637171)
                  ·
                    refine ⟨351064669556637659455757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 234043113037758439637171 351064669556637659455757)
                    ·
                      refine ⟨131649251083739122295909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 351064669556637659455757 131649251083739122295909)
                      ·
                        rfl

theorem cell23_256386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 1, 4, 1, 1, 3].length) (baseStart_256386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_256386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_256386 prefixEnd_256386 := by exact prefixLift 256386
  have htrace : WordTrace (prefixWord ++ tailWord_256386) baseStart_256386 baseEnd_256386 := by
    simpa [prefixWord, tailWord_256386, baseEnd_256386] using wordTrace_append hprefix tailTrace_256386
  have hstable : (prefixWord ++ tailWord_256386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_256386).length < 2 ^ (prefixWord ++ tailWord_256386).sum := by decide
  have hdescent : baseEnd_256386 < baseStart_256386 := by decide
  rcases family_descends (prefixWord ++ tailWord_256386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_256398 : List Nat := [4, 1, 1, 4, 1, 1, 3, 8]
def baseStart_256398 : Nat := 118140960795 + 256398 * 2 ^ 59
def prefixEnd_256398 : Nat := 4983230072969 + 3 ^ 40 * 256398 * 2
def baseEnd_256398 : Nat := 4876126401910854642439

theorem tailTrace_256398 : CollatzResearch.WordTrace tailWord_256398 prefixEnd_256398 4876126401910854642439 := by
  unfold tailWord_256398
  simp only [CollatzResearch.WordTrace]
  refine ⟨1168950415640163767158231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6234402216747540091510565 1168950415640163767158231)
  ·
    refine ⟨1753425623460245650737347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1168950415640163767158231 1753425623460245650737347)
    ·
      refine ⟨2630138435190368476106021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1753425623460245650737347 2630138435190368476106021)
      ·
        refine ⟨493150956598194089269879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2630138435190368476106021 493150956598194089269879)
        ·
          refine ⟨739726434897291133904819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 493150956598194089269879 739726434897291133904819)
          ·
            refine ⟨1109589652345936700857229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 739726434897291133904819 1109589652345936700857229)
            ·
              refine ⟨416096119629726262821461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1109589652345936700857229 416096119629726262821461)
              ·
                refine ⟨4876126401910854642439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 416096119629726262821461 4876126401910854642439)
                ·
                  rfl

theorem cell23_256398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 3, 8].length) (baseStart_256398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_256398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_256398 prefixEnd_256398 := by exact prefixLift 256398
  have htrace : WordTrace (prefixWord ++ tailWord_256398) baseStart_256398 baseEnd_256398 := by
    simpa [prefixWord, tailWord_256398, baseEnd_256398] using wordTrace_append hprefix tailTrace_256398
  have hstable : (prefixWord ++ tailWord_256398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_256398).length < 2 ^ (prefixWord ++ tailWord_256398).sum := by decide
  have hdescent : baseEnd_256398 < baseStart_256398 := by decide
  rcases family_descends (prefixWord ++ tailWord_256398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_256421 : List Nat := [1, 3, 1, 2, 1, 1, 4, 1, 2, 2, 5]
def baseStart_256421 : Nat := 118140960795 + 256421 * 2 ^ 59
def prefixEnd_256421 : Nat := 4983230072969 + 3 ^ 40 * 256421 * 2
def baseEnd_256421 : Nat := 131667222906646485358247

theorem tailTrace_256421 : CollatzResearch.WordTrace tailWord_256421 prefixEnd_256421 131667222906646485358247 := by
  unfold tailWord_256421
  simp only [CollatzResearch.WordTrace]
  refine ⟨9352442204037985065353117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6234961469358656710235411 9352442204037985065353117)
  ·
    refine ⟨3507165826514244399507419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9352442204037985065353117 3507165826514244399507419)
    ·
      refine ⟨5260748739771366599261129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3507165826514244399507419 5260748739771366599261129)
      ·
        refine ⟨3945561554828524949445847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5260748739771366599261129 3945561554828524949445847)
        ·
          refine ⟨5918342332242787424168771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3945561554828524949445847 5918342332242787424168771)
          ·
            refine ⟨8877513498364181136253157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5918342332242787424168771 8877513498364181136253157)
            ·
              refine ⟨1664533780943283963047467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8877513498364181136253157 1664533780943283963047467)
              ·
                refine ⟨2496800671414925944571201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1664533780943283963047467 2496800671414925944571201)
                ·
                  refine ⟨1872600503561194458428401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2496800671414925944571201 1872600503561194458428401)
                  ·
                    refine ⟨1404450377670895843821301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1872600503561194458428401 1404450377670895843821301)
                    ·
                      refine ⟨131667222906646485358247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1404450377670895843821301 131667222906646485358247)
                      ·
                        rfl

theorem cell23_256421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 1, 2, 2, 5].length) (baseStart_256421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_256421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_256421 prefixEnd_256421 := by exact prefixLift 256421
  have htrace : WordTrace (prefixWord ++ tailWord_256421) baseStart_256421 baseEnd_256421 := by
    simpa [prefixWord, tailWord_256421, baseEnd_256421] using wordTrace_append hprefix tailTrace_256421
  have hstable : (prefixWord ++ tailWord_256421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_256421).length < 2 ^ (prefixWord ++ tailWord_256421).sum := by decide
  have hdescent : baseEnd_256421 < baseStart_256421 := by decide
  rcases family_descends (prefixWord ++ tailWord_256421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_256436 : List Nat := [2, 5, 2, 2, 1, 2, 1, 2, 2, 4]
def baseStart_256436 : Nat := 118140960795 + 256436 * 2 ^ 59
def prefixEnd_256436 : Nat := 4983230072969 + 3 ^ 40 * 256436 * 2
def baseEnd_256436 : Nat := 43891641705487975556893

theorem tailTrace_256436 : CollatzResearch.WordTrace tailWord_256436 prefixEnd_256436 43891641705487975556893 := by
  unfold tailWord_256436
  simp only [CollatzResearch.WordTrace]
  refine ⟨4676494649491821313574581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6235326199322428418099441 4676494649491821313574581)
  ·
    refine ⟨438421373389858248147617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4676494649491821313574581 438421373389858248147617)
    ·
      refine ⟨328816030042393686110713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 438421373389858248147617 328816030042393686110713)
      ·
        refine ⟨246612022531795264583035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 328816030042393686110713 246612022531795264583035)
        ·
          refine ⟨369918033797692896874553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246612022531795264583035 369918033797692896874553)
          ·
            refine ⟨277438525348269672655915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 369918033797692896874553 277438525348269672655915)
            ·
              refine ⟨416157788022404508983873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 277438525348269672655915 416157788022404508983873)
              ·
                refine ⟨312118341016803381737905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 416157788022404508983873 312118341016803381737905)
                ·
                  refine ⟨234088755762602536303429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 312118341016803381737905 234088755762602536303429)
                  ·
                    refine ⟨43891641705487975556893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 234088755762602536303429 43891641705487975556893)
                    ·
                      rfl

theorem cell23_256436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 2, 1, 2, 2, 4].length) (baseStart_256436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_256436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_256436 prefixEnd_256436 := by exact prefixLift 256436
  have htrace : WordTrace (prefixWord ++ tailWord_256436) baseStart_256436 baseEnd_256436 := by
    simpa [prefixWord, tailWord_256436, baseEnd_256436] using wordTrace_append hprefix tailTrace_256436
  have hstable : (prefixWord ++ tailWord_256436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_256436).length < 2 ^ (prefixWord ++ tailWord_256436).sum := by decide
  have hdescent : baseEnd_256436 < baseStart_256436 := by decide
  rcases family_descends (prefixWord ++ tailWord_256436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_256451 : List Nat := [1, 1, 1, 3, 1, 1, 3, 2, 4, 1, 5]
def baseStart_256451 : Nat := 118140960795 + 256451 * 2 ^ 59
def prefixEnd_256451 : Nat := 4983230072969 + 3 ^ 40 * 256451 * 2
def baseEnd_256451 : Nat := 131682627326281367983109

theorem tailTrace_256451 : CollatzResearch.WordTrace tailWord_256451 prefixEnd_256451 131682627326281367983109 := by
  unfold tailWord_256451
  simp only [CollatzResearch.WordTrace]
  refine ⟨9353536393929300188945207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6235690929286200125963471 9353536393929300188945207)
  ·
    refine ⟨14030304590893950283417811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9353536393929300188945207 14030304590893950283417811)
    ·
      refine ⟨21045456886340925425126717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14030304590893950283417811 21045456886340925425126717)
      ·
        refine ⟨7892046332377847034422519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21045456886340925425126717 7892046332377847034422519)
        ·
          refine ⟨11838069498566770551633779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7892046332377847034422519 11838069498566770551633779)
          ·
            refine ⟨17757104247850155827450669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11838069498566770551633779 17757104247850155827450669)
            ·
              refine ⟨6658914092943808435294001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17757104247850155827450669 6658914092943808435294001)
              ·
                refine ⟨4994185569707856326470501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6658914092943808435294001 4994185569707856326470501)
                ·
                  refine ⟨936409794320223061213219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4994185569707856326470501 936409794320223061213219)
                  ·
                    refine ⟨1404614691480334591819829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 936409794320223061213219 1404614691480334591819829)
                    ·
                      refine ⟨131682627326281367983109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1404614691480334591819829 131682627326281367983109)
                      ·
                        rfl

theorem cell23_256451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 2, 4, 1, 5].length) (baseStart_256451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_256451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_256451 prefixEnd_256451 := by exact prefixLift 256451
  have htrace : WordTrace (prefixWord ++ tailWord_256451) baseStart_256451 baseEnd_256451 := by
    simpa [prefixWord, tailWord_256451, baseEnd_256451] using wordTrace_append hprefix tailTrace_256451
  have hstable : (prefixWord ++ tailWord_256451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_256451).length < 2 ^ (prefixWord ++ tailWord_256451).sum := by decide
  have hdescent : baseEnd_256451 < baseStart_256451 := by decide
  rcases family_descends (prefixWord ++ tailWord_256451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_256485 : List Nat := [1, 3, 1, 5, 2, 1, 1, 1, 2, 1, 5]
def baseStart_256485 : Nat := 118140960795 + 256485 * 2 ^ 59
def prefixEnd_256485 : Nat := 4983230072969 + 3 ^ 40 * 256485 * 2
def baseEnd_256485 : Nat := 131700085668534234957953

theorem tailTrace_256485 : CollatzResearch.WordTrace tailWord_256485 prefixEnd_256485 131700085668534234957953 := by
  unfold tailWord_256485
  simp only [CollatzResearch.WordTrace]
  refine ⟨9354776475806123995682909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6236517650537415997121939 9354776475806123995682909)
  ·
    refine ⟨3508041178427296498381091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9354776475806123995682909 3508041178427296498381091)
    ·
      refine ⟨5262061767640944747571637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3508041178427296498381091 5262061767640944747571637)
      ·
        refine ⟨493318290716338570084841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5262061767640944747571637 493318290716338570084841)
        ·
          refine ⟨369988718037253927563631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 493318290716338570084841 369988718037253927563631)
          ·
            refine ⟨554983077055880891345447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 369988718037253927563631 554983077055880891345447)
            ·
              refine ⟨832474615583821337018171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 554983077055880891345447 832474615583821337018171)
              ·
                refine ⟨1248711923375732005527257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 832474615583821337018171 1248711923375732005527257)
                ·
                  refine ⟨936533942531799004145443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1248711923375732005527257 936533942531799004145443)
                  ·
                    refine ⟨1404800913797698506218165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 936533942531799004145443 1404800913797698506218165)
                    ·
                      refine ⟨131700085668534234957953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1404800913797698506218165 131700085668534234957953)
                      ·
                        rfl

theorem cell23_256485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 1, 1, 2, 1, 5].length) (baseStart_256485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_256485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_256485 prefixEnd_256485 := by exact prefixLift 256485
  have htrace : WordTrace (prefixWord ++ tailWord_256485) baseStart_256485 baseEnd_256485 := by
    simpa [prefixWord, tailWord_256485, baseEnd_256485] using wordTrace_append hprefix tailTrace_256485
  have hstable : (prefixWord ++ tailWord_256485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_256485).length < 2 ^ (prefixWord ++ tailWord_256485).sum := by decide
  have hdescent : baseEnd_256485 < baseStart_256485 := by decide
  rcases family_descends (prefixWord ++ tailWord_256485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_256516 : List Nat := [2, 3, 2, 3, 1, 1, 4, 1, 2, 2, 2]
def baseStart_256516 : Nat := 118140960795 + 256516 * 2 ^ 59
def prefixEnd_256516 : Nat := 4983230072969 + 3 ^ 40 * 256516 * 2
def baseEnd_256516 : Nat := 131716003568823613670311

theorem tailTrace_256516 : CollatzResearch.WordTrace tailWord_256516 prefixEnd_256516 131716003568823613670311 := by
  unfold tailWord_256516
  simp only [CollatzResearch.WordTrace]
  refine ⟨4677953569346908145030701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6237271425795877526707601 4677953569346908145030701)
  ·
    refine ⟨1754232588505090554386513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4677953569346908145030701 1754232588505090554386513)
    ·
      refine ⟨1315674441378817915789885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1754232588505090554386513 1315674441378817915789885)
      ·
        refine ⟨493377915517056718421207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1315674441378817915789885 493377915517056718421207)
        ·
          refine ⟨740066873275585077631811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 493377915517056718421207 740066873275585077631811)
          ·
            refine ⟨1110100309913377616447717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 740066873275585077631811 1110100309913377616447717)
            ·
              refine ⟨208143808108758303083947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1110100309913377616447717 208143808108758303083947)
              ·
                refine ⟨312215712163137454625921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 208143808108758303083947 312215712163137454625921)
                ·
                  refine ⟨234161784122353090969441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 312215712163137454625921 234161784122353090969441)
                  ·
                    refine ⟨175621338091764818227081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 234161784122353090969441 175621338091764818227081)
                    ·
                      refine ⟨131716003568823613670311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 175621338091764818227081 131716003568823613670311)
                      ·
                        rfl

theorem cell23_256516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 4, 1, 2, 2, 2].length) (baseStart_256516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_256516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_256516 prefixEnd_256516 := by exact prefixLift 256516
  have htrace : WordTrace (prefixWord ++ tailWord_256516) baseStart_256516 baseEnd_256516 := by
    simpa [prefixWord, tailWord_256516, baseEnd_256516] using wordTrace_append hprefix tailTrace_256516
  have hstable : (prefixWord ++ tailWord_256516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_256516).length < 2 ^ (prefixWord ++ tailWord_256516).sum := by decide
  have hdescent : baseEnd_256516 < baseStart_256516 := by decide
  rcases family_descends (prefixWord ++ tailWord_256516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_256538 : List Nat := [3, 1, 1, 3, 1, 1, 2, 3, 1, 3, 4]
def baseStart_256538 : Nat := 118140960795 + 256538 * 2 ^ 59
def prefixEnd_256538 : Nat := 4983230072969 + 3 ^ 40 * 256538 * 2
def baseEnd_256538 : Nat := 131727300143222527595209

theorem tailTrace_256538 : CollatzResearch.WordTrace tailWord_256538 prefixEnd_256538 131727300143222527595209 := by
  unfold tailWord_256538
  simp only [CollatzResearch.WordTrace]
  refine ⟨2339177386153528511840567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6237806363076076031574845 2339177386153528511840567)
  ·
    refine ⟨3508766079230292767760851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2339177386153528511840567 3508766079230292767760851)
    ·
      refine ⟨5263149118845439151641277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3508766079230292767760851 5263149118845439151641277)
      ·
        refine ⟨1973680919567039681865479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5263149118845439151641277 1973680919567039681865479)
        ·
          refine ⟨2960521379350559522798219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1973680919567039681865479 2960521379350559522798219)
          ·
            refine ⟨4440782069025839284197329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2960521379350559522798219 4440782069025839284197329)
            ·
              refine ⟨3330586551769379463147997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4440782069025839284197329 3330586551769379463147997)
              ·
                refine ⟨1248969956913517298680499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3330586551769379463147997 1248969956913517298680499)
                ·
                  refine ⟨1873454935370275948020749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1248969956913517298680499 1873454935370275948020749)
                  ·
                    refine ⟨702545600763853480507781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1873454935370275948020749 702545600763853480507781)
                    ·
                      refine ⟨131727300143222527595209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 702545600763853480507781 131727300143222527595209)
                      ·
                        rfl

theorem cell23_256538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 3, 1, 3, 4].length) (baseStart_256538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_256538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_256538 prefixEnd_256538 := by exact prefixLift 256538
  have htrace : WordTrace (prefixWord ++ tailWord_256538) baseStart_256538 baseEnd_256538 := by
    simpa [prefixWord, tailWord_256538, baseEnd_256538] using wordTrace_append hprefix tailTrace_256538
  have hstable : (prefixWord ++ tailWord_256538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_256538).length < 2 ^ (prefixWord ++ tailWord_256538).sum := by decide
  have hdescent : baseEnd_256538 < baseStart_256538 := by decide
  rcases family_descends (prefixWord ++ tailWord_256538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_256565 : List Nat := [1, 3, 3, 1, 1, 2, 2, 3, 3, 4]
def baseStart_256565 : Nat := 118140960795 + 256565 * 2 ^ 59
def prefixEnd_256565 : Nat := 4983230072969 + 3 ^ 40 * 256565 * 2
def baseEnd_256565 : Nat := 43913721373631307319195

theorem tailTrace_256565 : CollatzResearch.WordTrace tailWord_256565 prefixEnd_256565 43913721373631307319195 := by
  unfold tailWord_256565
  simp only [CollatzResearch.WordTrace]
  refine ⟨9357694315516297658595149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6238462877010865105730099 9357694315516297658595149)
  ·
    refine ⟨3509135368318611621973181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9357694315516297658595149 3509135368318611621973181)
    ·
      refine ⟨1315925763119479358239943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3509135368318611621973181 1315925763119479358239943)
      ·
        refine ⟨1973888644679219037359915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1315925763119479358239943 1973888644679219037359915)
        ·
          refine ⟨2960832967018828556039873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1973888644679219037359915 2960832967018828556039873)
          ·
            refine ⟨2220624725264121417029905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2960832967018828556039873 2220624725264121417029905)
            ·
              refine ⟨1665468543948091062772429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2220624725264121417029905 1665468543948091062772429)
              ·
                refine ⟨624550703980534148539661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1665468543948091062772429 624550703980534148539661)
                ·
                  refine ⟨234206513992700305702373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 624550703980534148539661 234206513992700305702373)
                  ·
                    refine ⟨43913721373631307319195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 234206513992700305702373 43913721373631307319195)
                    ·
                      rfl

theorem cell23_256565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 3, 3, 4].length) (baseStart_256565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_256565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_256565 prefixEnd_256565 := by exact prefixLift 256565
  have htrace : WordTrace (prefixWord ++ tailWord_256565) baseStart_256565 baseEnd_256565 := by
    simpa [prefixWord, tailWord_256565, baseEnd_256565] using wordTrace_append hprefix tailTrace_256565
  have hstable : (prefixWord ++ tailWord_256565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_256565).length < 2 ^ (prefixWord ++ tailWord_256565).sum := by decide
  have hdescent : baseEnd_256565 < baseStart_256565 := by decide
  rcases family_descends (prefixWord ++ tailWord_256565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_256572 : List Nat := [2, 2, 2, 2, 3, 2, 1, 1, 2, 4, 2]
def baseStart_256572 : Nat := 118140960795 + 256572 * 2 ^ 59
def prefixEnd_256572 : Nat := 4983230072969 + 3 ^ 40 * 256572 * 2
def baseEnd_256572 : Nat := 131744758485475394570053

theorem tailTrace_256572 : CollatzResearch.WordTrace tailWord_256572 prefixEnd_256572 131744758485475394570053 := by
  unfold tailWord_256572
  simp only [CollatzResearch.WordTrace]
  refine ⟨4678974813245468927049985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6238633084327291902733313 4678974813245468927049985)
  ·
    refine ⟨3509231109934101695287489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4678974813245468927049985 3509231109934101695287489)
    ·
      refine ⟨2631923332450576271465617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3509231109934101695287489 2631923332450576271465617)
      ·
        refine ⟨1973942499337932203599213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2631923332450576271465617 1973942499337932203599213)
        ·
          refine ⟨740228437251724576349705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1973942499337932203599213 740228437251724576349705)
          ·
            refine ⟨555171327938793432262279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 740228437251724576349705 555171327938793432262279)
            ·
              refine ⟨832756991908190148393419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 555171327938793432262279 832756991908190148393419)
              ·
                refine ⟨1249135487862285222590129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 832756991908190148393419 1249135487862285222590129)
                ·
                  refine ⟨936851615896713916942597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1249135487862285222590129 936851615896713916942597)
                  ·
                    refine ⟨175659677980633859426737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 936851615896713916942597 175659677980633859426737)
                    ·
                      refine ⟨131744758485475394570053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 175659677980633859426737 131744758485475394570053)
                      ·
                        rfl

theorem cell23_256572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 1, 1, 2, 4, 2].length) (baseStart_256572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_256572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_256572 prefixEnd_256572 := by exact prefixLift 256572
  have htrace : WordTrace (prefixWord ++ tailWord_256572) baseStart_256572 baseEnd_256572 := by
    simpa [prefixWord, tailWord_256572, baseEnd_256572] using wordTrace_append hprefix tailTrace_256572
  have hstable : (prefixWord ++ tailWord_256572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_256572).length < 2 ^ (prefixWord ++ tailWord_256572).sum := by decide
  have hdescent : baseEnd_256572 < baseStart_256572 := by decide
  rcases family_descends (prefixWord ++ tailWord_256572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_256589 : List Nat := [1, 6, 1, 1, 2, 3, 1, 1, 2, 1, 4]
def baseStart_256589 : Nat := 118140960795 + 256589 * 2 ^ 59
def prefixEnd_256589 : Nat := 4983230072969 + 3 ^ 40 * 256589 * 2
def baseEnd_256589 : Nat := 131753487656601828057475

theorem tailTrace_256589 : CollatzResearch.WordTrace tailWord_256589 prefixEnd_256589 131753487656601828057475 := by
  unfold tailWord_256589
  simp only [CollatzResearch.WordTrace]
  refine ⟨9358569667429349757468821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6239046444952899838312547 9358569667429349757468821)
  ·
    refine ⟨438682953160750769881351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 9358569667429349757468821 438682953160750769881351)
    ·
      refine ⟨658024429741126154822027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 438682953160750769881351 658024429741126154822027)
      ·
        refine ⟨987036644611689232233041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 658024429741126154822027 987036644611689232233041)
        ·
          refine ⟨740277483458766924174781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 987036644611689232233041 740277483458766924174781)
          ·
            refine ⟨277604056297037596565543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 740277483458766924174781 277604056297037596565543)
            ·
              refine ⟨416406084445556394848315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 277604056297037596565543 416406084445556394848315)
              ·
                refine ⟨624609126668334592272473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 416406084445556394848315 624609126668334592272473)
                ·
                  refine ⟨468456845001250944204355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 624609126668334592272473 468456845001250944204355)
                  ·
                    refine ⟨702685267501876416306533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 468456845001250944204355 702685267501876416306533)
                    ·
                      refine ⟨131753487656601828057475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 702685267501876416306533 131753487656601828057475)
                      ·
                        rfl

theorem cell23_256589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 3, 1, 1, 2, 1, 4].length) (baseStart_256589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_256589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_256589 prefixEnd_256589 := by exact prefixLift 256589
  have htrace : WordTrace (prefixWord ++ tailWord_256589) baseStart_256589 baseEnd_256589 := by
    simpa [prefixWord, tailWord_256589, baseEnd_256589] using wordTrace_append hprefix tailTrace_256589
  have hstable : (prefixWord ++ tailWord_256589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_256589).length < 2 ^ (prefixWord ++ tailWord_256589).sum := by decide
  have hdescent : baseEnd_256589 < baseStart_256589 := by decide
  rcases family_descends (prefixWord ++ tailWord_256589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_256629 : List Nat := [1, 3, 4, 2, 2, 1, 3, 1, 6]
def baseStart_256629 : Nat := 118140960795 + 256629 * 2 ^ 59
def prefixEnd_256629 : Nat := 4983230072969 + 3 ^ 40 * 256629 * 2
def baseEnd_256629 : Nat := 14641558542531296839699

theorem tailTrace_256629 : CollatzResearch.WordTrace tailWord_256629 prefixEnd_256629 14641558542531296839699 := by
  unfold tailWord_256629
  simp only [CollatzResearch.WordTrace]
  refine ⟨9360028587284436588924941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6240019058189624392616627 9360028587284436588924941)
  ·
    refine ⟨3510010720231663720846853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9360028587284436588924941 3510010720231663720846853)
    ·
      refine ⟨658127010043436947658785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3510010720231663720846853 658127010043436947658785)
      ·
        refine ⟨493595257532577710744089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 658127010043436947658785 493595257532577710744089)
        ·
          refine ⟨370196443149433283058067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 493595257532577710744089 370196443149433283058067)
          ·
            refine ⟨555294664724149924587101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 370196443149433283058067 555294664724149924587101)
            ·
              refine ⟨208235499271556221720163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 555294664724149924587101 208235499271556221720163)
              ·
                refine ⟨312353248907334332580245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 208235499271556221720163 312353248907334332580245)
                ·
                  refine ⟨14641558542531296839699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 312353248907334332580245 14641558542531296839699)
                  ·
                    rfl

theorem cell23_256629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 3, 1, 6].length) (baseStart_256629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_256629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_256629 prefixEnd_256629 := by exact prefixLift 256629
  have htrace : WordTrace (prefixWord ++ tailWord_256629) baseStart_256629 baseEnd_256629 := by
    simpa [prefixWord, tailWord_256629, baseEnd_256629] using wordTrace_append hprefix tailTrace_256629
  have hstable : (prefixWord ++ tailWord_256629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_256629).length < 2 ^ (prefixWord ++ tailWord_256629).sum := by decide
  have hdescent : baseEnd_256629 < baseStart_256629 := by decide
  rcases family_descends (prefixWord ++ tailWord_256629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_256665 : List Nat := [1, 2, 1, 2, 1, 2, 6, 1, 1, 1, 5]
def baseStart_256665 : Nat := 118140960795 + 256665 * 2 ^ 59
def prefixEnd_256665 : Nat := 4983230072969 + 3 ^ 40 * 256665 * 2
def baseEnd_256665 : Nat := 131792512186343530707125

theorem tailTrace_256665 : CollatzResearch.WordTrace tailWord_256665 prefixEnd_256665 131792512186343530707125 := by
  unfold tailWord_256665
  simp only [CollatzResearch.WordTrace]
  refine ⟨9361341615154014737235449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6240894410102676491490299 9361341615154014737235449)
  ·
    refine ⟨7021006211365511052926587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9361341615154014737235449 7021006211365511052926587)
    ·
      refine ⟨10531509317048266579389881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7021006211365511052926587 10531509317048266579389881)
      ·
        refine ⟨7898631987786199934542411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10531509317048266579389881 7898631987786199934542411)
        ·
          refine ⟨11847947981679299901813617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7898631987786199934542411 11847947981679299901813617)
          ·
            refine ⟨8885960986259474926360213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11847947981679299901813617 8885960986259474926360213)
            ·
              refine ⟨416529421230912887173135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 8885960986259474926360213 416529421230912887173135)
              ·
                refine ⟨624794131846369330759703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 416529421230912887173135 624794131846369330759703)
                ·
                  refine ⟨937191197769553996139555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 624794131846369330759703 937191197769553996139555)
                  ·
                    refine ⟨1405786796654330994209333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 937191197769553996139555 1405786796654330994209333)
                    ·
                      refine ⟨131792512186343530707125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1405786796654330994209333 131792512186343530707125)
                      ·
                        rfl

theorem cell23_256665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 6, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 6, 1, 1, 1, 5].length) (baseStart_256665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_256665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_256665 prefixEnd_256665 := by exact prefixLift 256665
  have htrace : WordTrace (prefixWord ++ tailWord_256665) baseStart_256665 baseEnd_256665 := by
    simpa [prefixWord, tailWord_256665, baseEnd_256665] using wordTrace_append hprefix tailTrace_256665
  have hstable : (prefixWord ++ tailWord_256665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_256665).length < 2 ^ (prefixWord ++ tailWord_256665).sum := by decide
  have hdescent : baseEnd_256665 < baseStart_256665 := by decide
  rcases family_descends (prefixWord ++ tailWord_256665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_256666 : List Nat := [3, 1, 1, 6, 1, 1, 1, 2, 2, 3, 2]
def baseStart_256666 : Nat := 118140960795 + 256666 * 2 ^ 59
def prefixEnd_256666 : Nat := 4983230072969 + 3 ^ 40 * 256666 * 2
def baseEnd_256666 : Nat := 131793025666998026794621

theorem tailTrace_256666 : CollatzResearch.WordTrace tailWord_256666 prefixEnd_256666 131793025666998026794621 := by
  unfold tailWord_256666
  simp only [CollatzResearch.WordTrace]
  refine ⟨2340344522037597977005463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6240918725433594605347901 2340344522037597977005463)
  ·
    refine ⟨3510516783056396965508195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2340344522037597977005463 3510516783056396965508195)
    ·
      refine ⟨5265775174584595448262293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3510516783056396965508195 5265775174584595448262293)
      ·
        refine ⟨246833211308652911637295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 5265775174584595448262293 246833211308652911637295)
        ·
          refine ⟨370249816962979367455943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246833211308652911637295 370249816962979367455943)
          ·
            refine ⟨555374725444469051183915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 370249816962979367455943 555374725444469051183915)
            ·
              refine ⟨833062088166703576775873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 555374725444469051183915 833062088166703576775873)
              ·
                refine ⟨624796566125027682581905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 833062088166703576775873 624796566125027682581905)
                ·
                  refine ⟨468597424593770761936429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 624796566125027682581905 468597424593770761936429)
                  ·
                    refine ⟨175724034222664035726161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 468597424593770761936429 175724034222664035726161)
                    ·
                      refine ⟨131793025666998026794621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 175724034222664035726161 131793025666998026794621)
                      ·
                        rfl

theorem cell23_256666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 1, 2, 2, 3, 2].length) (baseStart_256666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_256666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_256666 prefixEnd_256666 := by exact prefixLift 256666
  have htrace : WordTrace (prefixWord ++ tailWord_256666) baseStart_256666 baseEnd_256666 := by
    simpa [prefixWord, tailWord_256666, baseEnd_256666] using wordTrace_append hprefix tailTrace_256666
  have hstable : (prefixWord ++ tailWord_256666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_256666).length < 2 ^ (prefixWord ++ tailWord_256666).sum := by decide
  have hdescent : baseEnd_256666 < baseStart_256666 := by decide
  rcases family_descends (prefixWord ++ tailWord_256666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_256673 : List Nat := [1, 2, 3, 3, 3, 1, 3, 2, 1, 1, 3]
def baseStart_256673 : Nat := 118140960795 + 256673 * 2 ^ 59
def prefixEnd_256673 : Nat := 4983230072969 + 3 ^ 40 * 256673 * 2
def baseEnd_256673 : Nat := 131796620031579499407089

theorem tailTrace_256673 : CollatzResearch.WordTrace tailWord_256673 prefixEnd_256673 131796620031579499407089 := by
  unfold tailWord_256673
  simp only [CollatzResearch.WordTrace]
  refine ⟨9361633399125032103526673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6241088932750021402351115 9361633399125032103526673)
  ·
    refine ⟨7021225049343774077645005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9361633399125032103526673 7021225049343774077645005)
    ·
      refine ⟨2632959393503915279116877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7021225049343774077645005 2632959393503915279116877)
      ·
        refine ⟨987359772563968229668829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2632959393503915279116877 987359772563968229668829)
        ·
          refine ⟨370259914711488086125811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 987359772563968229668829 370259914711488086125811)
          ·
            refine ⟨555389872067232129188717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 370259914711488086125811 555389872067232129188717)
            ·
              refine ⟨208271202025212048445769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 555389872067232129188717 208271202025212048445769)
              ·
                refine ⟨156203401518909036334327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 208271202025212048445769 156203401518909036334327)
                ·
                  refine ⟨234305102278363554501491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 156203401518909036334327 234305102278363554501491)
                  ·
                    refine ⟨351457653417545331752237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 234305102278363554501491 351457653417545331752237)
                    ·
                      refine ⟨131796620031579499407089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 351457653417545331752237 131796620031579499407089)
                      ·
                        rfl

theorem cell23_256673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 3, 2, 1, 1, 3].length) (baseStart_256673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_256673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_256673 prefixEnd_256673 := by exact prefixLift 256673
  have htrace : WordTrace (prefixWord ++ tailWord_256673) baseStart_256673 baseEnd_256673 := by
    simpa [prefixWord, tailWord_256673, baseEnd_256673] using wordTrace_append hprefix tailTrace_256673
  have hstable : (prefixWord ++ tailWord_256673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_256673).length < 2 ^ (prefixWord ++ tailWord_256673).sum := by decide
  have hdescent : baseEnd_256673 < baseStart_256673 := by decide
  rcases family_descends (prefixWord ++ tailWord_256673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_256685 : List Nat := [1, 5, 2, 1, 1, 2, 1, 10]
def baseStart_256685 : Nat := 118140960795 + 256685 * 2 ^ 59
def prefixEnd_256685 : Nat := 4983230072969 + 3 ^ 40 * 256685 * 2
def baseEnd_256685 : Nat := 4881584511090127868779

theorem tailTrace_256685 : CollatzResearch.WordTrace tailWord_256685 prefixEnd_256685 4881584511090127868779 := by
  unfold tailWord_256685
  simp only [CollatzResearch.WordTrace]
  refine ⟨9362071075081558152963509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6241380716721038768642339 9362071075081558152963509)
  ·
    refine ⟨877694163288896076840329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9362071075081558152963509 877694163288896076840329)
    ·
      refine ⟨658270622466672057630247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 877694163288896076840329 658270622466672057630247)
      ·
        refine ⟨987405933700008086445371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 658270622466672057630247 987405933700008086445371)
        ·
          refine ⟨1481108900550012129668057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 987405933700008086445371 1481108900550012129668057)
          ·
            refine ⟨1110831675412509097251043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1481108900550012129668057 1110831675412509097251043)
            ·
              refine ⟨1666247513118763645876565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1110831675412509097251043 1666247513118763645876565)
              ·
                refine ⟨4881584511090127868779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 1666247513118763645876565 4881584511090127868779)
                ·
                  rfl

theorem cell23_256685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 10].length) (baseStart_256685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_256685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_256685 prefixEnd_256685 := by exact prefixLift 256685
  have htrace : WordTrace (prefixWord ++ tailWord_256685) baseStart_256685 baseEnd_256685 := by
    simpa [prefixWord, tailWord_256685, baseEnd_256685] using wordTrace_append hprefix tailTrace_256685
  have hstable : (prefixWord ++ tailWord_256685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_256685).length < 2 ^ (prefixWord ++ tailWord_256685).sum := by decide
  have hdescent : baseEnd_256685 < baseStart_256685 := by decide
  rcases family_descends (prefixWord ++ tailWord_256685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_256688 : List Nat := [2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 6]
def baseStart_256688 : Nat := 118140960795 + 256688 * 2 ^ 59
def prefixEnd_256688 : Nat := 4983230072969 + 3 ^ 40 * 256688 * 2
def baseEnd_256688 : Nat := 131804322241396940719519

theorem tailTrace_256688 : CollatzResearch.WordTrace tailWord_256688 prefixEnd_256688 131804322241396940719519 := by
  unfold tailWord_256688
  simp only [CollatzResearch.WordTrace]
  refine ⟨4681090247035344832661359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6241453662713793110215145 4681090247035344832661359)
  ·
    refine ⟨7021635370553017248992039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4681090247035344832661359 7021635370553017248992039)
    ·
      refine ⟨10532453055829525873488059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7021635370553017248992039 10532453055829525873488059)
      ·
        refine ⟨15798679583744288810232089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10532453055829525873488059 15798679583744288810232089)
        ·
          refine ⟨11849009687808216607674067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15798679583744288810232089 11849009687808216607674067)
          ·
            refine ⟨17773514531712324911511101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11849009687808216607674067 17773514531712324911511101)
            ·
              refine ⟨6665067949392121841816663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17773514531712324911511101 6665067949392121841816663)
              ·
                refine ⟨9997601924088182762724995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6665067949392121841816663 9997601924088182762724995)
                ·
                  refine ⟨14996402886132274144087493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9997601924088182762724995 14996402886132274144087493)
                  ·
                    refine ⟨2811825541149801402016405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14996402886132274144087493 2811825541149801402016405)
                    ·
                      refine ⟨131804322241396940719519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 2811825541149801402016405 131804322241396940719519)
                      ·
                        rfl

theorem cell23_256688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 6].length) (baseStart_256688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_256688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_256688 prefixEnd_256688 := by exact prefixLift 256688
  have htrace : WordTrace (prefixWord ++ tailWord_256688) baseStart_256688 baseEnd_256688 := by
    simpa [prefixWord, tailWord_256688, baseEnd_256688] using wordTrace_append hprefix tailTrace_256688
  have hstable : (prefixWord ++ tailWord_256688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_256688).length < 2 ^ (prefixWord ++ tailWord_256688).sum := by decide
  have hdescent : baseEnd_256688 < baseStart_256688 := by decide
  rcases family_descends (prefixWord ++ tailWord_256688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_256712 : List Nat := [2, 1, 3, 1, 2, 4, 1, 2, 1, 3, 3]
def baseStart_256712 : Nat := 118140960795 + 256712 * 2 ^ 59
def prefixEnd_256712 : Nat := 4983230072969 + 3 ^ 40 * 256712 * 2
def baseEnd_256712 : Nat := 131816645777104846819409

theorem tailTrace_256712 : CollatzResearch.WordTrace tailWord_256712 prefixEnd_256712 131816645777104846819409 := by
  unfold tailWord_256712
  simp only [CollatzResearch.WordTrace]
  refine ⟨4681527922991870882098195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6242037230655827842797593 4681527922991870882098195)
  ·
    refine ⟨7022291884487806323147293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4681527922991870882098195 7022291884487806323147293)
    ·
      refine ⟨2633359456682927371180235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7022291884487806323147293 2633359456682927371180235)
      ·
        refine ⟨3950039185024391056770353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2633359456682927371180235 3950039185024391056770353)
        ·
          refine ⟨2962529388768293292577765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3950039185024391056770353 2962529388768293292577765)
          ·
            refine ⟨555474260394054992358331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2962529388768293292577765 555474260394054992358331)
            ·
              refine ⟨833211390591082488537497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 555474260394054992358331 833211390591082488537497)
              ·
                refine ⟨624908542943311866403123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 833211390591082488537497 624908542943311866403123)
                ·
                  refine ⟨937362814414967799604685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 624908542943311866403123 937362814414967799604685)
                  ·
                    refine ⟨351511055405612924851757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 937362814414967799604685 351511055405612924851757)
                    ·
                      refine ⟨131816645777104846819409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 351511055405612924851757 131816645777104846819409)
                      ·
                        rfl

theorem cell23_256712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 1, 2, 1, 3, 3].length) (baseStart_256712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_256712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_256712 prefixEnd_256712 := by exact prefixLift 256712
  have htrace : WordTrace (prefixWord ++ tailWord_256712) baseStart_256712 baseEnd_256712 := by
    simpa [prefixWord, tailWord_256712, baseEnd_256712] using wordTrace_append hprefix tailTrace_256712
  have hstable : (prefixWord ++ tailWord_256712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_256712).length < 2 ^ (prefixWord ++ tailWord_256712).sum := by decide
  have hdescent : baseEnd_256712 < baseStart_256712 := by decide
  rcases family_descends (prefixWord ++ tailWord_256712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_256716 : List Nat := [2, 2, 1, 5, 1, 2, 3, 1, 1, 2, 3]
def baseStart_256716 : Nat := 118140960795 + 256716 * 2 ^ 59
def prefixEnd_256716 : Nat := 4983230072969 + 3 ^ 40 * 256716 * 2
def baseEnd_256716 : Nat := 131818699699722831169391

theorem tailTrace_256716 : CollatzResearch.WordTrace tailWord_256716 prefixEnd_256716 131818699699722831169391 := by
  unfold tailWord_256716
  simp only [CollatzResearch.WordTrace]
  refine ⟨4681600868984625223671001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6242134491979500298228001 4681600868984625223671001)
  ·
    refine ⟨3511200651738468917753251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4681600868984625223671001 3511200651738468917753251)
    ·
      refine ⟨5266800977607703376629877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3511200651738468917753251 5266800977607703376629877)
      ·
        refine ⟨493762591650722191559051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5266800977607703376629877 493762591650722191559051)
        ·
          refine ⟨740643887476083287338577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 493762591650722191559051 740643887476083287338577)
          ·
            refine ⟨555482915607062465503933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 740643887476083287338577 555482915607062465503933)
            ·
              refine ⟨208306093352648424563975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 555482915607062465503933 208306093352648424563975)
              ·
                refine ⟨312459140028972636845963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 208306093352648424563975 312459140028972636845963)
                ·
                  refine ⟨468688710043458955268945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 312459140028972636845963 468688710043458955268945)
                  ·
                    refine ⟨351516532532594216451709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 468688710043458955268945 351516532532594216451709)
                    ·
                      refine ⟨131818699699722831169391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 351516532532594216451709 131818699699722831169391)
                      ·
                        rfl

theorem cell23_256716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 3, 1, 1, 2, 3].length) (baseStart_256716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_256716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_256716 prefixEnd_256716 := by exact prefixLift 256716
  have htrace : WordTrace (prefixWord ++ tailWord_256716) baseStart_256716 baseEnd_256716 := by
    simpa [prefixWord, tailWord_256716, baseEnd_256716] using wordTrace_append hprefix tailTrace_256716
  have hstable : (prefixWord ++ tailWord_256716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_256716).length < 2 ^ (prefixWord ++ tailWord_256716).sum := by decide
  have hdescent : baseEnd_256716 < baseStart_256716 := by decide
  rcases family_descends (prefixWord ++ tailWord_256716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_256729 : List Nat := [1, 2, 1, 2, 3, 2, 4, 2, 2, 1, 3]
def baseStart_256729 : Nat := 118140960795 + 256729 * 2 ^ 59
def prefixEnd_256729 : Nat := 4983230072969 + 3 ^ 40 * 256729 * 2
def baseEnd_256729 : Nat := 131825374948231280306831

theorem tailTrace_256729 : CollatzResearch.WordTrace tailWord_256729 prefixEnd_256729 131825374948231280306831 := by
  unfold tailWord_256729
  simp only [CollatzResearch.WordTrace]
  refine ⟨9363675886922153667565241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6242450591281435778376827 9363675886922153667565241)
  ·
    refine ⟨7022756915191615250673931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9363675886922153667565241 7022756915191615250673931)
    ·
      refine ⟨10534135372787422876010897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7022756915191615250673931 10534135372787422876010897)
      ·
        refine ⟨7900601529590567157008173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10534135372787422876010897 7900601529590567157008173)
        ·
          refine ⟨2962725573596462683878065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7900601529590567157008173 2962725573596462683878065)
          ·
            refine ⟨2222044180197347012908549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2962725573596462683878065 2222044180197347012908549)
            ·
              refine ⟨416633283787002564920353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2222044180197347012908549 416633283787002564920353)
              ·
                refine ⟨312474962840251923690265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 416633283787002564920353 312474962840251923690265)
                ·
                  refine ⟨234356222130188942767699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 312474962840251923690265 234356222130188942767699)
                  ·
                    refine ⟨351534333195283414151549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 234356222130188942767699 351534333195283414151549)
                    ·
                      refine ⟨131825374948231280306831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 351534333195283414151549 131825374948231280306831)
                      ·
                        rfl

theorem cell23_256729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 4, 2, 2, 1, 3].length) (baseStart_256729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_256729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_256729 prefixEnd_256729 := by exact prefixLift 256729
  have htrace : WordTrace (prefixWord ++ tailWord_256729) baseStart_256729 baseEnd_256729 := by
    simpa [prefixWord, tailWord_256729, baseEnd_256729] using wordTrace_append hprefix tailTrace_256729
  have hstable : (prefixWord ++ tailWord_256729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_256729).length < 2 ^ (prefixWord ++ tailWord_256729).sum := by decide
  have hdescent : baseEnd_256729 < baseStart_256729 := by decide
  rcases family_descends (prefixWord ++ tailWord_256729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_256732 : List Nat := [2, 2, 5, 1, 1, 1, 1, 1, 2, 7]
def baseStart_256732 : Nat := 118140960795 + 256732 * 2 ^ 59
def prefixEnd_256732 : Nat := 4983230072969 + 3 ^ 40 * 256732 * 2
def baseEnd_256732 : Nat := 43942305130064922856439

theorem tailTrace_256732 : CollatzResearch.WordTrace tailWord_256732 prefixEnd_256732 43942305130064922856439 := by
  unfold tailWord_256732
  simp only [CollatzResearch.WordTrace]
  refine ⟨4681892652955642589962225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6242523537274190119949633 4681892652955642589962225)
  ·
    refine ⟨3511419489716731942471669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4681892652955642589962225 3511419489716731942471669)
    ·
      refine ⟨329195577160943619606719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3511419489716731942471669 329195577160943619606719)
      ·
        refine ⟨493793365741415429410079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 329195577160943619606719 493793365741415429410079)
        ·
          refine ⟨740690048612123144115119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 493793365741415429410079 740690048612123144115119)
          ·
            refine ⟨1111035072918184716172679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 740690048612123144115119 1111035072918184716172679)
            ·
              refine ⟨1666552609377277074259019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1111035072918184716172679 1666552609377277074259019)
              ·
                refine ⟨2499828914065915611388529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1666552609377277074259019 2499828914065915611388529)
                ·
                  refine ⟨1874871685549436708541397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2499828914065915611388529 1874871685549436708541397)
                  ·
                    refine ⟨43942305130064922856439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1874871685549436708541397 43942305130064922856439)
                    ·
                      rfl

theorem cell23_256732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 1, 2, 7].length) (baseStart_256732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_256732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_256732 prefixEnd_256732 := by exact prefixLift 256732
  have htrace : WordTrace (prefixWord ++ tailWord_256732) baseStart_256732 baseEnd_256732 := by
    simpa [prefixWord, tailWord_256732, baseEnd_256732] using wordTrace_append hprefix tailTrace_256732
  have hstable : (prefixWord ++ tailWord_256732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_256732).length < 2 ^ (prefixWord ++ tailWord_256732).sum := by decide
  have hdescent : baseEnd_256732 < baseStart_256732 := by decide
  rcases family_descends (prefixWord ++ tailWord_256732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_256735 : List Nat := [1, 1, 2, 3, 2, 3, 1, 1, 2, 3, 4]
def baseStart_256735 : Nat := 118140960795 + 256735 * 2 ^ 59
def prefixEnd_256735 : Nat := 4983230072969 + 3 ^ 40 * 256735 * 2
def baseEnd_256735 : Nat := 131828455832158256831803

theorem tailTrace_256735 : CollatzResearch.WordTrace tailWord_256735 prefixEnd_256735 131828455832158256831803 := by
  unfold tailWord_256735
  simp only [CollatzResearch.WordTrace]
  refine ⟨9363894724900416692283659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6242596483266944461522439 9363894724900416692283659)
  ·
    refine ⟨14045842087350625038425489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9363894724900416692283659 14045842087350625038425489)
    ·
      refine ⟨10534381565512968778819117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14045842087350625038425489 10534381565512968778819117)
      ·
        refine ⟨3950393087067363292057169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10534381565512968778819117 3950393087067363292057169)
        ·
          refine ⟨2962794815300522469042877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3950393087067363292057169 2962794815300522469042877)
          ·
            refine ⟨1111048055737695925891079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2962794815300522469042877 1111048055737695925891079)
            ·
              refine ⟨1666572083606543888836619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1111048055737695925891079 1666572083606543888836619)
              ·
                refine ⟨2499858125409815833254929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1666572083606543888836619 2499858125409815833254929)
                ·
                  refine ⟨1874893594057361874941197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2499858125409815833254929 1874893594057361874941197)
                  ·
                    refine ⟨703085097771510703102949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1874893594057361874941197 703085097771510703102949)
                    ·
                      refine ⟨131828455832158256831803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 703085097771510703102949 131828455832158256831803)
                      ·
                        rfl

theorem cell23_256735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 1, 2, 3, 4].length) (baseStart_256735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_256735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_256735 prefixEnd_256735 := by exact prefixLift 256735
  have htrace : WordTrace (prefixWord ++ tailWord_256735) baseStart_256735 baseEnd_256735 := by
    simpa [prefixWord, tailWord_256735, baseEnd_256735] using wordTrace_append hprefix tailTrace_256735
  have hstable : (prefixWord ++ tailWord_256735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_256735).length < 2 ^ (prefixWord ++ tailWord_256735).sum := by decide
  have hdescent : baseEnd_256735 < baseStart_256735 := by decide
  rcases family_descends (prefixWord ++ tailWord_256735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_256739 : List Nat := [1, 1, 1, 7, 1, 1, 1, 2, 3, 3, 2]
def baseStart_256739 : Nat := 118140960795 + 256739 * 2 ^ 59
def prefixEnd_256739 : Nat := 4983230072969 + 3 ^ 40 * 256739 * 2
def baseEnd_256739 : Nat := 131830509754776241181785

theorem tailTrace_256739 : CollatzResearch.WordTrace tailWord_256739 prefixEnd_256739 131830509754776241181785 := by
  unfold tailWord_256739
  simp only [CollatzResearch.WordTrace]
  refine ⟨9364040616885925375429271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6242693744590616916952847 9364040616885925375429271)
  ·
    refine ⟨14046060925328888063143907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9364040616885925375429271 14046060925328888063143907)
    ·
      refine ⟨21069091387993332094715861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14046060925328888063143907 21069091387993332094715861)
      ·
        refine ⟨493806829406093720969903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 21069091387993332094715861 493806829406093720969903)
        ·
          refine ⟨740710244109140581454855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 493806829406093720969903 740710244109140581454855)
          ·
            refine ⟨1111065366163710872182283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 740710244109140581454855 1111065366163710872182283)
            ·
              refine ⟨1666598049245566308273425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1111065366163710872182283 1666598049245566308273425)
              ·
                refine ⟨1249948536934174731205069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1666598049245566308273425 1249948536934174731205069)
                ·
                  refine ⟨468730701350315524201901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1249948536934174731205069 468730701350315524201901)
                  ·
                    refine ⟨175774013006368321575713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 468730701350315524201901 175774013006368321575713)
                    ·
                      refine ⟨131830509754776241181785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 175774013006368321575713 131830509754776241181785)
                      ·
                        rfl

theorem cell23_256739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 2, 3, 3, 2].length) (baseStart_256739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_256739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_256739 prefixEnd_256739 := by exact prefixLift 256739
  have htrace : WordTrace (prefixWord ++ tailWord_256739) baseStart_256739 baseEnd_256739 := by
    simpa [prefixWord, tailWord_256739, baseEnd_256739] using wordTrace_append hprefix tailTrace_256739
  have hstable : (prefixWord ++ tailWord_256739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_256739).length < 2 ^ (prefixWord ++ tailWord_256739).sum := by decide
  have hdescent : baseEnd_256739 < baseStart_256739 := by decide
  rcases family_descends (prefixWord ++ tailWord_256739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_256755 : List Nat := [1, 1, 1, 2, 2, 3, 1, 1, 4, 4, 3]
def baseStart_256755 : Nat := 118140960795 + 256755 * 2 ^ 59
def prefixEnd_256755 : Nat := 4983230072969 + 3 ^ 40 * 256755 * 2
def baseEnd_256755 : Nat := 131838725445248178581711

theorem tailTrace_256755 : CollatzResearch.WordTrace tailWord_256755 prefixEnd_256755 131838725445248178581711 := by
  unfold tailWord_256755
  simp only [CollatzResearch.WordTrace]
  refine ⟨9364624184827960108011719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6243082789885306738674479 9364624184827960108011719)
  ·
    refine ⟨14046936277241940162017579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9364624184827960108011719 14046936277241940162017579)
    ·
      refine ⟨21070404415862910243026369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14046936277241940162017579 21070404415862910243026369)
      ·
        refine ⟨15802803311897182682269777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21070404415862910243026369 15802803311897182682269777)
        ·
          refine ⟨11852102483922887011702333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15802803311897182682269777 11852102483922887011702333)
          ·
            refine ⟨4444538431471082629388375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11852102483922887011702333 4444538431471082629388375)
            ·
              refine ⟨6666807647206623944082563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4444538431471082629388375 6666807647206623944082563)
              ·
                refine ⟨10000211470809935916123845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6666807647206623944082563 10000211470809935916123845)
                ·
                  refine ⟨1875039650776862984273221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10000211470809935916123845 1875039650776862984273221)
                  ·
                    refine ⟨351569934520661809551229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1875039650776862984273221 351569934520661809551229)
                    ·
                      refine ⟨131838725445248178581711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 351569934520661809551229 131838725445248178581711)
                      ·
                        rfl

theorem cell23_256755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 1, 4, 4, 3].length) (baseStart_256755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_256755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_256755 prefixEnd_256755 := by exact prefixLift 256755
  have htrace : WordTrace (prefixWord ++ tailWord_256755) baseStart_256755 baseEnd_256755 := by
    simpa [prefixWord, tailWord_256755, baseEnd_256755] using wordTrace_append hprefix tailTrace_256755
  have hstable : (prefixWord ++ tailWord_256755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_256755).length < 2 ^ (prefixWord ++ tailWord_256755).sum := by decide
  have hdescent : baseEnd_256755 < baseStart_256755 := by decide
  rcases family_descends (prefixWord ++ tailWord_256755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_256765 : List Nat := [1, 4, 1, 1, 1, 1, 3, 2, 1, 4, 4]
def baseStart_256765 : Nat := 118140960795 + 256765 * 2 ^ 59
def prefixEnd_256765 : Nat := 4983230072969 + 3 ^ 40 * 256765 * 2
def baseEnd_256765 : Nat := 131843860251793139456665

theorem tailTrace_256765 : CollatzResearch.WordTrace tailWord_256765 prefixEnd_256765 131843860251793139456665 := by
  unfold tailWord_256765
  simp only [CollatzResearch.WordTrace]
  refine ⟨9364988914791731815875749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6243325943194487877250499 9364988914791731815875749)
  ·
    refine ⟨1755935421523449715476703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9364988914791731815875749 1755935421523449715476703)
    ·
      refine ⟨2633903132285174573215055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1755935421523449715476703 2633903132285174573215055)
      ·
        refine ⟨3950854698427761859822583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2633903132285174573215055 3950854698427761859822583)
        ·
          refine ⟨5926282047641642789733875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3950854698427761859822583 5926282047641642789733875)
          ·
            refine ⟨8889423071462464184600813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5926282047641642789733875 8889423071462464184600813)
            ·
              refine ⟨3333533651798424069225305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8889423071462464184600813 3333533651798424069225305)
              ·
                refine ⟨2500150238848818051918979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3333533651798424069225305 2500150238848818051918979)
                ·
                  refine ⟨3750225358273227077878469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2500150238848818051918979 3750225358273227077878469)
                  ·
                    refine ⟨703167254676230077102213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3750225358273227077878469 703167254676230077102213)
                    ·
                      refine ⟨131843860251793139456665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 703167254676230077102213 131843860251793139456665)
                      ·
                        rfl

theorem cell23_256765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 2, 1, 4, 4].length) (baseStart_256765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_256765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_256765 prefixEnd_256765 := by exact prefixLift 256765
  have htrace : WordTrace (prefixWord ++ tailWord_256765) baseStart_256765 baseEnd_256765 := by
    simpa [prefixWord, tailWord_256765, baseEnd_256765] using wordTrace_append hprefix tailTrace_256765
  have hstable : (prefixWord ++ tailWord_256765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_256765).length < 2 ^ (prefixWord ++ tailWord_256765).sum := by decide
  have hdescent : baseEnd_256765 < baseStart_256765 := by decide
  rcases family_descends (prefixWord ++ tailWord_256765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_256769 : List Nat := [1, 2, 4, 1, 1, 1, 1, 4, 4, 2, 2]
def baseStart_256769 : Nat := 118140960795 + 256769 * 2 ^ 59
def prefixEnd_256769 : Nat := 4983230072969 + 3 ^ 40 * 256769 * 2
def baseEnd_256769 : Nat := 131845914174411123806647

theorem tailTrace_256769 : CollatzResearch.WordTrace tailWord_256769 prefixEnd_256769 131845914174411123806647 := by
  unfold tailWord_256769
  simp only [CollatzResearch.WordTrace]
  refine ⟨9365134806777240499021361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6243423204518160332680907 9365134806777240499021361)
  ·
    refine ⟨7023851105082930374266021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9365134806777240499021361 7023851105082930374266021)
    ·
      refine ⟨1316972082203049445174879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7023851105082930374266021 1316972082203049445174879)
      ·
        refine ⟨1975458123304574167762319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1316972082203049445174879 1975458123304574167762319)
        ·
          refine ⟨2963187184956861251643479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1975458123304574167762319 2963187184956861251643479)
          ·
            refine ⟨4444780777435291877465219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2963187184956861251643479 4444780777435291877465219)
            ·
              refine ⟨6667171166152937816197829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4444780777435291877465219 6667171166152937816197829)
              ·
                refine ⟨1250094593653675840537093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6667171166152937816197829 1250094593653675840537093)
                ·
                  refine ⟨234392736310064220100705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1250094593653675840537093 234392736310064220100705)
                  ·
                    refine ⟨175794552232548165075529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 234392736310064220100705 175794552232548165075529)
                    ·
                      refine ⟨131845914174411123806647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 175794552232548165075529 131845914174411123806647)
                      ·
                        rfl

theorem cell23_256769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 4, 4, 2, 2].length) (baseStart_256769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_256769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_256769 prefixEnd_256769 := by exact prefixLift 256769
  have htrace : WordTrace (prefixWord ++ tailWord_256769) baseStart_256769 baseEnd_256769 := by
    simpa [prefixWord, tailWord_256769, baseEnd_256769] using wordTrace_append hprefix tailTrace_256769
  have hstable : (prefixWord ++ tailWord_256769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_256769).length < 2 ^ (prefixWord ++ tailWord_256769).sum := by decide
  have hdescent : baseEnd_256769 < baseStart_256769 := by decide
  rcases family_descends (prefixWord ++ tailWord_256769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_256805 : List Nat := [1, 3, 1, 2, 3, 1, 1, 1, 3, 7]
def baseStart_256805 : Nat := 118140960795 + 256805 * 2 ^ 59
def prefixEnd_256805 : Nat := 4983230072969 + 3 ^ 40 * 256805 * 2
def baseEnd_256805 : Nat := 43954799825990994318827

theorem tailTrace_256805 : CollatzResearch.WordTrace tailWord_256805 prefixEnd_256805 43954799825990994318827 := by
  unfold tailWord_256805
  simp only [CollatzResearch.WordTrace]
  refine ⟨9366447834646818647331869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6244298556431212431554579 9366447834646818647331869)
  ·
    refine ⟨3512417937992556992749451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9366447834646818647331869 3512417937992556992749451)
    ·
      refine ⟨5268626906988835489124177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3512417937992556992749451 5268626906988835489124177)
      ·
        refine ⟨3951470180241626616843133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5268626906988835489124177 3951470180241626616843133)
        ·
          refine ⟨1481801317590609981316175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3951470180241626616843133 1481801317590609981316175)
          ·
            refine ⟨2222701976385914971974263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1481801317590609981316175 2222701976385914971974263)
            ·
              refine ⟨3334052964578872457961395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2222701976385914971974263 3334052964578872457961395)
              ·
                refine ⟨5001079446868308686942093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3334052964578872457961395 5001079446868308686942093)
                ·
                  refine ⟨1875404792575615757603285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5001079446868308686942093 1875404792575615757603285)
                  ·
                    refine ⟨43954799825990994318827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1875404792575615757603285 43954799825990994318827)
                    ·
                      rfl

theorem cell23_256805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 1, 3, 7].length) (baseStart_256805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_256805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_256805 prefixEnd_256805 := by exact prefixLift 256805
  have htrace : WordTrace (prefixWord ++ tailWord_256805) baseStart_256805 baseEnd_256805 := by
    simpa [prefixWord, tailWord_256805, baseEnd_256805] using wordTrace_append hprefix tailTrace_256805
  have hstable : (prefixWord ++ tailWord_256805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_256805).length < 2 ^ (prefixWord ++ tailWord_256805).sum := by decide
  have hdescent : baseEnd_256805 < baseStart_256805 := by decide
  rcases family_descends (prefixWord ++ tailWord_256805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_256826 : List Nat := [3, 1, 1, 1, 6, 2, 1, 3, 5]
def baseStart_256826 : Nat := 118140960795 + 256826 * 2 ^ 59
def prefixEnd_256826 : Nat := 4983230072969 + 3 ^ 40 * 256826 * 2
def baseEnd_256826 : Nat := 14652798063524155643765

theorem tailTrace_256826 : CollatzResearch.WordTrace tailWord_256826 prefixEnd_256826 14652798063524155643765 := by
  unfold tailWord_256826
  simp only [CollatzResearch.WordTrace]
  refine ⟨2341803441892684808461583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6244809178380492822564221 2341803441892684808461583)
  ·
    refine ⟨3512705162839027212692375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2341803441892684808461583 3512705162839027212692375)
    ·
      refine ⟨5269057744258540819038563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3512705162839027212692375 5269057744258540819038563)
      ·
        refine ⟨7903586616387811228557845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5269057744258540819038563 7903586616387811228557845)
        ·
          refine ⟨370480622643178651338649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 7903586616387811228557845 370480622643178651338649)
          ·
            refine ⟨277860466982383988503987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 370480622643178651338649 277860466982383988503987)
            ·
              refine ⟨416790700473575982755981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 277860466982383988503987 416790700473575982755981)
              ·
                refine ⟨156296512677590993533493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 416790700473575982755981 156296512677590993533493)
                ·
                  refine ⟨14652798063524155643765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 156296512677590993533493 14652798063524155643765)
                  ·
                    rfl

theorem cell23_256826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 2, 1, 3, 5].length) (baseStart_256826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_256826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_256826 prefixEnd_256826 := by exact prefixLift 256826
  have htrace : WordTrace (prefixWord ++ tailWord_256826) baseStart_256826 baseEnd_256826 := by
    simpa [prefixWord, tailWord_256826, baseEnd_256826] using wordTrace_append hprefix tailTrace_256826
  have hstable : (prefixWord ++ tailWord_256826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_256826).length < 2 ^ (prefixWord ++ tailWord_256826).sum := by decide
  have hdescent : baseEnd_256826 < baseStart_256826 := by decide
  rcases family_descends (prefixWord ++ tailWord_256826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_256865 : List Nat := [1, 2, 3, 1, 1, 1, 2, 2, 10]
def baseStart_256865 : Nat := 118140960795 + 256865 * 2 ^ 59
def prefixEnd_256865 : Nat := 4983230072969 + 3 ^ 40 * 256865 * 2
def baseEnd_256865 : Nat := 14655023146360305356245

theorem tailTrace_256865 : CollatzResearch.WordTrace tailWord_256865 prefixEnd_256865 14655023146360305356245 := by
  unfold tailWord_256865
  simp only [CollatzResearch.WordTrace]
  refine ⟨9368636214429448894516049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6245757476286299263010699 9368636214429448894516049)
  ·
    refine ⟨7026477160822086670887037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9368636214429448894516049 7026477160822086670887037)
    ·
      refine ⟨2634928935308282501582639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7026477160822086670887037 2634928935308282501582639)
      ·
        refine ⟨3952393402962423752373959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2634928935308282501582639 3952393402962423752373959)
        ·
          refine ⟨5928590104443635628560939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3952393402962423752373959 5928590104443635628560939)
          ·
            refine ⟨8892885156665453442841409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5928590104443635628560939 8892885156665453442841409)
            ·
              refine ⟨6669663867499090082131057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8892885156665453442841409 6669663867499090082131057)
              ·
                refine ⟨5002247900624317561598293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6669663867499090082131057 5002247900624317561598293)
                ·
                  refine ⟨14655023146360305356245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 5002247900624317561598293 14655023146360305356245)
                  ·
                    rfl

theorem cell23_256865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 2, 10].length) (baseStart_256865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_256865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_256865 prefixEnd_256865 := by exact prefixLift 256865
  have htrace : WordTrace (prefixWord ++ tailWord_256865) baseStart_256865 baseEnd_256865 := by
    simpa [prefixWord, tailWord_256865, baseEnd_256865] using wordTrace_append hprefix tailTrace_256865
  have hstable : (prefixWord ++ tailWord_256865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_256865).length < 2 ^ (prefixWord ++ tailWord_256865).sum := by decide
  have hdescent : baseEnd_256865 < baseStart_256865 := by decide
  rcases family_descends (prefixWord ++ tailWord_256865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_256903 : List Nat := [1, 1, 4, 2, 3, 1, 4, 2, 1, 4]
def baseStart_256903 : Nat := 118140960795 + 256903 * 2 ^ 59
def prefixEnd_256903 : Nat := 4983230072969 + 3 ^ 40 * 256903 * 2
def baseEnd_256903 : Nat := 43971573527371199843677

theorem tailTrace_256903 : CollatzResearch.WordTrace tailWord_256903 prefixEnd_256903 43971573527371199843677 := by
  unfold tailWord_256903
  simp only [CollatzResearch.WordTrace]
  refine ⟨9370022188291781384399363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6246681458861187589599575 9370022188291781384399363)
  ·
    refine ⟨14055033282437672076599045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9370022188291781384399363 14055033282437672076599045)
    ·
      refine ⟨2635318740457063514362321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14055033282437672076599045 2635318740457063514362321)
      ·
        refine ⟨1976489055342797635771741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2635318740457063514362321 1976489055342797635771741)
        ·
          refine ⟨741183395753549113414403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1976489055342797635771741 741183395753549113414403)
          ·
            refine ⟨1111775093630323670121605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 741183395753549113414403 1111775093630323670121605)
            ·
              refine ⟨208457830055685688147801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1111775093630323670121605 208457830055685688147801)
              ·
                refine ⟨156343372541764266110851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 208457830055685688147801 156343372541764266110851)
                ·
                  refine ⟨234515058812646399166277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 156343372541764266110851 234515058812646399166277)
                  ·
                    refine ⟨43971573527371199843677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 234515058812646399166277 43971573527371199843677)
                    ·
                      rfl

theorem cell23_256903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 4, 2, 1, 4].length) (baseStart_256903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_256903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_256903 prefixEnd_256903 := by exact prefixLift 256903
  have htrace : WordTrace (prefixWord ++ tailWord_256903) baseStart_256903 baseEnd_256903 := by
    simpa [prefixWord, tailWord_256903, baseEnd_256903] using wordTrace_append hprefix tailTrace_256903
  have hstable : (prefixWord ++ tailWord_256903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_256903).length < 2 ^ (prefixWord ++ tailWord_256903).sum := by decide
  have hdescent : baseEnd_256903 < baseStart_256903 := by decide
  rcases family_descends (prefixWord ++ tailWord_256903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_256919 : List Nat := [1, 1, 3, 3, 1, 2, 2, 2, 1, 5, 2]
def baseStart_256919 : Nat := 118140960795 + 256919 * 2 ^ 59
def prefixEnd_256919 : Nat := 4983230072969 + 3 ^ 40 * 256919 * 2
def baseEnd_256919 : Nat := 131922936272585536930957

theorem tailTrace_256919 : CollatzResearch.WordTrace tailWord_256919 prefixEnd_256919 131922936272585536930957 := by
  unfold tailWord_256919
  simp only [CollatzResearch.WordTrace]
  refine ⟨9370605756233816116981811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6247070504155877411321207 9370605756233816116981811)
  ·
    refine ⟨14055908634350724175472717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9370605756233816116981811 14055908634350724175472717)
    ·
      refine ⟨5270965737881521565802269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14055908634350724175472717 5270965737881521565802269)
      ·
        refine ⟨1976612151705570587175851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5270965737881521565802269 1976612151705570587175851)
        ·
          refine ⟨2964918227558355880763777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1976612151705570587175851 2964918227558355880763777)
          ·
            refine ⟨2223688670668766910572833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2964918227558355880763777 2223688670668766910572833)
            ·
              refine ⟨1667766503001575182929625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2223688670668766910572833 1667766503001575182929625)
              ·
                refine ⟨1250824877251181387197219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1667766503001575182929625 1250824877251181387197219)
                ·
                  refine ⟨1876237315876772080795829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1250824877251181387197219 1876237315876772080795829)
                  ·
                    refine ⟨175897248363447382574609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1876237315876772080795829 175897248363447382574609)
                    ·
                      refine ⟨131922936272585536930957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 175897248363447382574609 131922936272585536930957)
                      ·
                        rfl

theorem cell23_256919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 2, 1, 5, 2].length) (baseStart_256919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_256919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_256919 prefixEnd_256919 := by exact prefixLift 256919
  have htrace : WordTrace (prefixWord ++ tailWord_256919) baseStart_256919 baseEnd_256919 := by
    simpa [prefixWord, tailWord_256919, baseEnd_256919] using wordTrace_append hprefix tailTrace_256919
  have hstable : (prefixWord ++ tailWord_256919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_256919).length < 2 ^ (prefixWord ++ tailWord_256919).sum := by decide
  have hdescent : baseEnd_256919 < baseStart_256919 := by decide
  rcases family_descends (prefixWord ++ tailWord_256919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_256929 : List Nat := [1, 2, 3, 4, 1, 1, 2, 1, 3, 5]
def baseStart_256929 : Nat := 118140960795 + 256929 * 2 ^ 59
def prefixEnd_256929 : Nat := 4983230072969 + 3 ^ 40 * 256929 * 2
def baseEnd_256929 : Nat := 43976023693043499268637

theorem tailTrace_256929 : CollatzResearch.WordTrace tailWord_256929 prefixEnd_256929 43976023693043499268637 := by
  unfold tailWord_256929
  simp only [CollatzResearch.WordTrace]
  refine ⟨9370970486197587824845841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6247313657465058549897227 9370970486197587824845841)
  ·
    refine ⟨7028227864648190868634381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9370970486197587824845841 7028227864648190868634381)
    ·
      refine ⟨2635585449243071575737893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7028227864648190868634381 2635585449243071575737893)
      ·
        refine ⟨494172271733075920450855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2635585449243071575737893 494172271733075920450855)
        ·
          refine ⟨741258407599613880676283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 494172271733075920450855 741258407599613880676283)
          ·
            refine ⟨1111887611399420821014425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 741258407599613880676283 1111887611399420821014425)
            ·
              refine ⟨833915708549565615760819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1111887611399420821014425 833915708549565615760819)
              ·
                refine ⟨1250873562824348423641229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 833915708549565615760819 1250873562824348423641229)
                ·
                  refine ⟨469077586059130658865461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1250873562824348423641229 469077586059130658865461)
                  ·
                    refine ⟨43976023693043499268637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 469077586059130658865461 43976023693043499268637)
                    ·
                      rfl

theorem cell23_256929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 2, 1, 3, 5].length) (baseStart_256929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_256929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_256929 prefixEnd_256929 := by exact prefixLift 256929
  have htrace : WordTrace (prefixWord ++ tailWord_256929) baseStart_256929 baseEnd_256929 := by
    simpa [prefixWord, tailWord_256929, baseEnd_256929] using wordTrace_append hprefix tailTrace_256929
  have hstable : (prefixWord ++ tailWord_256929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_256929).length < 2 ^ (prefixWord ++ tailWord_256929).sum := by decide
  have hdescent : baseEnd_256929 < baseStart_256929 := by decide
  rcases family_descends (prefixWord ++ tailWord_256929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_256959 : List Nat := [1, 1, 2, 2, 2, 1, 2, 6, 2, 4]
def baseStart_256959 : Nat := 118140960795 + 256959 * 2 ^ 59
def prefixEnd_256959 : Nat := 4983230072969 + 3 ^ 40 * 256959 * 2
def baseEnd_256959 : Nat := 43981158499588460143591

theorem tailTrace_256959 : CollatzResearch.WordTrace tailWord_256959 prefixEnd_256959 43981158499588460143591 := by
  unfold tailWord_256959
  simp only [CollatzResearch.WordTrace]
  refine ⟨9372064676088902948437931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6248043117392601965625287 9372064676088902948437931)
  ·
    refine ⟨14058097014133354422656897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9372064676088902948437931 14058097014133354422656897)
    ·
      refine ⟨10543572760600015816992673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14058097014133354422656897 10543572760600015816992673)
      ·
        refine ⟨7907679570450011862744505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10543572760600015816992673 7907679570450011862744505)
        ·
          refine ⟨5930759677837508897058379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7907679570450011862744505 5930759677837508897058379)
          ·
            refine ⟨8896139516756263345587569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5930759677837508897058379 8896139516756263345587569)
            ·
              refine ⟨6672104637567197509190677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8896139516756263345587569 6672104637567197509190677)
              ·
                refine ⟨312754904885962383243313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 6672104637567197509190677 312754904885962383243313)
                ·
                  refine ⟨234566178664471787432485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 312754904885962383243313 234566178664471787432485)
                  ·
                    refine ⟨43981158499588460143591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 234566178664471787432485 43981158499588460143591)
                    ·
                      rfl

theorem cell23_256959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 6, 2, 4].length) (baseStart_256959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_256959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_256959 prefixEnd_256959 := by exact prefixLift 256959
  have htrace : WordTrace (prefixWord ++ tailWord_256959) baseStart_256959 baseEnd_256959 := by
    simpa [prefixWord, tailWord_256959, baseEnd_256959] using wordTrace_append hprefix tailTrace_256959
  have hstable : (prefixWord ++ tailWord_256959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_256959).length < 2 ^ (prefixWord ++ tailWord_256959).sum := by decide
  have hdescent : baseEnd_256959 < baseStart_256959 := by decide
  rcases family_descends (prefixWord ++ tailWord_256959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_256972 : List Nat := [2, 2, 1, 4, 1, 1, 2, 10]
def baseStart_256972 : Nat := 118140960795 + 256972 * 2 ^ 59
def prefixEnd_256972 : Nat := 4983230072969 + 3 ^ 40 * 256972 * 2
def baseEnd_256972 : Nat := 4887042620269401095119

theorem tailTrace_256972 : CollatzResearch.WordTrace tailWord_256972 prefixEnd_256972 4887042620269401095119 := by
  unfold tailWord_256972
  simp only [CollatzResearch.WordTrace]
  refine ⟨4686269412520903084330585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6248359216694537445774113 4686269412520903084330585)
  ·
    refine ⟨3514702059390677313247939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4686269412520903084330585 3514702059390677313247939)
    ·
      refine ⟨5272053089086015969871909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3514702059390677313247939 5272053089086015969871909)
      ·
        refine ⟨988509954203627994350983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5272053089086015969871909 988509954203627994350983)
        ·
          refine ⟨1482764931305441991526475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 988509954203627994350983 1482764931305441991526475)
          ·
            refine ⟨2224147396958162987289713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1482764931305441991526475 2224147396958162987289713)
            ·
              refine ⟨1668110547718622240467285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2224147396958162987289713 1668110547718622240467285)
              ·
                refine ⟨4887042620269401095119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 1668110547718622240467285 4887042620269401095119)
                ·
                  rfl

theorem cell23_256972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 10].length) (baseStart_256972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_256972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_256972 prefixEnd_256972 := by exact prefixLift 256972
  have htrace : WordTrace (prefixWord ++ tailWord_256972) baseStart_256972 baseEnd_256972 := by
    simpa [prefixWord, tailWord_256972, baseEnd_256972] using wordTrace_append hprefix tailTrace_256972
  have hstable : (prefixWord ++ tailWord_256972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_256972).length < 2 ^ (prefixWord ++ tailWord_256972).sum := by decide
  have hdescent : baseEnd_256972 < baseStart_256972 := by decide
  rcases family_descends (prefixWord ++ tailWord_256972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_256986 : List Nat := [3, 1, 1, 2, 4, 1, 1, 4, 1, 2, 3]
def baseStart_256986 : Nat := 118140960795 + 256986 * 2 ^ 59
def prefixEnd_256986 : Nat := 4983230072969 + 3 ^ 40 * 256986 * 2
def baseEnd_256986 : Nat := 131957339476436774793149

theorem tailTrace_256986 : CollatzResearch.WordTrace tailWord_256986 prefixEnd_256986 131957339476436774793149 := by
  unfold tailWord_256986
  simp only [CollatzResearch.WordTrace]
  refine ⟨2343262361747771639917703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6248699631327391039780541 2343262361747771639917703)
  ·
    refine ⟨3514893542621657459876555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2343262361747771639917703 3514893542621657459876555)
    ·
      refine ⟨5272340313932486189814833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3514893542621657459876555 5272340313932486189814833)
      ·
        refine ⟨3954255235449364642361125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5272340313932486189814833 3954255235449364642361125)
        ·
          refine ⟨741422856646755870442711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3954255235449364642361125 741422856646755870442711)
          ·
            refine ⟨1112134284970133805664067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 741422856646755870442711 1112134284970133805664067)
            ·
              refine ⟨1668201427455200708496101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1112134284970133805664067 1668201427455200708496101)
              ·
                refine ⟨312787767647850132843019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1668201427455200708496101 312787767647850132843019)
                ·
                  refine ⟨469181651471775199264529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 312787767647850132843019 469181651471775199264529)
                  ·
                    refine ⟨351886238603831399448397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 469181651471775199264529 351886238603831399448397)
                    ·
                      refine ⟨131957339476436774793149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 351886238603831399448397 131957339476436774793149)
                      ·
                        rfl

theorem cell23_256986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 4, 1, 2, 3].length) (baseStart_256986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_256986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_256986 prefixEnd_256986 := by exact prefixLift 256986
  have htrace : WordTrace (prefixWord ++ tailWord_256986) baseStart_256986 baseEnd_256986 := by
    simpa [prefixWord, tailWord_256986, baseEnd_256986] using wordTrace_append hprefix tailTrace_256986
  have hstable : (prefixWord ++ tailWord_256986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_256986).length < 2 ^ (prefixWord ++ tailWord_256986).sum := by decide
  have hdescent : baseEnd_256986 < baseStart_256986 := by decide
  rcases family_descends (prefixWord ++ tailWord_256986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_256989 : List Nat := [1, 4, 3, 1, 2, 2, 1, 9]
def baseStart_256989 : Nat := 118140960795 + 256989 * 2 ^ 59
def prefixEnd_256989 : Nat := 4983230072969 + 3 ^ 40 * 256989 * 2
def baseEnd_256989 : Nat := 4887365922903713446505

theorem tailTrace_256989 : CollatzResearch.WordTrace tailWord_256989 prefixEnd_256989 4887365922903713446505 := by
  unfold tailWord_256989
  simp only [CollatzResearch.WordTrace]
  refine ⟨9373158865980218072030021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6248772577320145381353347 9373158865980218072030021)
  ·
    refine ⟨1757467287371290888505629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9373158865980218072030021 1757467287371290888505629)
    ·
      refine ⟨659050232764234083189611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1757467287371290888505629 659050232764234083189611)
      ·
        refine ⟨988575349146351124784417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 659050232764234083189611 988575349146351124784417)
        ·
          refine ⟨741431511859763343588313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 988575349146351124784417 741431511859763343588313)
          ·
            refine ⟨556073633894822507691235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 741431511859763343588313 556073633894822507691235)
            ·
              refine ⟨834110450842233761536853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 556073633894822507691235 834110450842233761536853)
              ·
                refine ⟨4887365922903713446505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 834110450842233761536853 4887365922903713446505)
                ·
                  rfl

theorem cell23_256989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 1, 9].length) (baseStart_256989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_256989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_256989 prefixEnd_256989 := by exact prefixLift 256989
  have htrace : WordTrace (prefixWord ++ tailWord_256989) baseStart_256989 baseEnd_256989 := by
    simpa [prefixWord, tailWord_256989, baseEnd_256989] using wordTrace_append hprefix tailTrace_256989
  have hstable : (prefixWord ++ tailWord_256989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_256989).length < 2 ^ (prefixWord ++ tailWord_256989).sum := by decide
  have hdescent : baseEnd_256989 < baseStart_256989 := by decide
  rcases family_descends (prefixWord ++ tailWord_256989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257000 : List Nat := [2, 1, 4, 1, 1, 1, 5, 3, 1, 2, 2]
def baseStart_257000 : Nat := 118140960795 + 257000 * 2 ^ 59
def prefixEnd_257000 : Nat := 4983230072969 + 3 ^ 40 * 257000 * 2
def baseEnd_257000 : Nat := 131964528205599720018085

theorem tailTrace_257000 : CollatzResearch.WordTrace tailWord_257000 prefixEnd_257000 131964528205599720018085 := by
  unfold tailWord_257000
  simp only [CollatzResearch.WordTrace]
  refine ⟨4686780034470183475340227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6249040045960244633786969 4686780034470183475340227)
  ·
    refine ⟨7030170051705275213010341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4686780034470183475340227 7030170051705275213010341)
    ·
      refine ⟨1318156884694739102439439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7030170051705275213010341 1318156884694739102439439)
      ·
        refine ⟨1977235327042108653659159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1318156884694739102439439 1977235327042108653659159)
        ·
          refine ⟨2965852990563162980488739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1977235327042108653659159 2965852990563162980488739)
          ·
            refine ⟨4448779485844744470733109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2965852990563162980488739 4448779485844744470733109)
            ·
              refine ⟨417073076797944794131229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4448779485844744470733109 417073076797944794131229)
              ·
                refine ⟨156402403799229297799211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 417073076797944794131229 156402403799229297799211)
                ·
                  refine ⟨234603605698843946698817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 156402403799229297799211 234603605698843946698817)
                  ·
                    refine ⟨175952704274132960024113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 234603605698843946698817 175952704274132960024113)
                    ·
                      refine ⟨131964528205599720018085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 175952704274132960024113 131964528205599720018085)
                      ·
                        rfl

theorem cell23_257000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 5, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 5, 3, 1, 2, 2].length) (baseStart_257000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_257000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_257000 prefixEnd_257000 := by exact prefixLift 257000
  have htrace : WordTrace (prefixWord ++ tailWord_257000) baseStart_257000 baseEnd_257000 := by
    simpa [prefixWord, tailWord_257000, baseEnd_257000] using wordTrace_append hprefix tailTrace_257000
  have hstable : (prefixWord ++ tailWord_257000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257000).length < 2 ^ (prefixWord ++ tailWord_257000).sum := by decide
  have hdescent : baseEnd_257000 < baseStart_257000 := by decide
  rcases family_descends (prefixWord ++ tailWord_257000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257006 : List Nat := [4, 1, 2, 1, 5, 1, 9]
def baseStart_257006 : Nat := 118140960795 + 257006 * 2 ^ 59
def prefixEnd_257006 : Nat := 4983230072969 + 3 ^ 40 * 257006 * 2
def baseEnd_257006 : Nat := 1629229741846008599297

theorem tailTrace_257006 : CollatzResearch.WordTrace tailWord_257006 prefixEnd_257006 1629229741846008599297 := by
  unfold tailWord_257006
  simp only [CollatzResearch.WordTrace]
  refine ⟨1171722363364828746924859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6249185937945753316932581 1171722363364828746924859)
  ·
    refine ⟨1757583545047243120387289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1171722363364828746924859 1757583545047243120387289)
    ·
      refine ⟨1318187658785432340290467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1757583545047243120387289 1318187658785432340290467)
      ·
        refine ⟨1977281488178148510435701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1318187658785432340290467 1977281488178148510435701)
        ·
          refine ⟨185370139516701422853347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1977281488178148510435701 185370139516701422853347)
          ·
            refine ⟨278055209275052134280021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 185370139516701422853347 278055209275052134280021)
            ·
              refine ⟨1629229741846008599297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 278055209275052134280021 1629229741846008599297)
              ·
                rfl

theorem cell23_257006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 1, 9].length) (baseStart_257006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_257006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_257006 prefixEnd_257006 := by exact prefixLift 257006
  have htrace : WordTrace (prefixWord ++ tailWord_257006) baseStart_257006 baseEnd_257006 := by
    simpa [prefixWord, tailWord_257006, baseEnd_257006] using wordTrace_append hprefix tailTrace_257006
  have hstable : (prefixWord ++ tailWord_257006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257006).length < 2 ^ (prefixWord ++ tailWord_257006).sum := by decide
  have hdescent : baseEnd_257006 < baseStart_257006 := by decide
  rcases family_descends (prefixWord ++ tailWord_257006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257016 : List Nat := [2, 1, 2, 1, 1, 3, 1, 6, 2, 1, 3]
def baseStart_257016 : Nat := 118140960795 + 257016 * 2 ^ 59
def prefixEnd_257016 : Nat := 4983230072969 + 3 ^ 40 * 257016 * 2
def baseEnd_257016 : Nat := 131972743896071657418011

theorem tailTrace_257016 : CollatzResearch.WordTrace tailWord_257016 prefixEnd_257016 131972743896071657418011 := by
  unfold tailWord_257016
  simp only [CollatzResearch.WordTrace]
  refine ⟨4687071818441200841631451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6249429091254934455508601 4687071818441200841631451)
  ·
    refine ⟨7030607727661801262447177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4687071818441200841631451 7030607727661801262447177)
    ·
      refine ⟨5272955795746350946835383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7030607727661801262447177 5272955795746350946835383)
      ·
        refine ⟨7909433693619526420253075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5272955795746350946835383 7909433693619526420253075)
        ·
          refine ⟨11864150540429289630379613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7909433693619526420253075 11864150540429289630379613)
          ·
            refine ⟨4449056452660983611392355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11864150540429289630379613 4449056452660983611392355)
            ·
              refine ⟨6673584678991475417088533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4449056452660983611392355 6673584678991475417088533)
              ·
                refine ⟨312824281827725410176025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 6673584678991475417088533 312824281827725410176025)
                ·
                  refine ⟨234618211370794057632019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 312824281827725410176025 234618211370794057632019)
                  ·
                    refine ⟨351927317056191086448029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 234618211370794057632019 351927317056191086448029)
                    ·
                      refine ⟨131972743896071657418011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 351927317056191086448029 131972743896071657418011)
                      ·
                        rfl

theorem cell23_257016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 6, 2, 1, 3].length) (baseStart_257016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_257016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_257016 prefixEnd_257016 := by exact prefixLift 257016
  have htrace : WordTrace (prefixWord ++ tailWord_257016) baseStart_257016 baseEnd_257016 := by
    simpa [prefixWord, tailWord_257016, baseEnd_257016] using wordTrace_append hprefix tailTrace_257016
  have hstable : (prefixWord ++ tailWord_257016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257016).length < 2 ^ (prefixWord ++ tailWord_257016).sum := by decide
  have hdescent : baseEnd_257016 < baseStart_257016 := by decide
  rcases family_descends (prefixWord ++ tailWord_257016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257059 : List Nat := [1, 1, 1, 4, 3, 2, 2, 1, 2, 1, 5]
def baseStart_257059 : Nat := 118140960795 + 257059 * 2 ^ 59
def prefixEnd_257059 : Nat := 4983230072969 + 3 ^ 40 * 257059 * 2
def baseEnd_257059 : Nat := 131994823564214989180313

theorem tailTrace_257059 : CollatzResearch.WordTrace tailWord_257059 prefixEnd_257059 131994823564214989180313 := by
  unfold tailWord_257059
  simp only [CollatzResearch.WordTrace]
  refine ⟨9375711975726620027078231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6250474650484413351385487 9375711975726620027078231)
  ·
    refine ⟨14063567963589930040617347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9375711975726620027078231 14063567963589930040617347)
    ·
      refine ⟨21095351945384895060926021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14063567963589930040617347 21095351945384895060926021)
      ·
        refine ⟨3955378489759667823923629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21095351945384895060926021 3955378489759667823923629)
        ·
          refine ⟨1483266933659875433971361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3955378489759667823923629 1483266933659875433971361)
          ·
            refine ⟨1112450200244906575478521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1483266933659875433971361 1112450200244906575478521)
            ·
              refine ⟨834337650183679931608891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1112450200244906575478521 834337650183679931608891)
              ·
                refine ⟨1251506475275519897413337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 834337650183679931608891 1251506475275519897413337)
                ·
                  refine ⟨938629856456639923060003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1251506475275519897413337 938629856456639923060003)
                  ·
                    refine ⟨1407944784684959884590005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 938629856456639923060003 1407944784684959884590005)
                    ·
                      refine ⟨131994823564214989180313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1407944784684959884590005 131994823564214989180313)
                      ·
                        rfl

theorem cell23_257059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 2, 1, 2, 1, 5].length) (baseStart_257059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_257059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_257059 prefixEnd_257059 := by exact prefixLift 257059
  have htrace : WordTrace (prefixWord ++ tailWord_257059) baseStart_257059 baseEnd_257059 := by
    simpa [prefixWord, tailWord_257059, baseEnd_257059] using wordTrace_append hprefix tailTrace_257059
  have hstable : (prefixWord ++ tailWord_257059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257059).length < 2 ^ (prefixWord ++ tailWord_257059).sum := by decide
  have hdescent : baseEnd_257059 < baseStart_257059 := by decide
  rcases family_descends (prefixWord ++ tailWord_257059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257086 : List Nat := [4, 2, 1, 3, 1, 1, 1, 1, 1, 4, 4]
def baseStart_257086 : Nat := 118140960795 + 257086 * 2 ^ 59
def prefixEnd_257086 : Nat := 4983230072969 + 3 ^ 40 * 257086 * 2
def baseEnd_257086 : Nat := 132008687541886383542689

theorem tailTrace_257086 : CollatzResearch.WordTrace tailWord_257086 prefixEnd_257086 132008687541886383542689 := by
  unfold tailWord_257086
  simp only [CollatzResearch.WordTrace]
  refine ⟨1172087093328600454788889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6251131164419202425540741 1172087093328600454788889)
  ·
    refine ⟨879065319996450341091667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1172087093328600454788889 879065319996450341091667)
    ·
      refine ⟨1318597979994675511637501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 879065319996450341091667 1318597979994675511637501)
      ·
        refine ⟨494474242498003316864063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1318597979994675511637501 494474242498003316864063)
        ·
          refine ⟨741711363747004975296095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 494474242498003316864063 741711363747004975296095)
          ·
            refine ⟨1112567045620507462944143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 741711363747004975296095 1112567045620507462944143)
            ·
              refine ⟨1668850568430761194416215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1112567045620507462944143 1668850568430761194416215)
              ·
                refine ⟨2503275852646141791624323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1668850568430761194416215 2503275852646141791624323)
                ·
                  refine ⟨3754913778969212687436485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2503275852646141791624323 3754913778969212687436485)
                  ·
                    refine ⟨704046333556727378894341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3754913778969212687436485 704046333556727378894341)
                    ·
                      refine ⟨132008687541886383542689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 704046333556727378894341 132008687541886383542689)
                      ·
                        rfl

theorem cell23_257086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 1, 1, 4, 4].length) (baseStart_257086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_257086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_257086 prefixEnd_257086 := by exact prefixLift 257086
  have htrace : WordTrace (prefixWord ++ tailWord_257086) baseStart_257086 baseEnd_257086 := by
    simpa [prefixWord, tailWord_257086, baseEnd_257086] using wordTrace_append hprefix tailTrace_257086
  have hstable : (prefixWord ++ tailWord_257086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257086).length < 2 ^ (prefixWord ++ tailWord_257086).sum := by decide
  have hdescent : baseEnd_257086 < baseStart_257086 := by decide
  rcases family_descends (prefixWord ++ tailWord_257086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257109 : List Nat := [1, 3, 2, 2, 1, 2, 3, 1, 1, 7]
def baseStart_257109 : Nat := 118140960795 + 257109 * 2 ^ 59
def prefixEnd_257109 : Nat := 4983230072969 + 3 ^ 40 * 257109 * 2
def baseEnd_257109 : Nat := 44006832532313264518361

theorem tailTrace_257109 : CollatzResearch.WordTrace tailWord_257109 prefixEnd_257109 44006832532313264518361 := by
  unfold tailWord_257109
  simp only [CollatzResearch.WordTrace]
  refine ⟨9377535625545478566398381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6251690417030319044265587 9377535625545478566398381)
  ·
    refine ⟨3516575859579554462399393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9377535625545478566398381 3516575859579554462399393)
    ·
      refine ⟨2637431894684665846799545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3516575859579554462399393 2637431894684665846799545)
      ·
        refine ⟨1978073921013499385099659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2637431894684665846799545 1978073921013499385099659)
        ·
          refine ⟨2967110881520249077649489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1978073921013499385099659 2967110881520249077649489)
          ·
            refine ⟨2225333161140186808237117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2967110881520249077649489 2225333161140186808237117)
            ·
              refine ⟨834499935427570053088919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2225333161140186808237117 834499935427570053088919)
              ·
                refine ⟨1251749903141355079633379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 834499935427570053088919 1251749903141355079633379)
                ·
                  refine ⟨1877624854712032619450069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1251749903141355079633379 1877624854712032619450069)
                  ·
                    refine ⟨44006832532313264518361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1877624854712032619450069 44006832532313264518361)
                    ·
                      rfl

theorem cell23_257109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 3, 1, 1, 7].length) (baseStart_257109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_257109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_257109 prefixEnd_257109 := by exact prefixLift 257109
  have htrace : WordTrace (prefixWord ++ tailWord_257109) baseStart_257109 baseEnd_257109 := by
    simpa [prefixWord, tailWord_257109, baseEnd_257109] using wordTrace_append hprefix tailTrace_257109
  have hstable : (prefixWord ++ tailWord_257109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257109).length < 2 ^ (prefixWord ++ tailWord_257109).sum := by decide
  have hdescent : baseEnd_257109 < baseStart_257109 := by decide
  rcases family_descends (prefixWord ++ tailWord_257109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257159 : List Nat := [1, 1, 4, 2, 1, 1, 1, 1, 1, 6, 4]
def baseStart_257159 : Nat := 118140960795 + 257159 * 2 ^ 59
def prefixEnd_257159 : Nat := 4983230072969 + 3 ^ 40 * 257159 * 2
def baseEnd_257159 : Nat := 132046171629664597929853

theorem tailTrace_257159 : CollatzResearch.WordTrace tailWord_257159 prefixEnd_257159 132046171629664597929853 := by
  unfold tailWord_257159
  simp only [CollatzResearch.WordTrace]
  refine ⟨9379359275364337105718531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6252906183576224737145687 9379359275364337105718531)
  ·
    refine ⟨14069038913046505658577797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9379359275364337105718531 14069038913046505658577797)
    ·
      refine ⟨2637944796196219810983337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14069038913046505658577797 2637944796196219810983337)
      ·
        refine ⟨1978458597147164858237503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2637944796196219810983337 1978458597147164858237503)
        ·
          refine ⟨2967687895720747287356255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1978458597147164858237503 2967687895720747287356255)
          ·
            refine ⟨4451531843581120931034383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2967687895720747287356255 4451531843581120931034383)
            ·
              refine ⟨6677297765371681396551575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4451531843581120931034383 6677297765371681396551575)
              ·
                refine ⟨10015946648057522094827363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6677297765371681396551575 10015946648057522094827363)
                ·
                  refine ⟨15023919972086283142241045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10015946648057522094827363 15023919972086283142241045)
                  ·
                    refine ⟨704246248691544522292549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15023919972086283142241045 704246248691544522292549)
                    ·
                      refine ⟨132046171629664597929853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 704246248691544522292549 132046171629664597929853)
                      ·
                        rfl

theorem cell23_257159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 1, 1, 6, 4].length) (baseStart_257159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_257159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_257159 prefixEnd_257159 := by exact prefixLift 257159
  have htrace : WordTrace (prefixWord ++ tailWord_257159) baseStart_257159 baseEnd_257159 := by
    simpa [prefixWord, tailWord_257159, baseEnd_257159] using wordTrace_append hprefix tailTrace_257159
  have hstable : (prefixWord ++ tailWord_257159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257159).length < 2 ^ (prefixWord ++ tailWord_257159).sum := by decide
  have hdescent : baseEnd_257159 < baseStart_257159 := by decide
  rcases family_descends (prefixWord ++ tailWord_257159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257173 : List Nat := [1, 3, 2, 1, 1, 1, 2, 7, 1, 4]
def baseStart_257173 : Nat := 118140960795 + 257173 * 2 ^ 59
def prefixEnd_257173 : Nat := 4983230072969 + 3 ^ 40 * 257173 * 2
def baseEnd_257173 : Nat := 44017786786275847718263

theorem tailTrace_257173 : CollatzResearch.WordTrace tailWord_257173 prefixEnd_257173 44017786786275847718263 := by
  unfold tailWord_257173
  simp only [CollatzResearch.WordTrace]
  refine ⟨9379869897313617496728173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6253246598209078331152115 9379869897313617496728173)
  ·
    refine ⟨3517451211492606561273065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9379869897313617496728173 3517451211492606561273065)
    ·
      refine ⟨2638088408619454920954799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3517451211492606561273065 2638088408619454920954799)
      ·
        refine ⟨3957132612929182381432199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2638088408619454920954799 3957132612929182381432199)
        ·
          refine ⟨5935698919393773572148299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3957132612929182381432199 5935698919393773572148299)
          ·
            refine ⟨8903548379090660358222449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5935698919393773572148299 8903548379090660358222449)
            ·
              refine ⟨6677661284317995268666837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8903548379090660358222449 6677661284317995268666837)
              ·
                refine ⟨156507686351203014109379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6677661284317995268666837 156507686351203014109379)
                ·
                  refine ⟨234761529526804521164069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 156507686351203014109379 234761529526804521164069)
                  ·
                    refine ⟨44017786786275847718263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 234761529526804521164069 44017786786275847718263)
                    ·
                      rfl

theorem cell23_257173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 7, 1, 4].length) (baseStart_257173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_257173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_257173 prefixEnd_257173 := by exact prefixLift 257173
  have htrace : WordTrace (prefixWord ++ tailWord_257173) baseStart_257173 baseEnd_257173 := by
    simpa [prefixWord, tailWord_257173, baseEnd_257173] using wordTrace_append hprefix tailTrace_257173
  have hstable : (prefixWord ++ tailWord_257173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257173).length < 2 ^ (prefixWord ++ tailWord_257173).sum := by decide
  have hdescent : baseEnd_257173 < baseStart_257173 := by decide
  rcases family_descends (prefixWord ++ tailWord_257173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257213 : List Nat := [1, 4, 1, 2, 1, 1, 2, 4, 3, 1, 3]
def baseStart_257213 : Nat := 118140960795 + 257213 * 2 ^ 59
def prefixEnd_257213 : Nat := 4983230072969 + 3 ^ 40 * 257213 * 2
def baseEnd_257213 : Nat := 132073899585007386654605

theorem tailTrace_257213 : CollatzResearch.WordTrace tailWord_257213 prefixEnd_257213 132073899585007386654605 := by
  unfold tailWord_257213
  simp only [CollatzResearch.WordTrace]
  refine ⟨9381328817168704328184293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6254219211445802885456195 9381328817168704328184293)
  ·
    refine ⟨1758999153219132061534555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9381328817168704328184293 1758999153219132061534555)
    ·
      refine ⟨2638498729828698092301833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1758999153219132061534555 2638498729828698092301833)
      ·
        refine ⟨1978874047371523569226375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2638498729828698092301833 1978874047371523569226375)
        ·
          refine ⟨2968311071057285353839563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1978874047371523569226375 2968311071057285353839563)
          ·
            refine ⟨4452466606585928030759345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2968311071057285353839563 4452466606585928030759345)
            ·
              refine ⟨3339349954939446023069509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4452466606585928030759345 3339349954939446023069509)
              ·
                refine ⟨626128116551146129325533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3339349954939446023069509 626128116551146129325533)
                ·
                  refine ⟨234798043706679798497075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 626128116551146129325533 234798043706679798497075)
                  ·
                    refine ⟨352197065560019697745613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 234798043706679798497075 352197065560019697745613)
                    ·
                      refine ⟨132073899585007386654605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 352197065560019697745613 132073899585007386654605)
                      ·
                        rfl

theorem cell23_257213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 4, 3, 1, 3].length) (baseStart_257213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_257213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_257213 prefixEnd_257213 := by exact prefixLift 257213
  have htrace : WordTrace (prefixWord ++ tailWord_257213) baseStart_257213 baseEnd_257213 := by
    simpa [prefixWord, tailWord_257213, baseEnd_257213] using wordTrace_append hprefix tailTrace_257213
  have hstable : (prefixWord ++ tailWord_257213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257213).length < 2 ^ (prefixWord ++ tailWord_257213).sum := by decide
  have hdescent : baseEnd_257213 < baseStart_257213 := by decide
  rcases family_descends (prefixWord ++ tailWord_257213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257247 : List Nat := [1, 1, 2, 3, 2, 1, 6, 2, 1, 1, 3]
def baseStart_257247 : Nat := 118140960795 + 257247 * 2 ^ 59
def prefixEnd_257247 : Nat := 4983230072969 + 3 ^ 40 * 257247 * 2
def baseEnd_257247 : Nat := 132091357927260253629449

theorem tailTrace_257247 : CollatzResearch.WordTrace tailWord_257247 prefixEnd_257247 132091357927260253629449 := by
  unfold tailWord_257247
  simp only [CollatzResearch.WordTrace]
  refine ⟨9382568899045528134921995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6255045932697018756614663 9382568899045528134921995)
  ·
    refine ⟨14073853348568292202382993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9382568899045528134921995 14073853348568292202382993)
    ·
      refine ⟨10555390011426219151787245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14073853348568292202382993 10555390011426219151787245)
      ·
        refine ⟨3958271254284832181920217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10555390011426219151787245 3958271254284832181920217)
        ·
          refine ⟨2968703440713624136440163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3958271254284832181920217 2968703440713624136440163)
          ·
            refine ⟨4453055161070436204660245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2968703440713624136440163 4453055161070436204660245)
            ·
              refine ⟨208736960675176697093449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 4453055161070436204660245 208736960675176697093449)
              ·
                refine ⟨156552720506382522820087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 208736960675176697093449 156552720506382522820087)
                ·
                  refine ⟨234829080759573784230131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 156552720506382522820087 234829080759573784230131)
                  ·
                    refine ⟨352243621139360676345197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 234829080759573784230131 352243621139360676345197)
                    ·
                      refine ⟨132091357927260253629449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 352243621139360676345197 132091357927260253629449)
                      ·
                        rfl

theorem cell23_257247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 6, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 6, 2, 1, 1, 3].length) (baseStart_257247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_257247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_257247 prefixEnd_257247 := by exact prefixLift 257247
  have htrace : WordTrace (prefixWord ++ tailWord_257247) baseStart_257247 baseEnd_257247 := by
    simpa [prefixWord, tailWord_257247, baseEnd_257247] using wordTrace_append hprefix tailTrace_257247
  have hstable : (prefixWord ++ tailWord_257247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257247).length < 2 ^ (prefixWord ++ tailWord_257247).sum := by decide
  have hdescent : baseEnd_257247 < baseStart_257247 := by decide
  rcases family_descends (prefixWord ++ tailWord_257247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257256 : List Nat := [2, 1, 4, 1, 2, 1, 2, 1, 3, 1, 5]
def baseStart_257256 : Nat := 118140960795 + 257256 * 2 ^ 59
def prefixEnd_257256 : Nat := 4983230072969 + 3 ^ 40 * 257256 * 2
def baseEnd_257256 : Nat := 132095979253150718416907

theorem tailTrace_257256 : CollatzResearch.WordTrace tailWord_257256 prefixEnd_257256 132095979253150718416907 := by
  unfold tailWord_257256
  simp only [CollatzResearch.WordTrace]
  refine ⟨4691448578006461335999811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6255264770675281781333081 4691448578006461335999811)
  ·
    refine ⟨7037172867009692003999717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4691448578006461335999811 7037172867009692003999717)
    ·
      refine ⟨1319469912564317250749947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7037172867009692003999717 1319469912564317250749947)
      ·
        refine ⟨1979204868846475876124921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1319469912564317250749947 1979204868846475876124921)
        ·
          refine ⟨1484403651634856907093691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1979204868846475876124921 1484403651634856907093691)
          ·
            refine ⟨2226605477452285360640537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1484403651634856907093691 2226605477452285360640537)
            ·
              refine ⟨1669954108089214020480403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2226605477452285360640537 1669954108089214020480403)
              ·
                refine ⟨2504931162133821030720605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1669954108089214020480403 2504931162133821030720605)
                ·
                  refine ⟨939349185800182886520227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2504931162133821030720605 939349185800182886520227)
                  ·
                    refine ⟨1409023778700274329780341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 939349185800182886520227 1409023778700274329780341)
                    ·
                      refine ⟨132095979253150718416907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1409023778700274329780341 132095979253150718416907)
                      ·
                        rfl

theorem cell23_257256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 1, 3, 1, 5].length) (baseStart_257256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_257256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_257256 prefixEnd_257256 := by exact prefixLift 257256
  have htrace : WordTrace (prefixWord ++ tailWord_257256) baseStart_257256 baseEnd_257256 := by
    simpa [prefixWord, tailWord_257256, baseEnd_257256] using wordTrace_append hprefix tailTrace_257256
  have hstable : (prefixWord ++ tailWord_257256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257256).length < 2 ^ (prefixWord ++ tailWord_257256).sum := by decide
  have hdescent : baseEnd_257256 < baseStart_257256 := by decide
  rcases family_descends (prefixWord ++ tailWord_257256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257263 : List Nat := [1, 1, 2, 1, 7, 1, 2, 1, 1, 6]
def baseStart_257263 : Nat := 118140960795 + 257263 * 2 ^ 59
def prefixEnd_257263 : Nat := 4983230072969 + 3 ^ 40 * 257263 * 2
def baseEnd_257263 : Nat := 44033191205910730343125

theorem tailTrace_257263 : CollatzResearch.WordTrace tailWord_257263 prefixEnd_257263 44033191205910730343125 := by
  unfold tailWord_257263
  simp only [CollatzResearch.WordTrace]
  refine ⟨9383152466987562867504443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6255434977991708578336295 9383152466987562867504443)
  ·
    refine ⟨14074728700481344301256665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9383152466987562867504443 14074728700481344301256665)
    ·
      refine ⟨10556046525361008225942499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14074728700481344301256665 10556046525361008225942499)
      ·
        refine ⟨15834069788041512338913749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10556046525361008225942499 15834069788041512338913749)
        ·
          refine ⟨371111010657222945443291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 15834069788041512338913749 371111010657222945443291)
          ·
            refine ⟨556666515985834418164937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 371111010657222945443291 556666515985834418164937)
            ·
              refine ⟨417499886989375813623703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 556666515985834418164937 417499886989375813623703)
              ·
                refine ⟨626249830484063720435555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 417499886989375813623703 626249830484063720435555)
                ·
                  refine ⟨939374745726095580653333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 626249830484063720435555 939374745726095580653333)
                  ·
                    refine ⟨44033191205910730343125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 939374745726095580653333 44033191205910730343125)
                    ·
                      rfl

theorem cell23_257263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 2, 1, 1, 6].length) (baseStart_257263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_257263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_257263 prefixEnd_257263 := by exact prefixLift 257263
  have htrace : WordTrace (prefixWord ++ tailWord_257263) baseStart_257263 baseEnd_257263 := by
    simpa [prefixWord, tailWord_257263, baseEnd_257263] using wordTrace_append hprefix tailTrace_257263
  have hstable : (prefixWord ++ tailWord_257263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257263).length < 2 ^ (prefixWord ++ tailWord_257263).sum := by decide
  have hdescent : baseEnd_257263 < baseStart_257263 := by decide
  rcases family_descends (prefixWord ++ tailWord_257263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257273 : List Nat := [1, 2, 1, 3, 1, 1, 4, 4, 1, 2, 3]
def baseStart_257273 : Nat := 118140960795 + 257273 * 2 ^ 59
def prefixEnd_257273 : Nat := 4983230072969 + 3 ^ 40 * 257273 * 2
def baseEnd_257273 : Nat := 132104708424277151904329

theorem tailTrace_257273 : CollatzResearch.WordTrace tailWord_257273 prefixEnd_257273 132104708424277151904329 := by
  unfold tailWord_257273
  simp only [CollatzResearch.WordTrace]
  refine ⟨9383517196951334575368473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6255678131300889716912315 9383517196951334575368473)
  ·
    refine ⟨7037637897713500931526355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9383517196951334575368473 7037637897713500931526355)
    ·
      refine ⟨10556456846570251397289533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7037637897713500931526355 10556456846570251397289533)
      ·
        refine ⟨3958671317463844273983575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10556456846570251397289533 3958671317463844273983575)
        ·
          refine ⟨5938006976195766410975363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3958671317463844273983575 5938006976195766410975363)
          ·
            refine ⟨8907010464293649616463045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5938006976195766410975363 8907010464293649616463045)
            ·
              refine ⟨1670064462055059303086821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8907010464293649616463045 1670064462055059303086821)
              ·
                refine ⟨313137086635323619328779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1670064462055059303086821 313137086635323619328779)
                ·
                  refine ⟨469705629952985428993169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 313137086635323619328779 469705629952985428993169)
                  ·
                    refine ⟨352279222464739071744877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 469705629952985428993169 352279222464739071744877)
                    ·
                      refine ⟨132104708424277151904329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 352279222464739071744877 132104708424277151904329)
                      ·
                        rfl

theorem cell23_257273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 4, 1, 2, 3].length) (baseStart_257273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_257273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_257273 prefixEnd_257273 := by exact prefixLift 257273
  have htrace : WordTrace (prefixWord ++ tailWord_257273) baseStart_257273 baseEnd_257273 := by
    simpa [prefixWord, tailWord_257273, baseEnd_257273] using wordTrace_append hprefix tailTrace_257273
  have hstable : (prefixWord ++ tailWord_257273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257273).length < 2 ^ (prefixWord ++ tailWord_257273).sum := by decide
  have hdescent : baseEnd_257273 < baseStart_257273 := by decide
  rcases family_descends (prefixWord ++ tailWord_257273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257320 : List Nat := [2, 1, 5, 1, 2, 1, 3, 1, 1, 3, 3]
def baseStart_257320 : Nat := 118140960795 + 257320 * 2 ^ 59
def prefixEnd_257320 : Nat := 4983230072969 + 3 ^ 40 * 257320 * 2
def baseEnd_257320 : Nat := 132128842015038468016613

theorem tailTrace_257320 : CollatzResearch.WordTrace tailWord_257320 prefixEnd_257320 132128842015038468016613 := by
  unfold tailWord_257320
  simp only [CollatzResearch.WordTrace]
  refine ⟨4692615713890530801164707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6256820951854041068219609 4692615713890530801164707)
  ·
    refine ⟨7038923570835796201747061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4692615713890530801164707 7038923570835796201747061)
    ·
      refine ⟨659899084765855893913787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7038923570835796201747061 659899084765855893913787)
      ·
        refine ⟨989848627148783840870681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 659899084765855893913787 989848627148783840870681)
        ·
          refine ⟨742386470361587880653011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 989848627148783840870681 742386470361587880653011)
          ·
            refine ⟨1113579705542381820979517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 742386470361587880653011 1113579705542381820979517)
            ·
              refine ⟨417592389578393182867319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1113579705542381820979517 417592389578393182867319)
              ·
                refine ⟨626388584367589774300979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 417592389578393182867319 626388584367589774300979)
                ·
                  refine ⟨939582876551384661451469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 626388584367589774300979 939582876551384661451469)
                  ·
                    refine ⟨352343578706769248044301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 939582876551384661451469 352343578706769248044301)
                    ·
                      refine ⟨132128842015038468016613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 352343578706769248044301 132128842015038468016613)
                      ·
                        rfl

theorem cell23_257320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 3, 1, 1, 3, 3].length) (baseStart_257320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_257320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_257320 prefixEnd_257320 := by exact prefixLift 257320
  have htrace : WordTrace (prefixWord ++ tailWord_257320) baseStart_257320 baseEnd_257320 := by
    simpa [prefixWord, tailWord_257320, baseEnd_257320] using wordTrace_append hprefix tailTrace_257320
  have hstable : (prefixWord ++ tailWord_257320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257320).length < 2 ^ (prefixWord ++ tailWord_257320).sum := by decide
  have hdescent : baseEnd_257320 < baseStart_257320 := by decide
  rcases family_descends (prefixWord ++ tailWord_257320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257360 : List Nat := [2, 1, 1, 1, 1, 5, 1, 3, 4, 2, 2]
def baseStart_257360 : Nat := 118140960795 + 257360 * 2 ^ 59
def prefixEnd_257360 : Nat := 4983230072969 + 3 ^ 40 * 257360 * 2
def baseEnd_257360 : Nat := 132149381241218311516429

theorem tailTrace_257360 : CollatzResearch.WordTrace tailWord_257360 prefixEnd_257360 132149381241218311516429 := by
  unfold tailWord_257360
  simp only [CollatzResearch.WordTrace]
  refine ⟨4693345173818074216892767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6257793565090765622523689 4693345173818074216892767)
  ·
    refine ⟨7040017760727111325339151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4693345173818074216892767 7040017760727111325339151)
    ·
      refine ⟨10560026641090666988008727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7040017760727111325339151 10560026641090666988008727)
      ·
        refine ⟨15840039961636000482013091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10560026641090666988008727 15840039961636000482013091)
        ·
          refine ⟨23760059942454000723019637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15840039961636000482013091 23760059942454000723019637)
          ·
            refine ⟨2227505619605062567783091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23760059942454000723019637 2227505619605062567783091)
            ·
              refine ⟨3341258429407593851674637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2227505619605062567783091 3341258429407593851674637)
              ·
                refine ⟨1252971911027847694377989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3341258429407593851674637 1252971911027847694377989)
                ·
                  refine ⟨234932233317721442695873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1252971911027847694377989 234932233317721442695873)
                  ·
                    refine ⟨176199174988291082021905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 234932233317721442695873 176199174988291082021905)
                    ·
                      refine ⟨132149381241218311516429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 176199174988291082021905 132149381241218311516429)
                      ·
                        rfl

theorem cell23_257360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 3, 4, 2, 2].length) (baseStart_257360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_257360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_257360 prefixEnd_257360 := by exact prefixLift 257360
  have htrace : WordTrace (prefixWord ++ tailWord_257360) baseStart_257360 baseEnd_257360 := by
    simpa [prefixWord, tailWord_257360, baseEnd_257360] using wordTrace_append hprefix tailTrace_257360
  have hstable : (prefixWord ++ tailWord_257360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257360).length < 2 ^ (prefixWord ++ tailWord_257360).sum := by decide
  have hdescent : baseEnd_257360 < baseStart_257360 := by decide
  rcases family_descends (prefixWord ++ tailWord_257360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257413 : List Nat := [1, 3, 1, 1, 3, 1, 4, 2, 2, 5]
def baseStart_257413 : Nat := 118140960795 + 257413 * 2 ^ 59
def prefixEnd_257413 : Nat := 4983230072969 + 3 ^ 40 * 257413 * 2
def baseEnd_257413 : Nat := 44058865238635534717895

theorem tailTrace_257413 : CollatzResearch.WordTrace tailWord_257413 prefixEnd_257413 44058865238635534717895 := by
  unfold tailWord_257413
  simp only [CollatzResearch.WordTrace]
  refine ⟨9388623416444138485464893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6259082277629425656976595 9388623416444138485464893)
  ·
    refine ⟨3520733781166551932049335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9388623416444138485464893 3520733781166551932049335)
    ·
      refine ⟨5281100671749827898074003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3520733781166551932049335 5281100671749827898074003)
      ·
        refine ⟨7921651007624741847111005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5281100671749827898074003 7921651007624741847111005)
        ·
          refine ⟨2970619127859278192666627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7921651007624741847111005 2970619127859278192666627)
          ·
            refine ⟨4455928691788917288999941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2970619127859278192666627 4455928691788917288999941)
            ·
              refine ⟨835486629710421991687489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4455928691788917288999941 835486629710421991687489)
              ·
                refine ⟨626614972282816493765617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 835486629710421991687489 626614972282816493765617)
                ·
                  refine ⟨469961229212112370324213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 626614972282816493765617 469961229212112370324213)
                  ·
                    refine ⟨44058865238635534717895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 469961229212112370324213 44058865238635534717895)
                    ·
                      rfl

theorem cell23_257413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 4, 2, 2, 5].length) (baseStart_257413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_257413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_257413 prefixEnd_257413 := by exact prefixLift 257413
  have htrace : WordTrace (prefixWord ++ tailWord_257413) baseStart_257413 baseEnd_257413 := by
    simpa [prefixWord, tailWord_257413, baseEnd_257413] using wordTrace_append hprefix tailTrace_257413
  have hstable : (prefixWord ++ tailWord_257413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257413).length < 2 ^ (prefixWord ++ tailWord_257413).sum := by decide
  have hdescent : baseEnd_257413 < baseStart_257413 := by decide
  rcases family_descends (prefixWord ++ tailWord_257413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257470 : List Nat := [4, 2, 1, 1, 1, 1, 1, 3, 4, 2, 3]
def baseStart_257470 : Nat := 118140960795 + 257470 * 2 ^ 59
def prefixEnd_257470 : Nat := 4983230072969 + 3 ^ 40 * 257470 * 2
def baseEnd_257470 : Nat := 132205864113212881140923

theorem tailTrace_257470 : CollatzResearch.WordTrace tailWord_257470 prefixEnd_257470 132205864113212881140923 := by
  unfold tailWord_257470
  simp only [CollatzResearch.WordTrace]
  refine ⟨1173837797154704652536233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6260468251491758146859909 1173837797154704652536233)
  ·
    refine ⟨880378347866028489402175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1173837797154704652536233 880378347866028489402175)
    ·
      refine ⟨1320567521799042734103263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 880378347866028489402175 1320567521799042734103263)
      ·
        refine ⟨1980851282698564101154895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1320567521799042734103263 1980851282698564101154895)
        ·
          refine ⟨2971276924047846151732343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1980851282698564101154895 2971276924047846151732343)
          ·
            refine ⟨4456915386071769227598515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2971276924047846151732343 4456915386071769227598515)
            ·
              refine ⟨6685373079107653841397773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4456915386071769227598515 6685373079107653841397773)
              ·
                refine ⟨2507014904665370190524165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6685373079107653841397773 2507014904665370190524165)
                ·
                  refine ⟨470065294624756910723281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2507014904665370190524165 470065294624756910723281)
                  ·
                    refine ⟨352548970968567683042461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 470065294624756910723281 352548970968567683042461)
                    ·
                      refine ⟨132205864113212881140923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 352548970968567683042461 132205864113212881140923)
                      ·
                        rfl

theorem cell23_257470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 3, 4, 2, 3].length) (baseStart_257470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_257470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_257470 prefixEnd_257470 := by exact prefixLift 257470
  have htrace : WordTrace (prefixWord ++ tailWord_257470) baseStart_257470 baseEnd_257470 := by
    simpa [prefixWord, tailWord_257470, baseEnd_257470] using wordTrace_append hprefix tailTrace_257470
  have hstable : (prefixWord ++ tailWord_257470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257470).length < 2 ^ (prefixWord ++ tailWord_257470).sum := by decide
  have hdescent : baseEnd_257470 < baseStart_257470 := by decide
  rcases family_descends (prefixWord ++ tailWord_257470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257493 : List Nat := [1, 3, 2, 3, 1, 1, 1, 2, 1, 2, 6]
def baseStart_257493 : Nat := 118140960795 + 257493 * 2 ^ 59
def prefixEnd_257493 : Nat := 4983230072969 + 3 ^ 40 * 257493 * 2
def baseEnd_257493 : Nat := 132217674168266291153317

theorem tailTrace_257493 : CollatzResearch.WordTrace tailWord_257493 prefixEnd_257493 132217674168266291153317 := by
  unfold tailWord_257493
  simp only [CollatzResearch.WordTrace]
  refine ⟨9391541256154312148377133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6261027504102874765584755 9391541256154312148377133)
  ·
    refine ⟨3521827971057867055641425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9391541256154312148377133 3521827971057867055641425)
    ·
      refine ⟨2641370978293400291731069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3521827971057867055641425 2641370978293400291731069)
      ·
        refine ⟨990514116860025109399151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2641370978293400291731069 990514116860025109399151)
        ·
          refine ⟨1485771175290037664098727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 990514116860025109399151 1485771175290037664098727)
          ·
            refine ⟨2228656762935056496148091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1485771175290037664098727 2228656762935056496148091)
            ·
              refine ⟨3342985144402584744222137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2228656762935056496148091 3342985144402584744222137)
              ·
                refine ⟨2507238858301938558166603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3342985144402584744222137 2507238858301938558166603)
                ·
                  refine ⟨3760858287452907837249905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2507238858301938558166603 3760858287452907837249905)
                  ·
                    refine ⟨2820643715589680877937429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3760858287452907837249905 2820643715589680877937429)
                    ·
                      refine ⟨132217674168266291153317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 2820643715589680877937429 132217674168266291153317)
                      ·
                        rfl

theorem cell23_257493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 2, 1, 2, 6].length) (baseStart_257493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_257493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_257493 prefixEnd_257493 := by exact prefixLift 257493
  have htrace : WordTrace (prefixWord ++ tailWord_257493) baseStart_257493 baseEnd_257493 := by
    simpa [prefixWord, tailWord_257493, baseEnd_257493] using wordTrace_append hprefix tailTrace_257493
  have hstable : (prefixWord ++ tailWord_257493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257493).length < 2 ^ (prefixWord ++ tailWord_257493).sum := by decide
  have hdescent : baseEnd_257493 < baseStart_257493 := by decide
  rcases family_descends (prefixWord ++ tailWord_257493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257520 : List Nat := [2, 1, 1, 1, 3, 4, 2, 3, 1, 5]
def baseStart_257520 : Nat := 118140960795 + 257520 * 2 ^ 59
def prefixEnd_257520 : Nat := 4983230072969 + 3 ^ 40 * 257520 * 2
def baseEnd_257520 : Nat := 44077179381979228505231

theorem tailTrace_257520 : CollatzResearch.WordTrace tailWord_257520 prefixEnd_257520 44077179381979228505231 := by
  unfold tailWord_257520
  simp only [CollatzResearch.WordTrace]
  refine ⟨4696263013528247879805007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6261684018037663839740009 4696263013528247879805007)
  ·
    refine ⟨7044394520292371819707511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4696263013528247879805007 7044394520292371819707511)
    ·
      refine ⟨10566591780438557729561267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7044394520292371819707511 10566591780438557729561267)
      ·
        refine ⟨15849887670657836594341901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10566591780438557729561267 15849887670657836594341901)
        ·
          refine ⟨5943707876496688722878213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15849887670657836594341901 5943707876496688722878213)
          ·
            refine ⟨1114445226843129135539665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5943707876496688722878213 1114445226843129135539665)
            ·
              refine ⟨835833920132346851654749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1114445226843129135539665 835833920132346851654749)
              ·
                refine ⟨313437720049630069370531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 835833920132346851654749 313437720049630069370531)
                ·
                  refine ⟨470156580074445104055797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 313437720049630069370531 470156580074445104055797)
                  ·
                    refine ⟨44077179381979228505231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 470156580074445104055797 44077179381979228505231)
                    ·
                      rfl

theorem cell23_257520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 2, 3, 1, 5].length) (baseStart_257520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_257520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_257520 prefixEnd_257520 := by exact prefixLift 257520
  have htrace : WordTrace (prefixWord ++ tailWord_257520) baseStart_257520 baseEnd_257520 := by
    simpa [prefixWord, tailWord_257520, baseEnd_257520] using wordTrace_append hprefix tailTrace_257520
  have hstable : (prefixWord ++ tailWord_257520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257520).length < 2 ^ (prefixWord ++ tailWord_257520).sum := by decide
  have hdescent : baseEnd_257520 < baseStart_257520 := by decide
  rcases family_descends (prefixWord ++ tailWord_257520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257553 : List Nat := [1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 6]
def baseStart_257553 : Nat := 118140960795 + 257553 * 2 ^ 59
def prefixEnd_257553 : Nat := 4983230072969 + 3 ^ 40 * 257553 * 2
def baseEnd_257553 : Nat := 132248483007536056403041

theorem tailTrace_257553 : CollatzResearch.WordTrace tailWord_257553 prefixEnd_257553 132248483007536056403041 := by
  unfold tailWord_257553
  simp only [CollatzResearch.WordTrace]
  refine ⟨9393729635936942395561313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6262486423957961597040875 9393729635936942395561313)
  ·
    refine ⟨7045297226952706796670985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9393729635936942395561313 7045297226952706796670985)
    ·
      refine ⟨5283972920214530097503239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7045297226952706796670985 5283972920214530097503239)
      ·
        refine ⟨7925959380321795146254859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5283972920214530097503239 7925959380321795146254859)
        ·
          refine ⟨11888939070482692719382289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7925959380321795146254859 11888939070482692719382289)
          ·
            refine ⟨8916704302862019539536717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11888939070482692719382289 8916704302862019539536717)
            ·
              refine ⟨3343764113573257327326269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8916704302862019539536717 3343764113573257327326269)
              ·
                refine ⟨1253911542589971497747351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3343764113573257327326269 1253911542589971497747351)
                ·
                  refine ⟨1880867313884957246621027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1253911542589971497747351 1880867313884957246621027)
                  ·
                    refine ⟨2821300970827435869931541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1880867313884957246621027 2821300970827435869931541)
                    ·
                      refine ⟨132248483007536056403041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 2821300970827435869931541 132248483007536056403041)
                      ·
                        rfl

theorem cell23_257553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 6].length) (baseStart_257553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_257553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_257553 prefixEnd_257553 := by exact prefixLift 257553
  have htrace : WordTrace (prefixWord ++ tailWord_257553) baseStart_257553 baseEnd_257553 := by
    simpa [prefixWord, tailWord_257553, baseEnd_257553] using wordTrace_append hprefix tailTrace_257553
  have hstable : (prefixWord ++ tailWord_257553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257553).length < 2 ^ (prefixWord ++ tailWord_257553).sum := by decide
  have hdescent : baseEnd_257553 < baseStart_257553 := by decide
  rcases family_descends (prefixWord ++ tailWord_257553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257557 : List Nat := [1, 3, 2, 1, 3, 2, 3, 2, 1, 1, 4]
def baseStart_257557 : Nat := 118140960795 + 257557 * 2 ^ 59
def prefixEnd_257557 : Nat := 4983230072969 + 3 ^ 40 * 257557 * 2
def baseEnd_257557 : Nat := 132250536930154040753023

theorem tailTrace_257557 : CollatzResearch.WordTrace tailWord_257557 prefixEnd_257557 132250536930154040753023 := by
  unfold tailWord_257557
  simp only [CollatzResearch.WordTrace]
  refine ⟨9393875527922451078706925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6262583685281634052471283 9393875527922451078706925)
  ·
    refine ⟨3522703322970919154515097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9393875527922451078706925 3522703322970919154515097)
    ·
      refine ⟨2642027492228189365886323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3522703322970919154515097 2642027492228189365886323)
      ·
        refine ⟨3963041238342284048829485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2642027492228189365886323 3963041238342284048829485)
        ·
          refine ⟨1486140464378356518311057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3963041238342284048829485 1486140464378356518311057)
          ·
            refine ⟨1114605348283767388733293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1486140464378356518311057 1114605348283767388733293)
            ·
              refine ⟨417977005606412770774985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1114605348283767388733293 417977005606412770774985)
              ·
                refine ⟨313482754204809578081239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 417977005606412770774985 313482754204809578081239)
                ·
                  refine ⟨470224131307214367121859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 313482754204809578081239 470224131307214367121859)
                  ·
                    refine ⟨705336196960821550682789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 470224131307214367121859 705336196960821550682789)
                    ·
                      refine ⟨132250536930154040753023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 705336196960821550682789 132250536930154040753023)
                      ·
                        rfl

theorem cell23_257557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 3, 2, 1, 1, 4].length) (baseStart_257557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_257557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_257557 prefixEnd_257557 := by exact prefixLift 257557
  have htrace : WordTrace (prefixWord ++ tailWord_257557) baseStart_257557 baseEnd_257557 := by
    simpa [prefixWord, tailWord_257557, baseEnd_257557] using wordTrace_append hprefix tailTrace_257557
  have hstable : (prefixWord ++ tailWord_257557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257557).length < 2 ^ (prefixWord ++ tailWord_257557).sum := by decide
  have hdescent : baseEnd_257557 < baseStart_257557 := by decide
  rcases family_descends (prefixWord ++ tailWord_257557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257570 : List Nat := [3, 3, 1, 1, 1, 1, 3, 1, 3, 2, 4]
def baseStart_257570 : Nat := 118140960795 + 257570 * 2 ^ 59
def prefixEnd_257570 : Nat := 4983230072969 + 3 ^ 40 * 257570 * 2
def baseEnd_257570 : Nat := 132257212178662489890463

theorem tailTrace_257570 : CollatzResearch.WordTrace tailWord_257570 prefixEnd_257570 132257212178662489890463 := by
  unfold tailWord_257570
  simp only [CollatzResearch.WordTrace]
  refine ⟨2348587419218838574732541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6262899784583569532620109 2348587419218838574732541)
  ·
    refine ⟨880720282207064465524703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2348587419218838574732541 880720282207064465524703)
    ·
      refine ⟨1321080423310596698287055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 880720282207064465524703 1321080423310596698287055)
      ·
        refine ⟨1981620634965895047430583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1321080423310596698287055 1981620634965895047430583)
        ·
          refine ⟨2972430952448842571145875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1981620634965895047430583 2972430952448842571145875)
          ·
            refine ⟨4458646428673263856718813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2972430952448842571145875 4458646428673263856718813)
            ·
              refine ⟨1671992410752473946269555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4458646428673263856718813 1671992410752473946269555)
              ·
                refine ⟨2507988616128710919404333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1671992410752473946269555 2507988616128710919404333)
                ·
                  refine ⟨940495731048266594776625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2507988616128710919404333 940495731048266594776625)
                  ·
                    refine ⟨705371798286199946082469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 940495731048266594776625 705371798286199946082469)
                    ·
                      refine ⟨132257212178662489890463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 705371798286199946082469 132257212178662489890463)
                      ·
                        rfl

theorem cell23_257570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 1, 3, 2, 4].length) (baseStart_257570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_257570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_257570 prefixEnd_257570 := by exact prefixLift 257570
  have htrace : WordTrace (prefixWord ++ tailWord_257570) baseStart_257570 baseEnd_257570 := by
    simpa [prefixWord, tailWord_257570, baseEnd_257570] using wordTrace_append hprefix tailTrace_257570
  have hstable : (prefixWord ++ tailWord_257570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257570).length < 2 ^ (prefixWord ++ tailWord_257570).sum := by decide
  have hdescent : baseEnd_257570 < baseStart_257570 := by decide
  rcases family_descends (prefixWord ++ tailWord_257570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257591 : List Nat := [1, 1, 3, 1, 2, 5, 1, 4, 1, 2, 2]
def baseStart_257591 : Nat := 118140960795 + 257591 * 2 ^ 59
def prefixEnd_257591 : Nat := 4983230072969 + 3 ^ 40 * 257591 * 2
def baseEnd_257591 : Nat := 132267995272406907727867

theorem tailTrace_257591 : CollatzResearch.WordTrace tailWord_257591 prefixEnd_257591 132267995272406907727867 := by
  unfold tailWord_257591
  simp only [CollatzResearch.WordTrace]
  refine ⟨9395115609799274885444627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6263410406532849923629751 9395115609799274885444627)
  ·
    refine ⟨14092673414698912328166941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9395115609799274885444627 14092673414698912328166941)
    ·
      refine ⟨5284752530512092123062603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14092673414698912328166941 5284752530512092123062603)
      ·
        refine ⟨7927128795768138184593905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5284752530512092123062603 7927128795768138184593905)
        ·
          refine ⟨5945346596826103638445429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7927128795768138184593905 5945346596826103638445429)
          ·
            refine ⟨557376243452447216104259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5945346596826103638445429 557376243452447216104259)
            ·
              refine ⟨836064365178670824156389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 557376243452447216104259 836064365178670824156389)
              ·
                refine ⟨156762068471000779529323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 836064365178670824156389 156762068471000779529323)
                ·
                  refine ⟨235143102706501169293985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 156762068471000779529323 235143102706501169293985)
                  ·
                    refine ⟨176357327029875876970489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 235143102706501169293985 176357327029875876970489)
                    ·
                      refine ⟨132267995272406907727867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 176357327029875876970489 132267995272406907727867)
                      ·
                        rfl

theorem cell23_257591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 1, 4, 1, 2, 2].length) (baseStart_257591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_257591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_257591 prefixEnd_257591 := by exact prefixLift 257591
  have htrace : WordTrace (prefixWord ++ tailWord_257591) baseStart_257591 baseEnd_257591 := by
    simpa [prefixWord, tailWord_257591, baseEnd_257591] using wordTrace_append hprefix tailTrace_257591
  have hstable : (prefixWord ++ tailWord_257591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257591).length < 2 ^ (prefixWord ++ tailWord_257591).sum := by decide
  have hdescent : baseEnd_257591 < baseStart_257591 := by decide
  rcases family_descends (prefixWord ++ tailWord_257591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257597 : List Nat := [1, 4, 1, 3, 3, 2, 1, 8]
def baseStart_257597 : Nat := 118140960795 + 257597 * 2 ^ 59
def prefixEnd_257597 : Nat := 4983230072969 + 3 ^ 40 * 257597 * 2
def baseEnd_257597 : Nat := 4898928746530884601957

theorem tailTrace_257597 : CollatzResearch.WordTrace tailWord_257597 prefixEnd_257597 4898928746530884601957 := by
  unfold tailWord_257597
  simp only [CollatzResearch.WordTrace]
  refine ⟨9395334447777537910163045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6263556298518358606775363 9395334447777537910163045)
  ·
    refine ⟨1761625208958288358155571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9395334447777537910163045 1761625208958288358155571)
    ·
      refine ⟨2642437813437432537233357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1761625208958288358155571 2642437813437432537233357)
      ·
        refine ⟨990914180039037201462509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2642437813437432537233357 990914180039037201462509)
        ·
          refine ⟨371592817514638950548441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 990914180039037201462509 371592817514638950548441)
          ·
            refine ⟨278694613135979212911331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 371592817514638950548441 278694613135979212911331)
            ·
              refine ⟨418041919703968819366997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 278694613135979212911331 418041919703968819366997)
              ·
                refine ⟨4898928746530884601957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 418041919703968819366997 4898928746530884601957)
                ·
                  rfl

theorem cell23_257597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 2, 1, 8].length) (baseStart_257597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_257597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_257597 prefixEnd_257597 := by exact prefixLift 257597
  have htrace : WordTrace (prefixWord ++ tailWord_257597) baseStart_257597 baseEnd_257597 := by
    simpa [prefixWord, tailWord_257597, baseEnd_257597] using wordTrace_append hprefix tailTrace_257597
  have hstable : (prefixWord ++ tailWord_257597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257597).length < 2 ^ (prefixWord ++ tailWord_257597).sum := by decide
  have hdescent : baseEnd_257597 < baseStart_257597 := by decide
  rcases family_descends (prefixWord ++ tailWord_257597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257603 : List Nat := [1, 1, 1, 3, 1, 2, 1, 1, 3, 4, 5]
def baseStart_257603 : Nat := 118140960795 + 257603 * 2 ^ 59
def prefixEnd_257603 : Nat := 4983230072969 + 3 ^ 40 * 257603 * 2
def baseEnd_257603 : Nat := 132274157040260860777811

theorem tailTrace_257603 : CollatzResearch.WordTrace tailWord_257603 prefixEnd_257603 132274157040260860777811 := by
  unfold tailWord_257603
  simp only [CollatzResearch.WordTrace]
  refine ⟨9395553285755800934881463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6263702190503867289920975 9395553285755800934881463)
  ·
    refine ⟨14093329928633701402322195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9395553285755800934881463 14093329928633701402322195)
    ·
      refine ⟨21139994892950552103483293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14093329928633701402322195 21139994892950552103483293)
      ·
        refine ⟨7927498084856457038806235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21139994892950552103483293 7927498084856457038806235)
        ·
          refine ⟨11891247127284685558209353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7927498084856457038806235 11891247127284685558209353)
          ·
            refine ⟨8918435345463514168657015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11891247127284685558209353 8918435345463514168657015)
            ·
              refine ⟨13377653018195271252985523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8918435345463514168657015 13377653018195271252985523)
              ·
                refine ⟨20066479527292906879478285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13377653018195271252985523 20066479527292906879478285)
                ·
                  refine ⟨7524929822734840079804357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20066479527292906879478285 7524929822734840079804357)
                  ·
                    refine ⟨1410924341762782514963317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7524929822734840079804357 1410924341762782514963317)
                    ·
                      refine ⟨132274157040260860777811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1410924341762782514963317 132274157040260860777811)
                      ·
                        rfl

theorem cell23_257603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 3, 4, 5].length) (baseStart_257603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_257603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_257603 prefixEnd_257603 := by exact prefixLift 257603
  have htrace : WordTrace (prefixWord ++ tailWord_257603) baseStart_257603 baseEnd_257603 := by
    simpa [prefixWord, tailWord_257603, baseEnd_257603] using wordTrace_append hprefix tailTrace_257603
  have hstable : (prefixWord ++ tailWord_257603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257603).length < 2 ^ (prefixWord ++ tailWord_257603).sum := by decide
  have hdescent : baseEnd_257603 < baseStart_257603 := by decide
  rcases family_descends (prefixWord ++ tailWord_257603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257617 : List Nat := [1, 2, 2, 1, 3, 2, 1, 3, 3, 3, 2]
def baseStart_257617 : Nat := 118140960795 + 257617 * 2 ^ 59
def prefixEnd_257617 : Nat := 4983230072969 + 3 ^ 40 * 257617 * 2
def baseEnd_257617 : Nat := 132281345769423806002747

theorem tailTrace_257617 : CollatzResearch.WordTrace tailWord_257617 prefixEnd_257617 132281345769423806002747 := by
  unfold tailWord_257617
  simp only [CollatzResearch.WordTrace]
  refine ⟨9396063907705081325891105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6264042605136720883927403 9396063907705081325891105)
  ·
    refine ⟨7047047930778810994418329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9396063907705081325891105 7047047930778810994418329)
    ·
      refine ⟨5285285948084108245813747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7047047930778810994418329 5285285948084108245813747)
      ·
        refine ⟨7927928922126162368720621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5285285948084108245813747 7927928922126162368720621)
        ·
          refine ⟨2972973345797310888270233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7927928922126162368720621 2972973345797310888270233)
          ·
            refine ⟨2229730009347983166202675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2972973345797310888270233 2229730009347983166202675)
            ·
              refine ⟨3344595014021974749304013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2229730009347983166202675 3344595014021974749304013)
              ·
                refine ⟨1254223130258240530989005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3344595014021974749304013 1254223130258240530989005)
                ·
                  refine ⟨470333673846840199120877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1254223130258240530989005 470333673846840199120877)
                  ·
                    refine ⟨176375127692565074670329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 470333673846840199120877 176375127692565074670329)
                    ·
                      refine ⟨132281345769423806002747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 176375127692565074670329 132281345769423806002747)
                      ·
                        rfl

theorem cell23_257617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 3, 3, 3, 2].length) (baseStart_257617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_257617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_257617 prefixEnd_257617 := by exact prefixLift 257617
  have htrace : WordTrace (prefixWord ++ tailWord_257617) baseStart_257617 baseEnd_257617 := by
    simpa [prefixWord, tailWord_257617, baseEnd_257617] using wordTrace_append hprefix tailTrace_257617
  have hstable : (prefixWord ++ tailWord_257617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257617).length < 2 ^ (prefixWord ++ tailWord_257617).sum := by decide
  have hdescent : baseEnd_257617 < baseStart_257617 := by decide
  rcases family_descends (prefixWord ++ tailWord_257617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257620 : List Nat := [2, 4, 1, 1, 1, 2, 2, 1, 2, 2, 5]
def baseStart_257620 : Nat := 118140960795 + 257620 * 2 ^ 59
def prefixEnd_257620 : Nat := 4983230072969 + 3 ^ 40 * 257620 * 2
def baseEnd_257620 : Nat := 132282886211387294265233

theorem tailTrace_257620 : CollatzResearch.WordTrace tailWord_257620 prefixEnd_257620 132282886211387294265233 := by
  unfold tailWord_257620
  simp only [CollatzResearch.WordTrace]
  refine ⟨4698086663347106419125157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6264115551129475225500209 4698086663347106419125157)
  ·
    refine ⟨880891249377582453585967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4698086663347106419125157 880891249377582453585967)
    ·
      refine ⟨1321336874066373680378951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 880891249377582453585967 1321336874066373680378951)
      ·
        refine ⟨1982005311099560520568427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1321336874066373680378951 1982005311099560520568427)
        ·
          refine ⟨2973007966649340780852641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1982005311099560520568427 2973007966649340780852641)
          ·
            refine ⟨2229755974987005585639481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2973007966649340780852641 2229755974987005585639481)
            ·
              refine ⟨1672316981240254189229611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2229755974987005585639481 1672316981240254189229611)
              ·
                refine ⟨2508475471860381283844417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1672316981240254189229611 2508475471860381283844417)
                ·
                  refine ⟨1881356603895285962883313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2508475471860381283844417 1881356603895285962883313)
                  ·
                    refine ⟨1411017452921464472162485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1881356603895285962883313 1411017452921464472162485)
                    ·
                      refine ⟨132282886211387294265233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1411017452921464472162485 132282886211387294265233)
                      ·
                        rfl

theorem cell23_257620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 1, 2, 2, 5].length) (baseStart_257620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_257620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_257620 prefixEnd_257620 := by exact prefixLift 257620
  have htrace : WordTrace (prefixWord ++ tailWord_257620) baseStart_257620 baseEnd_257620 := by
    simpa [prefixWord, tailWord_257620, baseEnd_257620] using wordTrace_append hprefix tailTrace_257620
  have hstable : (prefixWord ++ tailWord_257620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257620).length < 2 ^ (prefixWord ++ tailWord_257620).sum := by decide
  have hdescent : baseEnd_257620 < baseStart_257620 := by decide
  rcases family_descends (prefixWord ++ tailWord_257620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257680 : List Nat := [2, 1, 1, 1, 1, 1, 3, 4, 1, 5, 3]
def baseStart_257680 : Nat := 118140960795 + 257680 * 2 ^ 59
def prefixEnd_257680 : Nat := 4983230072969 + 3 ^ 40 * 257680 * 2
def baseEnd_257680 : Nat := 132313695050657059514957

theorem tailTrace_257680 : CollatzResearch.WordTrace tailWord_257680 prefixEnd_257680 132313695050657059514957 := by
  unfold tailWord_257680
  simp only [CollatzResearch.WordTrace]
  refine ⟨4699180853238421542717247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6265574470984562056956329 4699180853238421542717247)
  ·
    refine ⟨7048771279857632314075871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4699180853238421542717247 7048771279857632314075871)
    ·
      refine ⟨10573156919786448471113807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7048771279857632314075871 10573156919786448471113807)
      ·
        refine ⟨15859735379679672706670711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10573156919786448471113807 15859735379679672706670711)
        ·
          refine ⟨23789603069519509060006067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15859735379679672706670711 23789603069519509060006067)
          ·
            refine ⟨35684404604279263590009101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23789603069519509060006067 35684404604279263590009101)
            ·
              refine ⟨13381651726604723846253413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35684404604279263590009101 13381651726604723846253413)
              ·
                refine ⟨2509059698738385721172515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13381651726604723846253413 2509059698738385721172515)
                ·
                  refine ⟨3763589548107578581758773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2509059698738385721172515 3763589548107578581758773)
                  ·
                    refine ⟨352836520135085492039885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3763589548107578581758773 352836520135085492039885)
                    ·
                      refine ⟨132313695050657059514957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 352836520135085492039885 132313695050657059514957)
                      ·
                        rfl

theorem cell23_257680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 4, 1, 5, 3].length) (baseStart_257680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_257680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_257680 prefixEnd_257680 := by exact prefixLift 257680
  have htrace : WordTrace (prefixWord ++ tailWord_257680) baseStart_257680 baseEnd_257680 := by
    simpa [prefixWord, tailWord_257680, baseEnd_257680] using wordTrace_append hprefix tailTrace_257680
  have hstable : (prefixWord ++ tailWord_257680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257680).length < 2 ^ (prefixWord ++ tailWord_257680).sum := by decide
  have hdescent : baseEnd_257680 < baseStart_257680 := by decide
  rcases family_descends (prefixWord ++ tailWord_257680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257684 : List Nat := [2, 4, 2, 2, 2, 1, 1, 1, 2, 1, 5]
def baseStart_257684 : Nat := 118140960795 + 257684 * 2 ^ 59
def prefixEnd_257684 : Nat := 4983230072969 + 3 ^ 40 * 257684 * 2
def baseEnd_257684 : Nat := 132315748973275043864939

theorem tailTrace_257684 : CollatzResearch.WordTrace tailWord_257684 prefixEnd_257684 132315748973275043864939 := by
  unfold tailWord_257684
  simp only [CollatzResearch.WordTrace]
  refine ⟨4699253799231175884290053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6265671732308234512386737 4699253799231175884290053)
  ·
    refine ⟨881110087355845478304385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4699253799231175884290053 881110087355845478304385)
    ·
      refine ⟨660832565516884108728289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 881110087355845478304385 660832565516884108728289)
      ·
        refine ⟨495624424137663081546217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 660832565516884108728289 495624424137663081546217)
        ·
          refine ⟨371718318103247311159663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 495624424137663081546217 371718318103247311159663)
          ·
            refine ⟨557577477154870966739495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 371718318103247311159663 557577477154870966739495)
            ·
              refine ⟨836366215732306450109243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 557577477154870966739495 836366215732306450109243)
              ·
                refine ⟨1254549323598459675163865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 836366215732306450109243 1254549323598459675163865)
                ·
                  refine ⟨940911992698844756372899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1254549323598459675163865 940911992698844756372899)
                  ·
                    refine ⟨1411367989048267134559349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 940911992698844756372899 1411367989048267134559349)
                    ·
                      refine ⟨132315748973275043864939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1411367989048267134559349 132315748973275043864939)
                      ·
                        rfl

theorem cell23_257684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 1, 1, 2, 1, 5].length) (baseStart_257684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_257684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_257684 prefixEnd_257684 := by exact prefixLift 257684
  have htrace : WordTrace (prefixWord ++ tailWord_257684) baseStart_257684 baseEnd_257684 := by
    simpa [prefixWord, tailWord_257684, baseEnd_257684] using wordTrace_append hprefix tailTrace_257684
  have hstable : (prefixWord ++ tailWord_257684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257684).length < 2 ^ (prefixWord ++ tailWord_257684).sum := by decide
  have hdescent : baseEnd_257684 < baseStart_257684 := by decide
  rcases family_descends (prefixWord ++ tailWord_257684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257720 : List Nat := [2, 1, 2, 1, 2, 1, 1, 3, 3, 3, 4]
def baseStart_257720 : Nat := 118140960795 + 257720 * 2 ^ 59
def prefixEnd_257720 : Nat := 4983230072969 + 3 ^ 40 * 257720 * 2
def baseEnd_257720 : Nat := 132334234276836903014773

theorem tailTrace_257720 : CollatzResearch.WordTrace tailWord_257720 prefixEnd_257720 132334234276836903014773 := by
  unfold tailWord_257720
  simp only [CollatzResearch.WordTrace]
  refine ⟨4699910313165964958445307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6266547084221286611260409 4699910313165964958445307)
  ·
    refine ⟨7049865469748947437667961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4699910313165964958445307 7049865469748947437667961)
    ·
      refine ⟨5287399102311710578250971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7049865469748947437667961 5287399102311710578250971)
      ·
        refine ⟨7931098653467565867376457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5287399102311710578250971 7931098653467565867376457)
        ·
          refine ⟨5948323990100674400532343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7931098653467565867376457 5948323990100674400532343)
          ·
            refine ⟨8922485985151011600798515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5948323990100674400532343 8922485985151011600798515)
            ·
              refine ⟨13383728977726517401197773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8922485985151011600798515 13383728977726517401197773)
              ·
                refine ⟨5018898366647444025449165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13383728977726517401197773 5018898366647444025449165)
                ·
                  refine ⟨1882086887492791509543437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5018898366647444025449165 1882086887492791509543437)
                  ·
                    refine ⟨705782582809796816078789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1882086887492791509543437 705782582809796816078789)
                    ·
                      refine ⟨132334234276836903014773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 705782582809796816078789 132334234276836903014773)
                      ·
                        rfl

theorem cell23_257720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 3, 3, 3, 4].length) (baseStart_257720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_257720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_257720 prefixEnd_257720 := by exact prefixLift 257720
  have htrace : WordTrace (prefixWord ++ tailWord_257720) baseStart_257720 baseEnd_257720 := by
    simpa [prefixWord, tailWord_257720, baseEnd_257720] using wordTrace_append hprefix tailTrace_257720
  have hstable : (prefixWord ++ tailWord_257720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257720).length < 2 ^ (prefixWord ++ tailWord_257720).sum := by decide
  have hdescent : baseEnd_257720 < baseStart_257720 := by decide
  rcases family_descends (prefixWord ++ tailWord_257720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257760 : List Nat := [2, 1, 1, 3, 1, 2, 2, 3, 8]
def baseStart_257760 : Nat := 118140960795 + 257760 * 2 ^ 59
def prefixEnd_257760 : Nat := 4983230072969 + 3 ^ 40 * 257760 * 2
def baseEnd_257760 : Nat := 14706085944779638501621

theorem tailTrace_257760 : CollatzResearch.WordTrace tailWord_257760 prefixEnd_257760 14706085944779638501621 := by
  unfold tailWord_257760
  simp only [CollatzResearch.WordTrace]
  refine ⟨4700639773093508374173367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6267519697458011165564489 4700639773093508374173367)
  ·
    refine ⟨7050959659640262561260051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4700639773093508374173367 7050959659640262561260051)
    ·
      refine ⟨10576439489460393841890077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7050959659640262561260051 10576439489460393841890077)
      ·
        refine ⟨3966164808547647690708779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10576439489460393841890077 3966164808547647690708779)
        ·
          refine ⟨5949247212821471536063169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3966164808547647690708779 5949247212821471536063169)
          ·
            refine ⟨4461935409616103652047377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5949247212821471536063169 4461935409616103652047377)
            ·
              refine ⟨3346451557212077739035533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4461935409616103652047377 3346451557212077739035533)
              ·
                refine ⟨1254919333954529152138325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3346451557212077739035533 1254919333954529152138325)
                ·
                  refine ⟨14706085944779638501621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1254919333954529152138325 14706085944779638501621)
                  ·
                    rfl

theorem cell23_257760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 3, 8].length) (baseStart_257760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_257760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_257760 prefixEnd_257760 := by exact prefixLift 257760
  have htrace : WordTrace (prefixWord ++ tailWord_257760) baseStart_257760 baseEnd_257760 := by
    simpa [prefixWord, tailWord_257760, baseEnd_257760] using wordTrace_append hprefix tailTrace_257760
  have hstable : (prefixWord ++ tailWord_257760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257760).length < 2 ^ (prefixWord ++ tailWord_257760).sum := by decide
  have hdescent : baseEnd_257760 < baseStart_257760 := by decide
  rcases family_descends (prefixWord ++ tailWord_257760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257777 : List Nat := [1, 2, 2, 2, 2, 3, 2, 3, 6]
def baseStart_257777 : Nat := 118140960795 + 257777 * 2 ^ 59
def prefixEnd_257777 : Nat := 4983230072969 + 3 ^ 40 * 257777 * 2
def baseEnd_257777 : Nat := 14707055852682575555779

theorem tailTrace_257777 : CollatzResearch.WordTrace tailWord_257777 prefixEnd_257777 14707055852682575555779 := by
  unfold tailWord_257777
  simp only [CollatzResearch.WordTrace]
  refine ⟨9401899587125428651715585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6267933058083619101143723 9401899587125428651715585)
  ·
    refine ⟨7051424690344071488786689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9401899587125428651715585 7051424690344071488786689)
    ·
      refine ⟨5288568517758053616590017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7051424690344071488786689 5288568517758053616590017)
      ·
        refine ⟨3966426388318540212442513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5288568517758053616590017 3966426388318540212442513)
        ·
          refine ⟨2974819791238905159331885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3966426388318540212442513 2974819791238905159331885)
          ·
            refine ⟨1115557421714589434749457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2974819791238905159331885 1115557421714589434749457)
            ·
              refine ⟨836668066285942076062093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1115557421714589434749457 836668066285942076062093)
              ·
                refine ⟨313750524857228278523285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 836668066285942076062093 313750524857228278523285)
                ·
                  refine ⟨14707055852682575555779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 313750524857228278523285 14707055852682575555779)
                  ·
                    rfl

theorem cell23_257777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 2, 3, 6].length) (baseStart_257777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_257777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_257777 prefixEnd_257777 := by exact prefixLift 257777
  have htrace : WordTrace (prefixWord ++ tailWord_257777) baseStart_257777 baseEnd_257777 := by
    simpa [prefixWord, tailWord_257777, baseEnd_257777] using wordTrace_append hprefix tailTrace_257777
  have hstable : (prefixWord ++ tailWord_257777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257777).length < 2 ^ (prefixWord ++ tailWord_257777).sum := by decide
  have hdescent : baseEnd_257777 < baseStart_257777 := by decide
  rcases family_descends (prefixWord ++ tailWord_257777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257827 : List Nat := [1, 1, 1, 4, 2, 1, 2, 1, 5, 1, 4]
def baseStart_257827 : Nat := 118140960795 + 257827 * 2 ^ 59
def prefixEnd_257827 : Nat := 4983230072969 + 3 ^ 40 * 257827 * 2
def baseEnd_257827 : Nat := 132389176706867984376781

theorem tailTrace_257827 : CollatzResearch.WordTrace tailWord_257827 prefixEnd_257827 132389176706867984376781 := by
  unfold tailWord_257827
  simp only [CollatzResearch.WordTrace]
  refine ⟨9403723236944287191035735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6269148824629524794023823 9403723236944287191035735)
  ·
    refine ⟨14105584855416430786553603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9403723236944287191035735 14105584855416430786553603)
    ·
      refine ⟨21158377283124646179830405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14105584855416430786553603 21158377283124646179830405)
      ·
        refine ⟨3967195740585871158718201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21158377283124646179830405 3967195740585871158718201)
        ·
          refine ⟨2975396805439403369038651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3967195740585871158718201 2975396805439403369038651)
          ·
            refine ⟨4463095208159105053557977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2975396805439403369038651 4463095208159105053557977)
            ·
              refine ⟨3347321406119328790168483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4463095208159105053557977 3347321406119328790168483)
              ·
                refine ⟨5020982109178993185252725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3347321406119328790168483 5020982109178993185252725)
                ·
                  refine ⟨470717072735530611117443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5020982109178993185252725 470717072735530611117443)
                  ·
                    refine ⟨706075609103295916676165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 470717072735530611117443 706075609103295916676165)
                    ·
                      refine ⟨132389176706867984376781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 706075609103295916676165 132389176706867984376781)
                      ·
                        rfl

theorem cell23_257827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 1, 5, 1, 4].length) (baseStart_257827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_257827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_257827 prefixEnd_257827 := by exact prefixLift 257827
  have htrace : WordTrace (prefixWord ++ tailWord_257827) baseStart_257827 baseEnd_257827 := by
    simpa [prefixWord, tailWord_257827, baseEnd_257827] using wordTrace_append hprefix tailTrace_257827
  have hstable : (prefixWord ++ tailWord_257827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257827).length < 2 ^ (prefixWord ++ tailWord_257827).sum := by decide
  have hdescent : baseEnd_257827 < baseStart_257827 := by decide
  rcases family_descends (prefixWord ++ tailWord_257827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257855 : List Nat := [1, 1, 2, 2, 6, 2, 1, 3, 1, 1, 3]
def baseStart_257855 : Nat := 118140960795 + 257855 * 2 ^ 59
def prefixEnd_257855 : Nat := 4983230072969 + 3 ^ 40 * 257855 * 2
def baseEnd_257855 : Nat := 132403554165193874826653

theorem tailTrace_257855 : CollatzResearch.WordTrace tailWord_257855 prefixEnd_257855 132403554165193874826653 := by
  unfold tailWord_257855
  simp only [CollatzResearch.WordTrace]
  refine ⟨9404744480842847973055019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6269829653895231982036679 9404744480842847973055019)
  ·
    refine ⟨14107116721264271959582529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9404744480842847973055019 14107116721264271959582529)
    ·
      refine ⟨10580337540948203969686897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14107116721264271959582529 10580337540948203969686897)
      ·
        refine ⟨7935253155711152977265173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10580337540948203969686897 7935253155711152977265173)
        ·
          refine ⟨371964991673960295809305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 7935253155711152977265173 371964991673960295809305)
          ·
            refine ⟨278973743755470221856979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 371964991673960295809305 278973743755470221856979)
            ·
              refine ⟨418460615633205332785469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 278973743755470221856979 418460615633205332785469)
              ·
                refine ⟨156922730862451999794551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 418460615633205332785469 156922730862451999794551)
                ·
                  refine ⟨235384096293677999691827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 156922730862451999794551 235384096293677999691827)
                  ·
                    refine ⟨353076144440516999537741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 235384096293677999691827 353076144440516999537741)
                    ·
                      refine ⟨132403554165193874826653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 353076144440516999537741 132403554165193874826653)
                      ·
                        rfl

theorem cell23_257855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 2, 1, 3, 1, 1, 3].length) (baseStart_257855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_257855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_257855 prefixEnd_257855 := by exact prefixLift 257855
  have htrace : WordTrace (prefixWord ++ tailWord_257855) baseStart_257855 baseEnd_257855 := by
    simpa [prefixWord, tailWord_257855, baseEnd_257855] using wordTrace_append hprefix tailTrace_257855
  have hstable : (prefixWord ++ tailWord_257855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257855).length < 2 ^ (prefixWord ++ tailWord_257855).sum := by decide
  have hdescent : baseEnd_257855 < baseStart_257855 := by decide
  rcases family_descends (prefixWord ++ tailWord_257855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257864 : List Nat := [2, 1, 3, 1, 1, 5, 2, 1, 1, 1, 5]
def baseStart_257864 : Nat := 118140960795 + 257864 * 2 ^ 59
def prefixEnd_257864 : Nat := 4983230072969 + 3 ^ 40 * 257864 * 2
def baseEnd_257864 : Nat := 132408175491084339614111

theorem tailTrace_257864 : CollatzResearch.WordTrace tailWord_257864 prefixEnd_257864 132408175491084339614111 := by
  unfold tailWord_257864
  simp only [CollatzResearch.WordTrace]
  refine ⟨4702536368905121255066323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6270048491873495006755097 4702536368905121255066323)
  ·
    refine ⟨7053804553357681882599485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4702536368905121255066323 7053804553357681882599485)
    ·
      refine ⟨2645176707509130705974807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7053804553357681882599485 2645176707509130705974807)
      ·
        refine ⟨3967765061263696058962211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2645176707509130705974807 3967765061263696058962211)
        ·
          refine ⟨5951647591895544088443317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3967765061263696058962211 5951647591895544088443317)
          ·
            refine ⟨557966961740207258291561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5951647591895544088443317 557966961740207258291561)
            ·
              refine ⟨418475221305155443718671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 557966961740207258291561 418475221305155443718671)
              ·
                refine ⟨627712831957733165578007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 418475221305155443718671 627712831957733165578007)
                ·
                  refine ⟨941569247936599748367011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 627712831957733165578007 941569247936599748367011)
                  ·
                    refine ⟨1412353871904899622550517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 941569247936599748367011 1412353871904899622550517)
                    ·
                      refine ⟨132408175491084339614111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1412353871904899622550517 132408175491084339614111)
                      ·
                        rfl

theorem cell23_257864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 2, 1, 1, 1, 5].length) (baseStart_257864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_257864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_257864 prefixEnd_257864 := by exact prefixLift 257864
  have htrace : WordTrace (prefixWord ++ tailWord_257864) baseStart_257864 baseEnd_257864 := by
    simpa [prefixWord, tailWord_257864, baseEnd_257864] using wordTrace_append hprefix tailTrace_257864
  have hstable : (prefixWord ++ tailWord_257864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257864).length < 2 ^ (prefixWord ++ tailWord_257864).sum := by decide
  have hdescent : baseEnd_257864 < baseStart_257864 := by decide
  rcases family_descends (prefixWord ++ tailWord_257864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257888 : List Nat := [2, 1, 1, 3, 3, 4, 2, 1, 2, 4]
def baseStart_257888 : Nat := 118140960795 + 257888 * 2 ^ 59
def prefixEnd_257888 : Nat := 4983230072969 + 3 ^ 40 * 257888 * 2
def baseEnd_257888 : Nat := 44140166342264081904667

theorem tailTrace_257888 : CollatzResearch.WordTrace tailWord_257888 prefixEnd_257888 44140166342264081904667 := by
  unfold tailWord_257888
  simp only [CollatzResearch.WordTrace]
  refine ⟨4702974044861647304503159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6270632059815529739337545 4702974044861647304503159)
  ·
    refine ⟨7054461067292470956754739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4702974044861647304503159 7054461067292470956754739)
    ·
      refine ⟨10581691600938706435132109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7054461067292470956754739 10581691600938706435132109)
      ·
        refine ⟨3968134350352014913174541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10581691600938706435132109 3968134350352014913174541)
        ·
          refine ⟨1488050381382005592440453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3968134350352014913174541 1488050381382005592440453)
          ·
            refine ⟨279009446509126048582585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1488050381382005592440453 279009446509126048582585)
            ·
              refine ⟨209257084881844536436939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 279009446509126048582585 209257084881844536436939)
              ·
                refine ⟨313885627322766804655409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 209257084881844536436939 313885627322766804655409)
                ·
                  refine ⟨235414220492075103491557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 313885627322766804655409 235414220492075103491557)
                  ·
                    refine ⟨44140166342264081904667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 235414220492075103491557 44140166342264081904667)
                    ·
                      rfl

theorem cell23_257888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 4, 2, 1, 2, 4].length) (baseStart_257888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_257888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_257888 prefixEnd_257888 := by exact prefixLift 257888
  have htrace : WordTrace (prefixWord ++ tailWord_257888) baseStart_257888 baseEnd_257888 := by
    simpa [prefixWord, tailWord_257888, baseEnd_257888] using wordTrace_append hprefix tailTrace_257888
  have hstable : (prefixWord ++ tailWord_257888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257888).length < 2 ^ (prefixWord ++ tailWord_257888).sum := by decide
  have hdescent : baseEnd_257888 < baseStart_257888 := by decide
  rcases family_descends (prefixWord ++ tailWord_257888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257898 : List Nat := [3, 1, 3, 4, 1, 1, 1, 1, 3, 2, 3]
def baseStart_257898 : Nat := 118140960795 + 257898 * 2 ^ 59
def prefixEnd_257898 : Nat := 4983230072969 + 3 ^ 40 * 257898 * 2
def baseEnd_257898 : Nat := 132425633833337206588955

theorem tailTrace_257898 : CollatzResearch.WordTrace tailWord_257898 prefixEnd_257898 132425633833337206588955 := by
  unfold tailWord_257898
  simp only [CollatzResearch.WordTrace]
  refine ⟨2351578204921766579217587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6270875213124710877913565 2351578204921766579217587)
  ·
    refine ⟨3527367307382649868826381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2351578204921766579217587 3527367307382649868826381)
    ·
      refine ⟨1322762740268493700809893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3527367307382649868826381 1322762740268493700809893)
      ·
        refine ⟨248018013800342568901855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1322762740268493700809893 248018013800342568901855)
        ·
          refine ⟨372027020700513853352783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248018013800342568901855 372027020700513853352783)
          ·
            refine ⟨558040531050770780029175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 372027020700513853352783 558040531050770780029175)
            ·
              refine ⟨837060796576156170043763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 558040531050770780029175 837060796576156170043763)
              ·
                refine ⟨1255591194864234255065645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 837060796576156170043763 1255591194864234255065645)
                ·
                  refine ⟨470846698074087845649617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1255591194864234255065645 470846698074087845649617)
                  ·
                    refine ⟨353135023555565884237213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 470846698074087845649617 353135023555565884237213)
                    ·
                      refine ⟨132425633833337206588955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 353135023555565884237213 132425633833337206588955)
                      ·
                        rfl

theorem cell23_257898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 1, 1, 3, 2, 3].length) (baseStart_257898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_257898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_257898 prefixEnd_257898 := by exact prefixLift 257898
  have htrace : WordTrace (prefixWord ++ tailWord_257898) baseStart_257898 baseEnd_257898 := by
    simpa [prefixWord, tailWord_257898, baseEnd_257898] using wordTrace_append hprefix tailTrace_257898
  have hstable : (prefixWord ++ tailWord_257898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257898).length < 2 ^ (prefixWord ++ tailWord_257898).sum := by decide
  have hdescent : baseEnd_257898 < baseStart_257898 := by decide
  rcases family_descends (prefixWord ++ tailWord_257898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257937 : List Nat := [1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 5]
def baseStart_257937 : Nat := 118140960795 + 257937 * 2 ^ 59
def prefixEnd_257937 : Nat := 4983230072969 + 3 ^ 40 * 257937 * 2
def baseEnd_257937 : Nat := 132445659578862554001275

theorem tailTrace_257937 : CollatzResearch.WordTrace tailWord_257937 prefixEnd_257937 132445659578862554001275 := by
  unfold tailWord_257937
  simp only [CollatzResearch.WordTrace]
  refine ⟨9407735266545775977540065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6271823511030517318360043 9407735266545775977540065)
  ·
    refine ⟨7055801449909331983155049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9407735266545775977540065 7055801449909331983155049)
    ·
      refine ⟨5291851087431998987366287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7055801449909331983155049 5291851087431998987366287)
      ·
        refine ⟨7937776631147998481049431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5291851087431998987366287 7937776631147998481049431)
        ·
          refine ⟨11906664946721997721574147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7937776631147998481049431 11906664946721997721574147)
          ·
            refine ⟨17859997420082996582361221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11906664946721997721574147 17859997420082996582361221)
            ·
              refine ⟨3348749516265561859192729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17859997420082996582361221 3348749516265561859192729)
              ·
                refine ⟨2511562137199171394394547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3348749516265561859192729 2511562137199171394394547)
                ·
                  refine ⟨3767343205798757091591821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2511562137199171394394547 3767343205798757091591821)
                  ·
                    refine ⟨1412753702174533909346933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3767343205798757091591821 1412753702174533909346933)
                    ·
                      refine ⟨132445659578862554001275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1412753702174533909346933 132445659578862554001275)
                      ·
                        rfl

theorem cell23_257937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 5].length) (baseStart_257937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_257937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_257937 prefixEnd_257937 := by exact prefixLift 257937
  have htrace : WordTrace (prefixWord ++ tailWord_257937) baseStart_257937 baseEnd_257937 := by
    simpa [prefixWord, tailWord_257937, baseEnd_257937] using wordTrace_append hprefix tailTrace_257937
  have hstable : (prefixWord ++ tailWord_257937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257937).length < 2 ^ (prefixWord ++ tailWord_257937).sum := by decide
  have hdescent : baseEnd_257937 < baseStart_257937 := by decide
  rcases family_descends (prefixWord ++ tailWord_257937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257938 : List Nat := [3, 2, 3, 2, 1, 1, 1, 2, 3, 3, 2]
def baseStart_257938 : Nat := 118140960795 + 257938 * 2 ^ 59
def prefixEnd_257938 : Nat := 4983230072969 + 3 ^ 40 * 257938 * 2
def baseEnd_257938 : Nat := 132446173059517050088771

theorem tailTrace_257938 : CollatzResearch.WordTrace tailWord_257938 prefixEnd_257938 132446173059517050088771 := by
  unfold tailWord_257938
  simp only [CollatzResearch.WordTrace]
  refine ⟨2351942934885538287081617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6271847826361435432217645 2351942934885538287081617)
  ·
    refine ⟨1763957201164153715311213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2351942934885538287081617 1763957201164153715311213)
    ·
      refine ⟨661483950436557643241705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1763957201164153715311213 661483950436557643241705)
      ·
        refine ⟨496112962827418232431279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 661483950436557643241705 496112962827418232431279)
        ·
          refine ⟨744169444241127348646919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 496112962827418232431279 744169444241127348646919)
          ·
            refine ⟨1116254166361691022970379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 744169444241127348646919 1116254166361691022970379)
            ·
              refine ⟨1674381249542536534455569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1116254166361691022970379 1674381249542536534455569)
              ·
                refine ⟨1255785937156902400841677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1674381249542536534455569 1255785937156902400841677)
                ·
                  refine ⟨470919726433838400315629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1255785937156902400841677 470919726433838400315629)
                  ·
                    refine ⟨176594897412689400118361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 470919726433838400315629 176594897412689400118361)
                    ·
                      refine ⟨132446173059517050088771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 176594897412689400118361 132446173059517050088771)
                      ·
                        rfl

theorem cell23_257938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 2, 3, 3, 2].length) (baseStart_257938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_257938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_257938 prefixEnd_257938 := by exact prefixLift 257938
  have htrace : WordTrace (prefixWord ++ tailWord_257938) baseStart_257938 baseEnd_257938 := by
    simpa [prefixWord, tailWord_257938, baseEnd_257938] using wordTrace_append hprefix tailTrace_257938
  have hstable : (prefixWord ++ tailWord_257938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257938).length < 2 ^ (prefixWord ++ tailWord_257938).sum := by decide
  have hdescent : baseEnd_257938 < baseStart_257938 := by decide
  rcases family_descends (prefixWord ++ tailWord_257938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257966 : List Nat := [4, 1, 5, 1, 2, 1, 2, 1, 1, 2, 3]
def baseStart_257966 : Nat := 118140960795 + 257966 * 2 ^ 59
def prefixEnd_257966 : Nat := 4983230072969 + 3 ^ 40 * 257966 * 2
def baseEnd_257966 : Nat := 132460550517842940538643

theorem tailTrace_257966 : CollatzResearch.WordTrace tailWord_257966 prefixEnd_257966 132460550517842940538643 := by
  unfold tailWord_257966
  simp only [CollatzResearch.WordTrace]
  refine ⟨1176099122930089241293219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6272528655627142620230501 1176099122930089241293219)
  ·
    refine ⟨1764148684395133861939829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1176099122930089241293219 1764148684395133861939829)
    ·
      refine ⟨165388939162043799556859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1764148684395133861939829 165388939162043799556859)
      ·
        refine ⟨248083408743065699335289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165388939162043799556859 248083408743065699335289)
        ·
          refine ⟨186062556557299274501467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 248083408743065699335289 186062556557299274501467)
          ·
            refine ⟨279093834835948911752201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186062556557299274501467 279093834835948911752201)
            ·
              refine ⟨209320376126961683814151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 279093834835948911752201 209320376126961683814151)
              ·
                refine ⟨313980564190442525721227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 209320376126961683814151 313980564190442525721227)
                ·
                  refine ⟨470970846285663788581841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 313980564190442525721227 470970846285663788581841)
                  ·
                    refine ⟨353228134714247841436381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 470970846285663788581841 353228134714247841436381)
                    ·
                      refine ⟨132460550517842940538643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 353228134714247841436381 132460550517842940538643)
                      ·
                        rfl

theorem cell23_257966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 1, 2, 1, 1, 2, 3].length) (baseStart_257966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_257966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_257966 prefixEnd_257966 := by exact prefixLift 257966
  have htrace : WordTrace (prefixWord ++ tailWord_257966) baseStart_257966 baseEnd_257966 := by
    simpa [prefixWord, tailWord_257966, baseEnd_257966] using wordTrace_append hprefix tailTrace_257966
  have hstable : (prefixWord ++ tailWord_257966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257966).length < 2 ^ (prefixWord ++ tailWord_257966).sum := by decide
  have hdescent : baseEnd_257966 < baseStart_257966 := by decide
  rcases family_descends (prefixWord ++ tailWord_257966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257972 : List Nat := [2, 5, 2, 1, 2, 1, 1, 3, 1, 3, 2]
def baseStart_257972 : Nat := 118140960795 + 257972 * 2 ^ 59
def prefixEnd_257972 : Nat := 4983230072969 + 3 ^ 40 * 257972 * 2
def baseEnd_257972 : Nat := 132463631401769917063615

theorem tailTrace_257972 : CollatzResearch.WordTrace tailWord_257972 prefixEnd_257972 132463631401769917063615 := by
  unfold tailWord_257972
  simp only [CollatzResearch.WordTrace]
  refine ⟨4704505910709488477532085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6272674547612651303376113 4704505910709488477532085)
  ·
    refine ⟨441047429129014544768633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4704505910709488477532085 441047429129014544768633)
    ·
      refine ⟨330785571846760908576475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 441047429129014544768633 330785571846760908576475)
      ·
        refine ⟨496178357770141362864713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 330785571846760908576475 496178357770141362864713)
        ·
          refine ⟨372133768327606022148535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 496178357770141362864713 372133768327606022148535)
          ·
            refine ⟨558200652491409033222803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 372133768327606022148535 558200652491409033222803)
            ·
              refine ⟨837300978737113549834205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 558200652491409033222803 837300978737113549834205)
              ·
                refine ⟨313987867026417581187827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 837300978737113549834205 313987867026417581187827)
                ·
                  refine ⟨470981800539626371781741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 313987867026417581187827 470981800539626371781741)
                  ·
                    refine ⟨176618175202359889418153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 470981800539626371781741 176618175202359889418153)
                    ·
                      refine ⟨132463631401769917063615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 176618175202359889418153 132463631401769917063615)
                      ·
                        rfl

theorem cell23_257972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 1, 3, 1, 3, 2].length) (baseStart_257972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_257972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_257972 prefixEnd_257972 := by exact prefixLift 257972
  have htrace : WordTrace (prefixWord ++ tailWord_257972) baseStart_257972 baseEnd_257972 := by
    simpa [prefixWord, tailWord_257972, baseEnd_257972] using wordTrace_append hprefix tailTrace_257972
  have hstable : (prefixWord ++ tailWord_257972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257972).length < 2 ^ (prefixWord ++ tailWord_257972).sum := by decide
  have hdescent : baseEnd_257972 < baseStart_257972 := by decide
  rcases family_descends (prefixWord ++ tailWord_257972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257984 : List Nat := [2, 1, 1, 2, 3, 2, 1, 1, 4, 3, 3]
def baseStart_257984 : Nat := 118140960795 + 257984 * 2 ^ 59
def prefixEnd_257984 : Nat := 4983230072969 + 3 ^ 40 * 257984 * 2
def baseEnd_257984 : Nat := 132469793169623870113559

theorem tailTrace_257984 : CollatzResearch.WordTrace tailWord_257984 prefixEnd_257984 132469793169623870113559 := by
  unfold tailWord_257984
  simp only [CollatzResearch.WordTrace]
  refine ⟨4704724748687751502250503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6272966331583668669667337 4704724748687751502250503)
  ·
    refine ⟨7057087123031627253375755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4704724748687751502250503 7057087123031627253375755)
    ·
      refine ⟨10585630684547440880063633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7057087123031627253375755 10585630684547440880063633)
      ·
        refine ⟨7939223013410580660047725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10585630684547440880063633 7939223013410580660047725)
        ·
          refine ⟨2977208630028967747517897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7939223013410580660047725 2977208630028967747517897)
          ·
            refine ⟨2232906472521725810638423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2977208630028967747517897 2232906472521725810638423)
            ·
              refine ⟨3349359708782588715957635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2232906472521725810638423 3349359708782588715957635)
              ·
                refine ⟨5024039563173883073936453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3349359708782588715957635 5024039563173883073936453)
                ·
                  refine ⟨942007418095103076363085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5024039563173883073936453 942007418095103076363085)
                  ·
                    refine ⟨353252781785663653636157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 942007418095103076363085 353252781785663653636157)
                    ·
                      refine ⟨132469793169623870113559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 353252781785663653636157 132469793169623870113559)
                      ·
                        rfl

theorem cell23_257984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 1, 4, 3, 3].length) (baseStart_257984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_257984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_257984 prefixEnd_257984 := by exact prefixLift 257984
  have htrace : WordTrace (prefixWord ++ tailWord_257984) baseStart_257984 baseEnd_257984 := by
    simpa [prefixWord, tailWord_257984, baseEnd_257984] using wordTrace_append hprefix tailTrace_257984
  have hstable : (prefixWord ++ tailWord_257984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257984).length < 2 ^ (prefixWord ++ tailWord_257984).sum := by decide
  have hdescent : baseEnd_257984 < baseStart_257984 := by decide
  rcases family_descends (prefixWord ++ tailWord_257984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257987 : List Nat := [1, 1, 1, 3, 1, 1, 2, 1, 5, 7]
def baseStart_257987 : Nat := 118140960795 + 257987 * 2 ^ 59
def prefixEnd_257987 : Nat := 4983230072969 + 3 ^ 40 * 257987 * 2
def baseEnd_257987 : Nat := 44157111203862452792015

theorem tailTrace_257987 : CollatzResearch.WordTrace tailWord_257987 prefixEnd_257987 44157111203862452792015 := by
  unfold tailWord_257987
  simp only [CollatzResearch.WordTrace]
  refine ⟨9409558916364634516860215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6273039277576423011240143 9409558916364634516860215)
  ·
    refine ⟨14114338374546951775290323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9409558916364634516860215 14114338374546951775290323)
    ·
      refine ⟨21171507561820427662935485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14114338374546951775290323 21171507561820427662935485)
      ·
        refine ⟨7939315335682660373600807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21171507561820427662935485 7939315335682660373600807)
        ·
          refine ⟨11908973003523990560401211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7939315335682660373600807 11908973003523990560401211)
          ·
            refine ⟨17863459505285985840601817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11908973003523990560401211 17863459505285985840601817)
            ·
              refine ⟨13397594628964489380451363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17863459505285985840601817 13397594628964489380451363)
              ·
                refine ⟨20096391943446734070677045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13397594628964489380451363 20096391943446734070677045)
                ·
                  refine ⟨1884036744698131319125973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 20096391943446734070677045 1884036744698131319125973)
                  ·
                    refine ⟨44157111203862452792015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1884036744698131319125973 44157111203862452792015)
                    ·
                      rfl

theorem cell23_257987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 1, 5, 7].length) (baseStart_257987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_257987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_257987 prefixEnd_257987 := by exact prefixLift 257987
  have htrace : WordTrace (prefixWord ++ tailWord_257987) baseStart_257987 baseEnd_257987 := by
    simpa [prefixWord, tailWord_257987, baseEnd_257987] using wordTrace_append hprefix tailTrace_257987
  have hstable : (prefixWord ++ tailWord_257987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257987).length < 2 ^ (prefixWord ++ tailWord_257987).sum := by decide
  have hdescent : baseEnd_257987 < baseStart_257987 := by decide
  rcases family_descends (prefixWord ++ tailWord_257987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_258002 : List Nat := [3, 2, 2, 3, 3, 1, 1, 1, 1, 4, 2]
def baseStart_258002 : Nat := 118140960795 + 258002 * 2 ^ 59
def prefixEnd_258002 : Nat := 4983230072969 + 3 ^ 40 * 258002 * 2
def baseEnd_258002 : Nat := 132479035821404799688477

theorem tailTrace_258002 : CollatzResearch.WordTrace tailWord_258002 prefixEnd_258002 132479035821404799688477 := by
  unfold tailWord_258002
  simp only [CollatzResearch.WordTrace]
  refine ⟨2352526502827573019664065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6273404007540194719104173 2352526502827573019664065)
  ·
    refine ⟨1764394877120679764748049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2352526502827573019664065 1764394877120679764748049)
    ·
      refine ⟨1323296157840509823561037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1764394877120679764748049 1323296157840509823561037)
      ·
        refine ⟨496236059190191183835389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1323296157840509823561037 496236059190191183835389)
        ·
          refine ⟨186088522196321693938271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 496236059190191183835389 186088522196321693938271)
          ·
            refine ⟨279132783294482540907407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186088522196321693938271 279132783294482540907407)
            ·
              refine ⟨418699174941723811361111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 279132783294482540907407 418699174941723811361111)
              ·
                refine ⟨628048762412585717041667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 418699174941723811361111 628048762412585717041667)
                ·
                  refine ⟨942073143618878575562501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 628048762412585717041667 942073143618878575562501)
                  ·
                    refine ⟨176638714428539732917969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 942073143618878575562501 176638714428539732917969)
                    ·
                      refine ⟨132479035821404799688477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 176638714428539732917969 132479035821404799688477)
                      ·
                        rfl

theorem cell23_258002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 1, 1, 1, 1, 4, 2].length) (baseStart_258002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_258002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_258002 prefixEnd_258002 := by exact prefixLift 258002
  have htrace : WordTrace (prefixWord ++ tailWord_258002) baseStart_258002 baseEnd_258002 := by
    simpa [prefixWord, tailWord_258002, baseEnd_258002] using wordTrace_append hprefix tailTrace_258002
  have hstable : (prefixWord ++ tailWord_258002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_258002).length < 2 ^ (prefixWord ++ tailWord_258002).sum := by decide
  have hdescent : baseEnd_258002 < baseStart_258002 := by decide
  rcases family_descends (prefixWord ++ tailWord_258002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_258004 : List Nat := [2, 4, 1, 2, 1, 1, 1, 1, 3, 7]
def baseStart_258004 : Nat := 118140960795 + 258004 * 2 ^ 59
def prefixEnd_258004 : Nat := 4983230072969 + 3 ^ 40 * 258004 * 2
def baseEnd_258004 : Nat := 44160020927571263954489

theorem tailTrace_258004 : CollatzResearch.WordTrace tailWord_258004 prefixEnd_258004 44160020927571263954489 := by
  unfold tailWord_258004
  simp only [CollatzResearch.WordTrace]
  refine ⟨4705089478651523210114533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6273452638202030946819377 4705089478651523210114533)
  ·
    refine ⟨882204277247160601896475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4705089478651523210114533 882204277247160601896475)
    ·
      refine ⟨1323306415870740902844713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 882204277247160601896475 1323306415870740902844713)
      ·
        refine ⟨992479811903055677133535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1323306415870740902844713 992479811903055677133535)
        ·
          refine ⟨1488719717854583515700303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 992479811903055677133535 1488719717854583515700303)
          ·
            refine ⟨2233079576781875273550455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1488719717854583515700303 2233079576781875273550455)
            ·
              refine ⟨3349619365172812910325683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2233079576781875273550455 3349619365172812910325683)
              ·
                refine ⟨5024429047759219365488525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3349619365172812910325683 5024429047759219365488525)
                ·
                  refine ⟨1884160892909707262058197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5024429047759219365488525 1884160892909707262058197)
                  ·
                    refine ⟨44160020927571263954489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1884160892909707262058197 44160020927571263954489)
                    ·
                      rfl

theorem cell23_258004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 1, 3, 7].length) (baseStart_258004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_258004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_258004 prefixEnd_258004 := by exact prefixLift 258004
  have htrace : WordTrace (prefixWord ++ tailWord_258004) baseStart_258004 baseEnd_258004 := by
    simpa [prefixWord, tailWord_258004, baseEnd_258004] using wordTrace_append hprefix tailTrace_258004
  have hstable : (prefixWord ++ tailWord_258004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_258004).length < 2 ^ (prefixWord ++ tailWord_258004).sum := by decide
  have hdescent : baseEnd_258004 < baseStart_258004 := by decide
  rcases family_descends (prefixWord ++ tailWord_258004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_258038 : List Nat := [5, 1, 1, 1, 4, 1, 1, 2, 2, 5]
def baseStart_258038 : Nat := 118140960795 + 258038 * 2 ^ 59
def prefixEnd_258038 : Nat := 4983230072969 + 3 ^ 40 * 258038 * 2
def baseEnd_258038 : Nat := 44165840374988886279437

theorem tailTrace_258038 : CollatzResearch.WordTrace tailWord_258038 prefixEnd_258038 44165840374988886279437 := by
  unfold tailWord_258038
  simp only [CollatzResearch.WordTrace]
  refine ⟨588213689948741889185423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6274279359453246817977845 588213689948741889185423)
  ·
    refine ⟨882320534923112833778135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 588213689948741889185423 882320534923112833778135)
    ·
      refine ⟨1323480802384669250667203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 882320534923112833778135 1323480802384669250667203)
      ·
        refine ⟨1985221203577003876000805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1323480802384669250667203 1985221203577003876000805)
        ·
          refine ⟨372228975670688226750151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1985221203577003876000805 372228975670688226750151)
          ·
            refine ⟨558343463506032340125227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 372228975670688226750151 558343463506032340125227)
            ·
              refine ⟨837515195259048510187841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 558343463506032340125227 837515195259048510187841)
              ·
                refine ⟨628136396444286382640881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 837515195259048510187841 628136396444286382640881)
                ·
                  refine ⟨471102297333214786980661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 628136396444286382640881 471102297333214786980661)
                  ·
                    refine ⟨44165840374988886279437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 471102297333214786980661 44165840374988886279437)
                    ·
                      rfl

theorem cell23_258038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 1, 2, 2, 5].length) (baseStart_258038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_258038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_258038 prefixEnd_258038 := by exact prefixLift 258038
  have htrace : WordTrace (prefixWord ++ tailWord_258038) baseStart_258038 baseEnd_258038 := by
    simpa [prefixWord, tailWord_258038, baseEnd_258038] using wordTrace_append hprefix tailTrace_258038
  have hstable : (prefixWord ++ tailWord_258038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_258038).length < 2 ^ (prefixWord ++ tailWord_258038).sum := by decide
  have hdescent : baseEnd_258038 < baseStart_258038 := by decide
  rcases family_descends (prefixWord ++ tailWord_258038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_258041 : List Nat := [1, 2, 1, 3, 1, 5, 1, 2, 2, 1, 4]
def baseStart_258041 : Nat := 118140960795 + 258041 * 2 ^ 59
def prefixEnd_258041 : Nat := 4983230072969 + 3 ^ 40 * 258041 * 2
def baseEnd_258041 : Nat := 132499061566930147100797

theorem tailTrace_258041 : CollatzResearch.WordTrace tailWord_258041 prefixEnd_258041 132499061566930147100797 := by
  unfold tailWord_258041
  simp only [CollatzResearch.WordTrace]
  refine ⟨9411528458169001739325977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6274352305446001159550651 9411528458169001739325977)
  ·
    refine ⟨7058646343626751304494483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9411528458169001739325977 7058646343626751304494483)
    ·
      refine ⟨10587969515440126956741725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7058646343626751304494483 10587969515440126956741725)
      ·
        refine ⟨3970488568290047608778147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10587969515440126956741725 3970488568290047608778147)
        ·
          refine ⟨5955732852435071413167221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3970488568290047608778147 5955732852435071413167221)
          ·
            refine ⟨558349954915787944984427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5955732852435071413167221 558349954915787944984427)
            ·
              refine ⟨837524932373681917476641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 558349954915787944984427 837524932373681917476641)
              ·
                refine ⟨628143699280261438107481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 837524932373681917476641 628143699280261438107481)
                ·
                  refine ⟨471107774460196078580611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 628143699280261438107481 471107774460196078580611)
                  ·
                    refine ⟨706661661690294117870917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 471107774460196078580611 706661661690294117870917)
                    ·
                      refine ⟨132499061566930147100797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 706661661690294117870917 132499061566930147100797)
                      ·
                        rfl

theorem cell23_258041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 1, 2, 2, 1, 4].length) (baseStart_258041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_258041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_258041 prefixEnd_258041 := by exact prefixLift 258041
  have htrace : WordTrace (prefixWord ++ tailWord_258041) baseStart_258041 baseEnd_258041 := by
    simpa [prefixWord, tailWord_258041, baseEnd_258041] using wordTrace_append hprefix tailTrace_258041
  have hstable : (prefixWord ++ tailWord_258041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_258041).length < 2 ^ (prefixWord ++ tailWord_258041).sum := by decide
  have hdescent : baseEnd_258041 < baseStart_258041 := by decide
  rcases family_descends (prefixWord ++ tailWord_258041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_258064 : List Nat := [2, 1, 1, 1, 1, 1, 1, 9, 6]
def baseStart_258064 : Nat := 118140960795 + 258064 * 2 ^ 59
def prefixEnd_258064 : Nat := 4983230072969 + 3 ^ 40 * 258064 * 2
def baseEnd_258064 : Nat := 14723430180220395234799

theorem tailTrace_258064 : CollatzResearch.WordTrace tailWord_258064 prefixEnd_258064 14723430180220395234799 := by
  unfold tailWord_258064
  simp only [CollatzResearch.WordTrace]
  refine ⟨4706183668542838333706623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6274911558057117778275497 4706183668542838333706623)
  ·
    refine ⟨7059275502814257500559935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4706183668542838333706623 7059275502814257500559935)
    ·
      refine ⟨10588913254221386250839903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7059275502814257500559935 10588913254221386250839903)
      ·
        refine ⟨15883369881332079376259855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10588913254221386250839903 15883369881332079376259855)
        ·
          refine ⟨23825054821998119064389783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15883369881332079376259855 23825054821998119064389783)
          ·
            refine ⟨35737582232997178596584675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23825054821998119064389783 35737582232997178596584675)
            ·
              refine ⟨53606373349495767894877013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35737582232997178596584675 53606373349495767894877013)
              ·
                refine ⟨314099843844701765009045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 53606373349495767894877013 314099843844701765009045)
                ·
                  refine ⟨14723430180220395234799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 314099843844701765009045 14723430180220395234799)
                  ·
                    rfl

theorem cell23_258064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 9, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 9, 6].length) (baseStart_258064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_258064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_258064 prefixEnd_258064 := by exact prefixLift 258064
  have htrace : WordTrace (prefixWord ++ tailWord_258064) baseStart_258064 baseEnd_258064 := by
    simpa [prefixWord, tailWord_258064, baseEnd_258064] using wordTrace_append hprefix tailTrace_258064
  have hstable : (prefixWord ++ tailWord_258064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_258064).length < 2 ^ (prefixWord ++ tailWord_258064).sum := by decide
  have hdescent : baseEnd_258064 < baseStart_258064 := by decide
  rcases family_descends (prefixWord ++ tailWord_258064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_258091 : List Nat := [1, 1, 1, 1, 2, 1, 4, 1, 7, 1, 3]
def baseStart_258091 : Nat := 118140960795 + 258091 * 2 ^ 59
def prefixEnd_258091 : Nat := 4983230072969 + 3 ^ 40 * 258091 * 2
def baseEnd_258091 : Nat := 132524735599654951475567

theorem tailTrace_258091 : CollatzResearch.WordTrace tailWord_258091 prefixEnd_258091 132524735599654951475567 := by
  unfold tailWord_258091
  simp only [CollatzResearch.WordTrace]
  refine ⟨9413352107987860278646127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6275568071991906852430751 9413352107987860278646127)
  ·
    refine ⟨14120028161981790417969191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9413352107987860278646127 14120028161981790417969191)
    ·
      refine ⟨21180042242972685626953787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14120028161981790417969191 21180042242972685626953787)
      ·
        refine ⟨31770063364459028440430681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21180042242972685626953787 31770063364459028440430681)
        ·
          refine ⟨23827547523344271330323011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31770063364459028440430681 23827547523344271330323011)
          ·
            refine ⟨35741321285016406995484517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23827547523344271330323011 35741321285016406995484517)
            ·
              refine ⟨6701497740940576311653347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35741321285016406995484517 6701497740940576311653347)
              ·
                refine ⟨10052246611410864467480021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6701497740940576311653347 10052246611410864467480021)
                ·
                  refine ⟨235599529954942135956563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10052246611410864467480021 235599529954942135956563)
                  ·
                    refine ⟨353399294932413203934845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 235599529954942135956563 353399294932413203934845)
                    ·
                      refine ⟨132524735599654951475567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 353399294932413203934845 132524735599654951475567)
                      ·
                        rfl

theorem cell23_258091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 1, 7, 1, 3].length) (baseStart_258091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_258091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_258091 prefixEnd_258091 := by exact prefixLift 258091
  have htrace : WordTrace (prefixWord ++ tailWord_258091) baseStart_258091 baseEnd_258091 := by
    simpa [prefixWord, tailWord_258091, baseEnd_258091] using wordTrace_append hprefix tailTrace_258091
  have hstable : (prefixWord ++ tailWord_258091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_258091).length < 2 ^ (prefixWord ++ tailWord_258091).sum := by decide
  have hdescent : baseEnd_258091 < baseStart_258091 := by decide
  rcases family_descends (prefixWord ++ tailWord_258091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_258108 : List Nat := [2, 2, 2, 2, 2, 1, 2, 3, 3, 1, 3]
def baseStart_258108 : Nat := 118140960795 + 258108 * 2 ^ 59
def prefixEnd_258108 : Nat := 4983230072969 + 3 ^ 40 * 258108 * 2
def baseEnd_258108 : Nat := 132533464770781384962989

theorem tailTrace_258108 : CollatzResearch.WordTrace tailWord_258108 prefixEnd_258108 132533464770781384962989 := by
  unfold tailWord_258108
  simp only [CollatzResearch.WordTrace]
  refine ⟨4706986074463136091007489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6275981432617514788009985 4706986074463136091007489)
  ·
    refine ⟨3530239555847352068255617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4706986074463136091007489 3530239555847352068255617)
    ·
      refine ⟨2647679666885514051191713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3530239555847352068255617 2647679666885514051191713)
      ·
        refine ⟨1985759750164135538393785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2647679666885514051191713 1985759750164135538393785)
        ·
          refine ⟨1489319812623101653795339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1985759750164135538393785 1489319812623101653795339)
          ·
            refine ⟨2233979718934652480693009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1489319812623101653795339 2233979718934652480693009)
            ·
              refine ⟨1675484789200989360519757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2233979718934652480693009 1675484789200989360519757)
              ·
                refine ⟨628306795950371010194909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1675484789200989360519757 628306795950371010194909)
                ·
                  refine ⟨235615048481389128823091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 628306795950371010194909 235615048481389128823091)
                  ·
                    refine ⟨353422572722083693234637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 235615048481389128823091 353422572722083693234637)
                    ·
                      refine ⟨132533464770781384962989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 353422572722083693234637 132533464770781384962989)
                      ·
                        rfl

theorem cell23_258108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 3, 3, 1, 3].length) (baseStart_258108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_258108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_258108 prefixEnd_258108 := by exact prefixLift 258108
  have htrace : WordTrace (prefixWord ++ tailWord_258108) baseStart_258108 baseEnd_258108 := by
    simpa [prefixWord, tailWord_258108, baseEnd_258108] using wordTrace_append hprefix tailTrace_258108
  have hstable : (prefixWord ++ tailWord_258108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_258108).length < 2 ^ (prefixWord ++ tailWord_258108).sum := by decide
  have hdescent : baseEnd_258108 < baseStart_258108 := by decide
  rcases family_descends (prefixWord ++ tailWord_258108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_258125 : List Nat := [1, 6, 1, 1, 1, 1, 3, 2, 3, 1, 3]
def baseStart_258125 : Nat := 118140960795 + 258125 * 2 ^ 59
def prefixEnd_258125 : Nat := 4983230072969 + 3 ^ 40 * 258125 * 2
def baseEnd_258125 : Nat := 132542193941907818450411

theorem tailTrace_258125 : CollatzResearch.WordTrace tailWord_258125 prefixEnd_258125 132542193941907818450411 := by
  unfold tailWord_258125
  simp only [CollatzResearch.WordTrace]
  refine ⟨9414592189864684085383829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6276394793243122723589219 9414592189864684085383829)
  ·
    refine ⟨441309008899907066502367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 9414592189864684085383829 441309008899907066502367)
    ·
      refine ⟨661963513349860599753551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 441309008899907066502367 661963513349860599753551)
      ·
        refine ⟨992945270024790899630327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 661963513349860599753551 992945270024790899630327)
        ·
          refine ⟨1489417905037186349445491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 992945270024790899630327 1489417905037186349445491)
          ·
            refine ⟨2234126857555779524168237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1489417905037186349445491 2234126857555779524168237)
            ·
              refine ⟨837797571583417321563089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2234126857555779524168237 837797571583417321563089)
              ·
                refine ⟨628348178687562991172317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 837797571583417321563089 628348178687562991172317)
                ·
                  refine ⟨235630567007836121689619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 628348178687562991172317 235630567007836121689619)
                  ·
                    refine ⟨353445850511754182534429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 235630567007836121689619 353445850511754182534429)
                    ·
                      refine ⟨132542193941907818450411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 353445850511754182534429 132542193941907818450411)
                      ·
                        rfl

theorem cell23_258125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 3, 2, 3, 1, 3].length) (baseStart_258125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_258125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_258125 prefixEnd_258125 := by exact prefixLift 258125
  have htrace : WordTrace (prefixWord ++ tailWord_258125) baseStart_258125 baseEnd_258125 := by
    simpa [prefixWord, tailWord_258125, baseEnd_258125] using wordTrace_append hprefix tailTrace_258125
  have hstable : (prefixWord ++ tailWord_258125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_258125).length < 2 ^ (prefixWord ++ tailWord_258125).sum := by decide
  have hdescent : baseEnd_258125 < baseStart_258125 := by decide
  rcases family_descends (prefixWord ++ tailWord_258125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_258151 : List Nat := [1, 1, 5, 1, 1, 2, 2, 3, 1, 1, 5]
def baseStart_258151 : Nat := 118140960795 + 258151 * 2 ^ 59
def prefixEnd_258151 : Nat := 4983230072969 + 3 ^ 40 * 258151 * 2
def baseEnd_258151 : Nat := 132555544438924716725291

theorem tailTrace_258151 : CollatzResearch.WordTrace tailWord_258151 prefixEnd_258151 132555544438924716725291 := by
  unfold tailWord_258151
  simp only [CollatzResearch.WordTrace]
  refine ⟨9415540487770490525830307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6277026991846993683886871 9415540487770490525830307)
  ·
    refine ⟨14123310731655735788745461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9415540487770490525830307 14123310731655735788745461)
    ·
      refine ⟨1324060381092725230194887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 14123310731655735788745461 1324060381092725230194887)
      ·
        refine ⟨1986090571639087845292331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1324060381092725230194887 1986090571639087845292331)
        ·
          refine ⟨2979135857458631767938497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1986090571639087845292331 2979135857458631767938497)
          ·
            refine ⟨2234351893093973825953873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2979135857458631767938497 2234351893093973825953873)
            ·
              refine ⟨1675763919820480369465405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2234351893093973825953873 1675763919820480369465405)
              ·
                refine ⟨628411469932680138549527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1675763919820480369465405 628411469932680138549527)
                ·
                  refine ⟨942617204899020207824291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 628411469932680138549527 942617204899020207824291)
                  ·
                    refine ⟨1413925807348530311736437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 942617204899020207824291 1413925807348530311736437)
                    ·
                      refine ⟨132555544438924716725291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1413925807348530311736437 132555544438924716725291)
                      ·
                        rfl

theorem cell23_258151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 3, 1, 1, 5].length) (baseStart_258151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_258151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_258151 prefixEnd_258151 := by exact prefixLift 258151
  have htrace : WordTrace (prefixWord ++ tailWord_258151) baseStart_258151 baseEnd_258151 := by
    simpa [prefixWord, tailWord_258151, baseEnd_258151] using wordTrace_append hprefix tailTrace_258151
  have hstable : (prefixWord ++ tailWord_258151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_258151).length < 2 ^ (prefixWord ++ tailWord_258151).sum := by decide
  have hdescent : baseEnd_258151 < baseStart_258151 := by decide
  rcases family_descends (prefixWord ++ tailWord_258151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_258158 : List Nat := [4, 1, 2, 2, 1, 1, 3, 1, 4, 4]
def baseStart_258158 : Nat := 118140960795 + 258158 * 2 ^ 59
def prefixEnd_258158 : Nat := 4983230072969 + 3 ^ 40 * 258158 * 2
def baseEnd_258158 : Nat := 44186379601168729779253

theorem tailTrace_258158 : CollatzResearch.WordTrace tailWord_258158 prefixEnd_258158 44186379601168729779253 := by
  unfold tailWord_258158
  simp only [CollatzResearch.WordTrace]
  refine ⟨1176974474843141340166891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6277197199163420480890085 1176974474843141340166891)
  ·
    refine ⟨1765461712264712010250337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1176974474843141340166891 1765461712264712010250337)
    ·
      refine ⟨1324096284198534007687753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1765461712264712010250337 1324096284198534007687753)
      ·
        refine ⟨993072213148900505765815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1324096284198534007687753 993072213148900505765815)
        ·
          refine ⟨1489608319723350758648723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 993072213148900505765815 1489608319723350758648723)
          ·
            refine ⟨2234412479585026137973085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1489608319723350758648723 2234412479585026137973085)
            ·
              refine ⟨837904679844384801739907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2234412479585026137973085 837904679844384801739907)
              ·
                refine ⟨1256857019766577202609861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 837904679844384801739907 1256857019766577202609861)
                ·
                  refine ⟨235660691206233225489349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1256857019766577202609861 235660691206233225489349)
                  ·
                    refine ⟨44186379601168729779253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 235660691206233225489349 44186379601168729779253)
                    ·
                      rfl

theorem cell23_258158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 3, 1, 4, 4].length) (baseStart_258158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_258158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_258158 prefixEnd_258158 := by exact prefixLift 258158
  have htrace : WordTrace (prefixWord ++ tailWord_258158) baseStart_258158 baseEnd_258158 := by
    simpa [prefixWord, tailWord_258158, baseEnd_258158] using wordTrace_append hprefix tailTrace_258158
  have hstable : (prefixWord ++ tailWord_258158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_258158).length < 2 ^ (prefixWord ++ tailWord_258158).sum := by decide
  have hdescent : baseEnd_258158 < baseStart_258158 := by decide
  rcases family_descends (prefixWord ++ tailWord_258158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_258258 : List Nat := [3, 2, 2, 2, 1, 2, 2, 1, 2, 1, 5]
def baseStart_258258 : Nat := 118140960795 + 258258 * 2 ^ 59
def prefixEnd_258258 : Nat := 4983230072969 + 3 ^ 40 * 258258 * 2
def baseEnd_258258 : Nat := 132610486868955798087299

theorem tailTrace_258258 : CollatzResearch.WordTrace tailWord_258258 prefixEnd_258258 132610486868955798087299 := by
  unfold tailWord_258258
  simp only [CollatzResearch.WordTrace]
  refine ⟨2354860774595711949993857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6279628732255231866650285 2354860774595711949993857)
  ·
    refine ⟨1766145580946783962495393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2354860774595711949993857 1766145580946783962495393)
    ·
      refine ⟨1324609185710087971871545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1766145580946783962495393 1324609185710087971871545)
      ·
        refine ⟨993456889282565978903659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1324609185710087971871545 993456889282565978903659)
        ·
          refine ⟨1490185333923848968355489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 993456889282565978903659 1490185333923848968355489)
          ·
            refine ⟨1117639000442886726266617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1490185333923848968355489 1117639000442886726266617)
            ·
              refine ⟨838229250332165044699963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1117639000442886726266617 838229250332165044699963)
              ·
                refine ⟨1257343875498247567049945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 838229250332165044699963 1257343875498247567049945)
                ·
                  refine ⟨943007906623685675287459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1257343875498247567049945 943007906623685675287459)
                  ·
                    refine ⟨1414511859935528512931189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 943007906623685675287459 1414511859935528512931189)
                    ·
                      refine ⟨132610486868955798087299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1414511859935528512931189 132610486868955798087299)
                      ·
                        rfl

theorem cell23_258258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 2, 1, 2, 1, 5].length) (baseStart_258258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_258258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_258258 prefixEnd_258258 := by exact prefixLift 258258
  have htrace : WordTrace (prefixWord ++ tailWord_258258) baseStart_258258 baseEnd_258258 := by
    simpa [prefixWord, tailWord_258258, baseEnd_258258] using wordTrace_append hprefix tailTrace_258258
  have hstable : (prefixWord ++ tailWord_258258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_258258).length < 2 ^ (prefixWord ++ tailWord_258258).sum := by decide
  have hdescent : baseEnd_258258 < baseStart_258258 := by decide
  rcases family_descends (prefixWord ++ tailWord_258258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_258272 : List Nat := [2, 1, 1, 3, 1, 3, 4, 2, 2, 2, 2]
def baseStart_258272 : Nat := 118140960795 + 258272 * 2 ^ 59
def prefixEnd_258272 : Nat := 4983230072969 + 3 ^ 40 * 258272 * 2
def baseEnd_258272 : Nat := 132617675598118743312235

theorem tailTrace_258272 : CollatzResearch.WordTrace tailWord_258272 prefixEnd_258272 132617675598118743312235 := by
  unfold tailWord_258272
  simp only [CollatzResearch.WordTrace]
  refine ⟨4709976860166064095492535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6279969146888085460656713 4709976860166064095492535)
  ·
    refine ⟨7064965290249096143238803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4709976860166064095492535 7064965290249096143238803)
    ·
      refine ⟨10597447935373644214858205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7064965290249096143238803 10597447935373644214858205)
      ·
        refine ⟨3974042975765116580571827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10597447935373644214858205 3974042975765116580571827)
        ·
          refine ⟨5961064463647674870857741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3974042975765116580571827 5961064463647674870857741)
          ·
            refine ⟨2235399173867878076571653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5961064463647674870857741 2235399173867878076571653)
            ·
              refine ⟨419137345100227139357185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2235399173867878076571653 419137345100227139357185)
              ·
                refine ⟨314353008825170354517889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 419137345100227139357185 314353008825170354517889)
                ·
                  refine ⟨235764756618877765888417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 314353008825170354517889 235764756618877765888417)
                  ·
                    refine ⟨176823567464158324416313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 235764756618877765888417 176823567464158324416313)
                    ·
                      refine ⟨132617675598118743312235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 176823567464158324416313 132617675598118743312235)
                      ·
                        rfl

theorem cell23_258272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 4, 2, 2, 2, 2].length) (baseStart_258272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_258272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_258272 prefixEnd_258272 := by exact prefixLift 258272
  have htrace : WordTrace (prefixWord ++ tailWord_258272) baseStart_258272 baseEnd_258272 := by
    simpa [prefixWord, tailWord_258272, baseEnd_258272] using wordTrace_append hprefix tailTrace_258272
  have hstable : (prefixWord ++ tailWord_258272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_258272).length < 2 ^ (prefixWord ++ tailWord_258272).sum := by decide
  have hdescent : baseEnd_258272 < baseStart_258272 := by decide
  rcases family_descends (prefixWord ++ tailWord_258272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_258285 : List Nat := [1, 5, 1, 2, 3, 1, 1, 1, 2, 2, 4]
def baseStart_258285 : Nat := 118140960795 + 258285 * 2 ^ 59
def prefixEnd_258285 : Nat := 4983230072969 + 3 ^ 40 * 258285 * 2
def baseEnd_258285 : Nat := 132624350846627192449675

theorem tailTrace_258285 : CollatzResearch.WordTrace tailWord_258285 prefixEnd_258285 132624350846627192449675 := by
  unfold tailWord_258285
  simp only [CollatzResearch.WordTrace]
  refine ⟨9420427869285031411208309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6280285246190020940805539 9420427869285031411208309)
  ·
    refine ⟨883165112745471694800779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9420427869285031411208309 883165112745471694800779)
    ·
      refine ⟨1324747669118207542201169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 883165112745471694800779 1324747669118207542201169)
      ·
        refine ⟨993560751838655656650877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1324747669118207542201169 993560751838655656650877)
        ·
          refine ⟨372585281939495871244079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 993560751838655656650877 372585281939495871244079)
          ·
            refine ⟨558877922909243806866119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 372585281939495871244079 558877922909243806866119)
            ·
              refine ⟨838316884363865710299179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 558877922909243806866119 838316884363865710299179)
              ·
                refine ⟨1257475326545798565448769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 838316884363865710299179 1257475326545798565448769)
                ·
                  refine ⟨943106494909348924086577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1257475326545798565448769 943106494909348924086577)
                  ·
                    refine ⟨707329871182011693064933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 943106494909348924086577 707329871182011693064933)
                    ·
                      refine ⟨132624350846627192449675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 707329871182011693064933 132624350846627192449675)
                      ·
                        rfl

theorem cell23_258285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 1, 1, 2, 2, 4].length) (baseStart_258285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_258285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_258285 prefixEnd_258285 := by exact prefixLift 258285
  have htrace : WordTrace (prefixWord ++ tailWord_258285) baseStart_258285 baseEnd_258285 := by
    simpa [prefixWord, tailWord_258285, baseEnd_258285] using wordTrace_append hprefix tailTrace_258285
  have hstable : (prefixWord ++ tailWord_258285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_258285).length < 2 ^ (prefixWord ++ tailWord_258285).sum := by decide
  have hdescent : baseEnd_258285 < baseStart_258285 := by decide
  rcases family_descends (prefixWord ++ tailWord_258285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_258291 : List Nat := [1, 1, 1, 2, 2, 4, 2, 2, 1, 7]
def baseStart_258291 : Nat := 118140960795 + 258291 * 2 ^ 59
def prefixEnd_258291 : Nat := 4983230072969 + 3 ^ 40 * 258291 * 2
def baseEnd_258291 : Nat := 44209143910184722991549

theorem tailTrace_258291 : CollatzResearch.WordTrace tailWord_258291 prefixEnd_258291 44209143910184722991549 := by
  unfold tailWord_258291
  simp only [CollatzResearch.WordTrace]
  refine ⟨9420646707263294435926727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6280431138175529623951151 9420646707263294435926727)
  ·
    refine ⟨14130970060894941653890091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9420646707263294435926727 14130970060894941653890091)
    ·
      refine ⟨21196455091342412480835137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14130970060894941653890091 21196455091342412480835137)
      ·
        refine ⟨15897341318506809360626353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21196455091342412480835137 15897341318506809360626353)
        ·
          refine ⟨11923005988880107020469765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15897341318506809360626353 11923005988880107020469765)
          ·
            refine ⟨2235563622915020066338081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11923005988880107020469765 2235563622915020066338081)
            ·
              refine ⟨1676672717186265049753561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2235563622915020066338081 1676672717186265049753561)
              ·
                refine ⟨1257504537889698787315171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1676672717186265049753561 1257504537889698787315171)
                ·
                  refine ⟨1886256806834548180972757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1257504537889698787315171 1886256806834548180972757)
                  ·
                    refine ⟨44209143910184722991549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1886256806834548180972757 44209143910184722991549)
                    ·
                      rfl

theorem cell23_258291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 2, 1, 7].length) (baseStart_258291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_258291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_258291 prefixEnd_258291 := by exact prefixLift 258291
  have htrace : WordTrace (prefixWord ++ tailWord_258291) baseStart_258291 baseEnd_258291 := by
    simpa [prefixWord, tailWord_258291, baseEnd_258291] using wordTrace_append hprefix tailTrace_258291
  have hstable : (prefixWord ++ tailWord_258291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_258291).length < 2 ^ (prefixWord ++ tailWord_258291).sum := by decide
  have hdescent : baseEnd_258291 < baseStart_258291 := by decide
  rcases family_descends (prefixWord ++ tailWord_258291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_258301 : List Nat := [1, 4, 1, 1, 1, 1, 1, 4, 1, 1, 7]
def baseStart_258301 : Nat := 118140960795 + 258301 * 2 ^ 59
def prefixEnd_258301 : Nat := 4983230072969 + 3 ^ 40 * 258301 * 2
def baseEnd_258301 : Nat := 132632566537099129849601

theorem tailTrace_258301 : CollatzResearch.WordTrace tailWord_258301 prefixEnd_258301 132632566537099129849601 := by
  unfold tailWord_258301
  simp only [CollatzResearch.WordTrace]
  refine ⟨9421011437227066143790757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6280674291484710762527171 9421011437227066143790757)
  ·
    refine ⟨1766439644480074901960767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9421011437227066143790757 1766439644480074901960767)
    ·
      refine ⟨2649659466720112352941151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1766439644480074901960767 2649659466720112352941151)
      ·
        refine ⟨3974489200080168529411727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2649659466720112352941151 3974489200080168529411727)
        ·
          refine ⟨5961733800120252794117591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3974489200080168529411727 5961733800120252794117591)
          ·
            refine ⟨8942600700180379191176387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5961733800120252794117591 8942600700180379191176387)
            ·
              refine ⟨13413901050270568786764581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8942600700180379191176387 13413901050270568786764581)
              ·
                refine ⟨2515106446925731647518359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13413901050270568786764581 2515106446925731647518359)
                ·
                  refine ⟨3772659670388597471277539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2515106446925731647518359 3772659670388597471277539)
                  ·
                    refine ⟨5658989505582896206916309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3772659670388597471277539 5658989505582896206916309)
                    ·
                      refine ⟨132632566537099129849601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 5658989505582896206916309 132632566537099129849601)
                      ·
                        rfl

theorem cell23_258301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 4, 1, 1, 7].length) (baseStart_258301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_258301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_258301 prefixEnd_258301 := by exact prefixLift 258301
  have htrace : WordTrace (prefixWord ++ tailWord_258301) baseStart_258301 baseEnd_258301 := by
    simpa [prefixWord, tailWord_258301, baseEnd_258301] using wordTrace_append hprefix tailTrace_258301
  have hstable : (prefixWord ++ tailWord_258301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_258301).length < 2 ^ (prefixWord ++ tailWord_258301).sum := by decide
  have hdescent : baseEnd_258301 < baseStart_258301 := by decide
  rcases family_descends (prefixWord ++ tailWord_258301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_258328 : List Nat := [2, 1, 2, 3, 1, 2, 2, 1, 4, 1, 4]
def baseStart_258328 : Nat := 118140960795 + 258328 * 2 ^ 59
def prefixEnd_258328 : Nat := 4983230072969 + 3 ^ 40 * 258328 * 2
def baseEnd_258328 : Nat := 132646430514770524211977

theorem tailTrace_258328 : CollatzResearch.WordTrace tailWord_258328 prefixEnd_258328 132646430514770524211977 := by
  unfold tailWord_258328
  simp only [CollatzResearch.WordTrace]
  refine ⟨4710998104064624877511819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6281330805419499836682425 4710998104064624877511819)
  ·
    refine ⟨7066497156096937316267729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4710998104064624877511819 7066497156096937316267729)
    ·
      refine ⟨5299872867072702987200797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7066497156096937316267729 5299872867072702987200797)
      ·
        refine ⟨1987452325152263620200299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5299872867072702987200797 1987452325152263620200299)
        ·
          refine ⟨2981178487728395430300449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1987452325152263620200299 2981178487728395430300449)
          ·
            refine ⟨2235883865796296572725337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2981178487728395430300449 2235883865796296572725337)
            ·
              refine ⟨1676912899347222429544003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2235883865796296572725337 1676912899347222429544003)
              ·
                refine ⟨2515369349020833644316005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1676912899347222429544003 2515369349020833644316005)
                ·
                  refine ⟨471631752941406308309251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2515369349020833644316005 471631752941406308309251)
                  ·
                    refine ⟨707447629412109462463877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 471631752941406308309251 707447629412109462463877)
                    ·
                      refine ⟨132646430514770524211977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 707447629412109462463877 132646430514770524211977)
                      ·
                        rfl

theorem cell23_258328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 1, 4, 1, 4].length) (baseStart_258328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_258328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_258328 prefixEnd_258328 := by exact prefixLift 258328
  have htrace : WordTrace (prefixWord ++ tailWord_258328) baseStart_258328 baseEnd_258328 := by
    simpa [prefixWord, tailWord_258328, baseEnd_258328] using wordTrace_append hprefix tailTrace_258328
  have hstable : (prefixWord ++ tailWord_258328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_258328).length < 2 ^ (prefixWord ++ tailWord_258328).sum := by decide
  have hdescent : baseEnd_258328 < baseStart_258328 := by decide
  rcases family_descends (prefixWord ++ tailWord_258328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_258331 : List Nat := [1, 1, 1, 1, 1, 1, 6, 1, 2, 3, 5]
def baseStart_258331 : Nat := 118140960795 + 258331 * 2 ^ 59
def prefixEnd_258331 : Nat := 4983230072969 + 3 ^ 40 * 258331 * 2
def baseEnd_258331 : Nat := 132647970956734012474463

theorem tailTrace_258331 : CollatzResearch.WordTrace tailWord_258331 prefixEnd_258331 132647970956734012474463 := by
  unfold tailWord_258331
  simp only [CollatzResearch.WordTrace]
  refine ⟨9422105627118381267382847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6281403751412254178255231 9422105627118381267382847)
  ·
    refine ⟨14133158440677571901074271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9422105627118381267382847 14133158440677571901074271)
    ·
      refine ⟨21199737661016357851611407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14133158440677571901074271 21199737661016357851611407)
      ·
        refine ⟨31799606491524536777417111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21199737661016357851611407 31799606491524536777417111)
        ·
          refine ⟨47699409737286805166125667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31799606491524536777417111 47699409737286805166125667)
          ·
            refine ⟨71549114605930207749188501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47699409737286805166125667 71549114605930207749188501)
            ·
              refine ⟨3353864747152978488243211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 71549114605930207749188501 3353864747152978488243211)
              ·
                refine ⟨5030797120729467732364817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3353864747152978488243211 5030797120729467732364817)
                ·
                  refine ⟨3773097840547100799273613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5030797120729467732364817 3773097840547100799273613)
                  ·
                    refine ⟨1414911690205162799727605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3773097840547100799273613 1414911690205162799727605)
                    ·
                      refine ⟨132647970956734012474463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1414911690205162799727605 132647970956734012474463)
                      ·
                        rfl

theorem cell23_258331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 1, 2, 3, 5].length) (baseStart_258331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_258331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_258331 prefixEnd_258331 := by exact prefixLift 258331
  have htrace : WordTrace (prefixWord ++ tailWord_258331) baseStart_258331 baseEnd_258331 := by
    simpa [prefixWord, tailWord_258331, baseEnd_258331] using wordTrace_append hprefix tailTrace_258331
  have hstable : (prefixWord ++ tailWord_258331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_258331).length < 2 ^ (prefixWord ++ tailWord_258331).sum := by decide
  have hdescent : baseEnd_258331 < baseStart_258331 := by decide
  rcases family_descends (prefixWord ++ tailWord_258331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_258348 : List Nat := [2, 2, 1, 1, 1, 3, 3, 2, 1, 4, 3]
def baseStart_258348 : Nat := 118140960795 + 258348 * 2 ^ 59
def prefixEnd_258348 : Nat := 4983230072969 + 3 ^ 40 * 258348 * 2
def baseEnd_258348 : Nat := 132656700127860445961885

theorem tailTrace_258348 : CollatzResearch.WordTrace tailWord_258348 prefixEnd_258348 132656700127860445961885 := by
  unfold tailWord_258348
  simp only [CollatzResearch.WordTrace]
  refine ⟨4711362834028396585375849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6281817112037862113834465 4711362834028396585375849)
  ·
    refine ⟨3533522125521297439031887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4711362834028396585375849 3533522125521297439031887)
    ·
      refine ⟨5300283188281946158547831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3533522125521297439031887 5300283188281946158547831)
      ·
        refine ⟨7950424782422919237821747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5300283188281946158547831 7950424782422919237821747)
        ·
          refine ⟨11925637173634378856732621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7950424782422919237821747 11925637173634378856732621)
          ·
            refine ⟨4472113940112892071274733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11925637173634378856732621 4472113940112892071274733)
            ·
              refine ⟨1677042727542334526728025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4472113940112892071274733 1677042727542334526728025)
              ·
                refine ⟨1257782045656750895046019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1677042727542334526728025 1257782045656750895046019)
                ·
                  refine ⟨1886673068485126342569029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1257782045656750895046019 1886673068485126342569029)
                  ·
                    refine ⟨353751200340961189231693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1886673068485126342569029 353751200340961189231693)
                    ·
                      refine ⟨132656700127860445961885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 353751200340961189231693 132656700127860445961885)
                      ·
                        rfl

theorem cell23_258348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 4, 3].length) (baseStart_258348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_258348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_258348 prefixEnd_258348 := by exact prefixLift 258348
  have htrace : WordTrace (prefixWord ++ tailWord_258348) baseStart_258348 baseEnd_258348 := by
    simpa [prefixWord, tailWord_258348, baseEnd_258348] using wordTrace_append hprefix tailTrace_258348
  have hstable : (prefixWord ++ tailWord_258348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_258348).length < 2 ^ (prefixWord ++ tailWord_258348).sum := by decide
  have hdescent : baseEnd_258348 < baseStart_258348 := by decide
  rcases family_descends (prefixWord ++ tailWord_258348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_258389 : List Nat := [1, 3, 2, 2, 5, 1, 1, 1, 3, 4]
def baseStart_258389 : Nat := 118140960795 + 258389 * 2 ^ 59
def prefixEnd_258389 : Nat := 4983230072969 + 3 ^ 40 * 258389 * 2
def baseEnd_258389 : Nat := 44225917611564928516399

theorem tailTrace_258389 : CollatzResearch.WordTrace tailWord_258389 prefixEnd_258389 44225917611564928516399 := by
  unfold tailWord_258389
  simp only [CollatzResearch.WordTrace]
  refine ⟨9424221060908257172994221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6282814040605504781996147 9424221060908257172994221)
  ·
    refine ⟨3534082897840596439872833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9424221060908257172994221 3534082897840596439872833)
    ·
      refine ⟨2650562173380447329904625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3534082897840596439872833 2650562173380447329904625)
      ·
        refine ⟨1987921630035335497428469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2650562173380447329904625 1987921630035335497428469)
        ·
          refine ⟨186367652815812702883919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1987921630035335497428469 186367652815812702883919)
          ·
            refine ⟨279551479223719054325879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186367652815812702883919 279551479223719054325879)
            ·
              refine ⟨419327218835578581488819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 279551479223719054325879 419327218835578581488819)
              ·
                refine ⟨628990828253367872233229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 419327218835578581488819 628990828253367872233229)
                ·
                  refine ⟨235871560595012952087461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 628990828253367872233229 235871560595012952087461)
                  ·
                    refine ⟨44225917611564928516399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 235871560595012952087461 44225917611564928516399)
                    ·
                      rfl

theorem cell23_258389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 1, 1, 1, 3, 4].length) (baseStart_258389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_258389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_258389 prefixEnd_258389 := by exact prefixLift 258389
  have htrace : WordTrace (prefixWord ++ tailWord_258389) baseStart_258389 baseEnd_258389 := by
    simpa [prefixWord, tailWord_258389, baseEnd_258389] using wordTrace_append hprefix tailTrace_258389
  have hstable : (prefixWord ++ tailWord_258389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_258389).length < 2 ^ (prefixWord ++ tailWord_258389).sum := by decide
  have hdescent : baseEnd_258389 < baseStart_258389 := by decide
  rcases family_descends (prefixWord ++ tailWord_258389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_258402 : List Nat := [3, 3, 2, 1, 1, 2, 4, 1, 6]
def baseStart_258402 : Nat := 118140960795 + 258402 * 2 ^ 59
def prefixEnd_258402 : Nat := 4983230072969 + 3 ^ 40 * 258402 * 2
def baseEnd_258402 : Nat := 14742714231467026076293

theorem tailTrace_258402 : CollatzResearch.WordTrace tailWord_258402 prefixEnd_258402 14742714231467026076293 := by
  unfold tailWord_258402
  simp only [CollatzResearch.WordTrace]
  refine ⟨2356173802465290098304365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6283130139907440262144973 2356173802465290098304365)
  ·
    refine ⟨883565175924483786864137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2356173802465290098304365 883565175924483786864137)
    ·
      refine ⟨662673881943362840148103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 883565175924483786864137 662673881943362840148103)
      ·
        refine ⟨994010822915044260222155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 662673881943362840148103 994010822915044260222155)
        ·
          refine ⟨1491016234372566390333233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 994010822915044260222155 1491016234372566390333233)
          ·
            refine ⟨1118262175779424792749925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1491016234372566390333233 1118262175779424792749925)
            ·
              refine ⟨209674157958642148640611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1118262175779424792749925 209674157958642148640611)
              ·
                refine ⟨314511236937963222960917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 209674157958642148640611 314511236937963222960917)
                ·
                  refine ⟨14742714231467026076293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 314511236937963222960917 14742714231467026076293)
                  ·
                    rfl

theorem cell23_258402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 4, 1, 6].length) (baseStart_258402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_258402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_258402 prefixEnd_258402 := by exact prefixLift 258402
  have htrace : WordTrace (prefixWord ++ tailWord_258402) baseStart_258402 baseEnd_258402 := by
    simpa [prefixWord, tailWord_258402, baseEnd_258402] using wordTrace_append hprefix tailTrace_258402
  have hstable : (prefixWord ++ tailWord_258402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_258402).length < 2 ^ (prefixWord ++ tailWord_258402).sum := by decide
  have hdescent : baseEnd_258402 < baseStart_258402 := by decide
  rcases family_descends (prefixWord ++ tailWord_258402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_258446 : List Nat := [4, 1, 1, 4, 1, 2, 1, 4, 1, 1, 3]
def baseStart_258446 : Nat := 118140960795 + 258446 * 2 ^ 59
def prefixEnd_258446 : Nat := 4983230072969 + 3 ^ 40 * 258446 * 2
def baseEnd_258446 : Nat := 132707021232001062536435

theorem tailTrace_258446 : CollatzResearch.WordTrace tailWord_258446 prefixEnd_258446 132707021232001062536435 := by
  unfold tailWord_258446
  simp only [CollatzResearch.WordTrace]
  refine ⟨1178287502712719488477399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6284200014467837271879461 1178287502712719488477399)
  ·
    refine ⟨1767431254069079232716099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1178287502712719488477399 1767431254069079232716099)
    ·
      refine ⟨2651146881103618849074149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1767431254069079232716099 2651146881103618849074149)
      ·
        refine ⟨497090040206928534201403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2651146881103618849074149 497090040206928534201403)
        ·
          refine ⟨745635060310392801302105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 497090040206928534201403 745635060310392801302105)
          ·
            refine ⟨559226295232794600976579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 745635060310392801302105 559226295232794600976579)
            ·
              refine ⟨838839442849191901464869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 559226295232794600976579 838839442849191901464869)
              ·
                refine ⟨157282395534223481524663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 838839442849191901464869 157282395534223481524663)
                ·
                  refine ⟨235923593301335222286995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 157282395534223481524663 235923593301335222286995)
                  ·
                    refine ⟨353885389952002833430493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 235923593301335222286995 353885389952002833430493)
                    ·
                      refine ⟨132707021232001062536435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 353885389952002833430493 132707021232001062536435)
                      ·
                        rfl

theorem cell23_258446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 1, 4, 1, 1, 3].length) (baseStart_258446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_258446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_258446 prefixEnd_258446 := by exact prefixLift 258446
  have htrace : WordTrace (prefixWord ++ tailWord_258446) baseStart_258446 baseEnd_258446 := by
    simpa [prefixWord, tailWord_258446, baseEnd_258446] using wordTrace_append hprefix tailTrace_258446
  have hstable : (prefixWord ++ tailWord_258446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_258446).length < 2 ^ (prefixWord ++ tailWord_258446).sum := by decide
  have hdescent : baseEnd_258446 < baseStart_258446 := by decide
  rcases family_descends (prefixWord ++ tailWord_258446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_258455 : List Nat := [1, 1, 3, 3, 1, 1, 3, 2, 3, 2, 3]
def baseStart_258455 : Nat := 118140960795 + 258455 * 2 ^ 59
def prefixEnd_258455 : Nat := 4983230072969 + 3 ^ 40 * 258455 * 2
def baseEnd_258455 : Nat := 132711642557891527323893

theorem tailTrace_258455 : CollatzResearch.WordTrace tailWord_258455 prefixEnd_258455 132711642557891527323893 := by
  unfold tailWord_258455
  simp only [CollatzResearch.WordTrace]
  refine ⟨9426628278669150444896819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6284418852446100296597879 9426628278669150444896819)
  ·
    refine ⟨14139942418003725667345229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9426628278669150444896819 14139942418003725667345229)
    ·
      refine ⟨5302478406751397125254461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14139942418003725667345229 5302478406751397125254461)
      ·
        refine ⟨1988429402531773921970423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5302478406751397125254461 1988429402531773921970423)
        ·
          refine ⟨2982644103797660882955635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1988429402531773921970423 2982644103797660882955635)
          ·
            refine ⟨4473966155696491324433453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2982644103797660882955635 4473966155696491324433453)
            ·
              refine ⟨1677737308386184246662545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4473966155696491324433453 1677737308386184246662545)
              ·
                refine ⟨1258302981289638184996909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1677737308386184246662545 1258302981289638184996909)
                ·
                  refine ⟨471863617983614319373841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1258302981289638184996909 471863617983614319373841)
                  ·
                    refine ⟨353897713487710739530381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 471863617983614319373841 353897713487710739530381)
                    ·
                      refine ⟨132711642557891527323893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 353897713487710739530381 132711642557891527323893)
                      ·
                        rfl

theorem cell23_258455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 2, 3, 2, 3].length) (baseStart_258455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_258455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_258455 prefixEnd_258455 := by exact prefixLift 258455
  have htrace : WordTrace (prefixWord ++ tailWord_258455) baseStart_258455 baseEnd_258455 := by
    simpa [prefixWord, tailWord_258455, baseEnd_258455] using wordTrace_append hprefix tailTrace_258455
  have hstable : (prefixWord ++ tailWord_258455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_258455).length < 2 ^ (prefixWord ++ tailWord_258455).sum := by decide
  have hdescent : baseEnd_258455 < baseStart_258455 := by decide
  rcases family_descends (prefixWord ++ tailWord_258455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_258462 : List Nat := [4, 3, 1, 2, 1, 1, 1, 3, 1, 6]
def baseStart_258462 : Nat := 118140960795 + 258462 * 2 ^ 59
def prefixEnd_258462 : Nat := 4983230072969 + 3 ^ 40 * 258462 * 2
def baseEnd_258462 : Nat := 44238412307490999978787

theorem tailTrace_258462 : CollatzResearch.WordTrace tailWord_258462 prefixEnd_258462 44238412307490999978787 := by
  unfold tailWord_258462
  simp only [CollatzResearch.WordTrace]
  refine ⟨1178360448705473830050205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6284589059762527093601093 1178360448705473830050205)
  ·
    refine ⟨441885168264552686268827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1178360448705473830050205 441885168264552686268827)
    ·
      refine ⟨662827752396829029403241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 441885168264552686268827 662827752396829029403241)
      ·
        refine ⟨497120814297621772052431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 662827752396829029403241 497120814297621772052431)
        ·
          refine ⟨745681221446432658078647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 497120814297621772052431 745681221446432658078647)
          ·
            refine ⟨1118521832169648987117971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 745681221446432658078647 1118521832169648987117971)
            ·
              refine ⟨1677782748254473480676957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1118521832169648987117971 1677782748254473480676957)
              ·
                refine ⟨629168530595427555253859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1677782748254473480676957 629168530595427555253859)
                ·
                  refine ⟨943752795893141332880789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 629168530595427555253859 943752795893141332880789)
                  ·
                    refine ⟨44238412307490999978787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 943752795893141332880789 44238412307490999978787)
                    ·
                      rfl

theorem cell23_258462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 3, 1, 6].length) (baseStart_258462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_258462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_258462 prefixEnd_258462 := by exact prefixLift 258462
  have htrace : WordTrace (prefixWord ++ tailWord_258462) baseStart_258462 baseEnd_258462 := by
    simpa [prefixWord, tailWord_258462, baseEnd_258462] using wordTrace_append hprefix tailTrace_258462
  have hstable : (prefixWord ++ tailWord_258462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_258462).length < 2 ^ (prefixWord ++ tailWord_258462).sum := by decide
  have hdescent : baseEnd_258462 < baseStart_258462 := by decide
  rcases family_descends (prefixWord ++ tailWord_258462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_258489 : List Nat := [1, 2, 1, 4, 3, 1, 4, 1, 1, 2, 3]
def baseStart_258489 : Nat := 118140960795 + 258489 * 2 ^ 59
def prefixEnd_258489 : Nat := 4983230072969 + 3 ^ 40 * 258489 * 2
def baseEnd_258489 : Nat := 132729100900144394298737

theorem tailTrace_258489 : CollatzResearch.WordTrace tailWord_258489 prefixEnd_258489 132729100900144394298737 := by
  unfold tailWord_258489
  simp only [CollatzResearch.WordTrace]
  refine ⟨9427868360545974251634521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6285245573697316167756347 9427868360545974251634521)
  ·
    refine ⟨7070901270409480688725891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9427868360545974251634521 7070901270409480688725891)
    ·
      refine ⟨10606351905614221033088837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7070901270409480688725891 10606351905614221033088837)
      ·
        refine ⟨1988690982302666443704157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10606351905614221033088837 1988690982302666443704157)
        ·
          refine ⟨745759118363499916389059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1988690982302666443704157 745759118363499916389059)
          ·
            refine ⟨1118638677545249874583589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 745759118363499916389059 1118638677545249874583589)
            ·
              refine ⟨209744752039734351484423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1118638677545249874583589 209744752039734351484423)
              ·
                refine ⟨314617128059601527226635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 209744752039734351484423 314617128059601527226635)
                ·
                  refine ⟨471925692089402290839953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 314617128059601527226635 471925692089402290839953)
                  ·
                    refine ⟨353944269067051718129965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 471925692089402290839953 353944269067051718129965)
                    ·
                      refine ⟨132729100900144394298737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 353944269067051718129965 132729100900144394298737)
                      ·
                        rfl

theorem cell23_258489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 4, 1, 1, 2, 3].length) (baseStart_258489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_258489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_258489 prefixEnd_258489 := by exact prefixLift 258489
  have htrace : WordTrace (prefixWord ++ tailWord_258489) baseStart_258489 baseEnd_258489 := by
    simpa [prefixWord, tailWord_258489, baseEnd_258489] using wordTrace_append hprefix tailTrace_258489
  have hstable : (prefixWord ++ tailWord_258489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_258489).length < 2 ^ (prefixWord ++ tailWord_258489).sum := by decide
  have hdescent : baseEnd_258489 < baseStart_258489 := by decide
  rcases family_descends (prefixWord ++ tailWord_258489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_258529 : List Nat := [1, 2, 3, 1, 2, 2, 4, 2, 1, 3, 2]
def baseStart_258529 : Nat := 118140960795 + 258529 * 2 ^ 59
def prefixEnd_258529 : Nat := 4983230072969 + 3 ^ 40 * 258529 * 2
def baseEnd_258529 : Nat := 132749640126324237798553

theorem tailTrace_258529 : CollatzResearch.WordTrace tailWord_258529 prefixEnd_258529 132749640126324237798553 := by
  unfold tailWord_258529
  simp only [CollatzResearch.WordTrace]
  refine ⟨9429327280401061083090641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6286218186934040722060427 9429327280401061083090641)
  ·
    refine ⟨7071995460300795812317981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9429327280401061083090641 7071995460300795812317981)
    ·
      refine ⟨2651998297612798429619243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7071995460300795812317981 2651998297612798429619243)
      ·
        refine ⟨3977997446419197644428865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2651998297612798429619243 3977997446419197644428865)
        ·
          refine ⟨2983498084814398233321649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3977997446419197644428865 2983498084814398233321649)
          ·
            refine ⟨2237623563610798674991237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2983498084814398233321649 2237623563610798674991237)
            ·
              refine ⟨419554418177024751560857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2237623563610798674991237 419554418177024751560857)
              ·
                refine ⟨314665813632768563670643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 419554418177024751560857 314665813632768563670643)
                ·
                  refine ⟨471998720449152845505965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 314665813632768563670643 471998720449152845505965)
                  ·
                    refine ⟨176999520168432317064737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 471998720449152845505965 176999520168432317064737)
                    ·
                      refine ⟨132749640126324237798553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 176999520168432317064737 132749640126324237798553)
                      ·
                        rfl

theorem cell23_258529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 4, 2, 1, 3, 2].length) (baseStart_258529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_258529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_258529 prefixEnd_258529 := by exact prefixLift 258529
  have htrace : WordTrace (prefixWord ++ tailWord_258529) baseStart_258529 baseEnd_258529 := by
    simpa [prefixWord, tailWord_258529, baseEnd_258529] using wordTrace_append hprefix tailTrace_258529
  have hstable : (prefixWord ++ tailWord_258529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_258529).length < 2 ^ (prefixWord ++ tailWord_258529).sum := by decide
  have hdescent : baseEnd_258529 < baseStart_258529 := by decide
  rcases family_descends (prefixWord ++ tailWord_258529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_258545 : List Nat := [1, 2, 2, 2, 3, 1, 3, 1, 2, 1, 5]
def baseStart_258545 : Nat := 118140960795 + 258545 * 2 ^ 59
def prefixEnd_258545 : Nat := 4983230072969 + 3 ^ 40 * 258545 * 2
def baseEnd_258545 : Nat := 132757855816796175198479

theorem tailTrace_258545 : CollatzResearch.WordTrace tailWord_258545 prefixEnd_258545 132757855816796175198479 := by
  unfold tailWord_258545
  simp only [CollatzResearch.WordTrace]
  refine ⟨9429910848343095815673089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6286607232228730543782059 9429910848343095815673089)
  ·
    refine ⟨7072433136257321861754817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9429910848343095815673089 7072433136257321861754817)
    ·
      refine ⟨5304324852192991396316113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7072433136257321861754817 5304324852192991396316113)
      ·
        refine ⟨3978243639144743547237085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5304324852192991396316113 3978243639144743547237085)
        ·
          refine ⟨1491841364679278830213907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3978243639144743547237085 1491841364679278830213907)
          ·
            refine ⟨2237762047018918245320861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1491841364679278830213907 2237762047018918245320861)
            ·
              refine ⟨839160767632094341995323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2237762047018918245320861 839160767632094341995323)
              ·
                refine ⟨1258741151448141512992985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 839160767632094341995323 1258741151448141512992985)
                ·
                  refine ⟨944055863586106134744739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1258741151448141512992985 944055863586106134744739)
                  ·
                    refine ⟨1416083795379159202117109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 944055863586106134744739 1416083795379159202117109)
                    ·
                      refine ⟨132757855816796175198479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1416083795379159202117109 132757855816796175198479)
                      ·
                        rfl

theorem cell23_258545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 3, 1, 2, 1, 5].length) (baseStart_258545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_258545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_258545 prefixEnd_258545 := by exact prefixLift 258545
  have htrace : WordTrace (prefixWord ++ tailWord_258545) baseStart_258545 baseEnd_258545 := by
    simpa [prefixWord, tailWord_258545, baseEnd_258545] using wordTrace_append hprefix tailTrace_258545
  have hstable : (prefixWord ++ tailWord_258545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_258545).length < 2 ^ (prefixWord ++ tailWord_258545).sum := by decide
  have hdescent : baseEnd_258545 < baseStart_258545 := by decide
  rcases family_descends (prefixWord ++ tailWord_258545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_258559 : List Nat := [1, 1, 2, 2, 1, 2, 4, 4, 2, 2, 2]
def baseStart_258559 : Nat := 118140960795 + 258559 * 2 ^ 59
def prefixEnd_258559 : Nat := 4983230072969 + 3 ^ 40 * 258559 * 2
def baseEnd_258559 : Nat := 132765044545959120423415

theorem tailTrace_258559 : CollatzResearch.WordTrace tailWord_258559 prefixEnd_258559 132765044545959120423415 := by
  unfold tailWord_258559
  simp only [CollatzResearch.WordTrace]
  refine ⟨9430421470292376206682731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6286947646861584137788487 9430421470292376206682731)
  ·
    refine ⟨14145632205438564310024097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9430421470292376206682731 14145632205438564310024097)
    ·
      refine ⟨10609224154078923232518073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14145632205438564310024097 10609224154078923232518073)
      ·
        refine ⟨7956918115559192424388555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10609224154078923232518073 7956918115559192424388555)
        ·
          refine ⟨11935377173338788636582833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7956918115559192424388555 11935377173338788636582833)
          ·
            refine ⟨8951532880004091477437125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11935377173338788636582833 8951532880004091477437125)
            ·
              refine ⟨1678412415000767152019461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8951532880004091477437125 1678412415000767152019461)
              ·
                refine ⟨314702327812643841003649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1678412415000767152019461 314702327812643841003649)
                ·
                  refine ⟨236026745859482880752737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 314702327812643841003649 236026745859482880752737)
                  ·
                    refine ⟨177020059394612160564553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 236026745859482880752737 177020059394612160564553)
                    ·
                      refine ⟨132765044545959120423415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 177020059394612160564553 132765044545959120423415)
                      ·
                        rfl

theorem cell23_258559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 4, 2, 2, 2].length) (baseStart_258559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_258559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_258559 prefixEnd_258559 := by exact prefixLift 258559
  have htrace : WordTrace (prefixWord ++ tailWord_258559) baseStart_258559 baseEnd_258559 := by
    simpa [prefixWord, tailWord_258559, baseEnd_258559] using wordTrace_append hprefix tailTrace_258559
  have hstable : (prefixWord ++ tailWord_258559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_258559).length < 2 ^ (prefixWord ++ tailWord_258559).sum := by decide
  have hdescent : baseEnd_258559 < baseStart_258559 := by decide
  rcases family_descends (prefixWord ++ tailWord_258559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_258565 : List Nat := [1, 3, 1, 1, 2, 2, 5, 1, 7]
def baseStart_258565 : Nat := 118140960795 + 258565 * 2 ^ 59
def prefixEnd_258565 : Nat := 4983230072969 + 3 ^ 40 * 258565 * 2
def baseEnd_258565 : Nat := 14752013936654010772043

theorem tailTrace_258565 : CollatzResearch.WordTrace tailWord_258565 prefixEnd_258565 14752013936654010772043 := by
  unfold tailWord_258565
  simp only [CollatzResearch.WordTrace]
  refine ⟨9430640308270639231401149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6287093538847092820934099 9430640308270639231401149)
  ·
    refine ⟨3536490115601489711775431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9430640308270639231401149 3536490115601489711775431)
    ·
      refine ⟨5304735173402234567663147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3536490115601489711775431 5304735173402234567663147)
      ·
        refine ⟨7957102760103351851494721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5304735173402234567663147 7957102760103351851494721)
        ·
          refine ⟨5967827070077513888621041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7957102760103351851494721 5967827070077513888621041)
          ·
            refine ⟨4475870302558135416465781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5967827070077513888621041 4475870302558135416465781)
            ·
              refine ⟨419612840864825195293667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4475870302558135416465781 419612840864825195293667)
              ·
                refine ⟨629419261297237792940501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 419612840864825195293667 629419261297237792940501)
                ·
                  refine ⟨14752013936654010772043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 629419261297237792940501 14752013936654010772043)
                  ·
                    rfl

theorem cell23_258565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 5, 1, 7].length) (baseStart_258565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_258565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_258565 prefixEnd_258565 := by exact prefixLift 258565
  have htrace : WordTrace (prefixWord ++ tailWord_258565) baseStart_258565 baseEnd_258565 := by
    simpa [prefixWord, tailWord_258565, baseEnd_258565] using wordTrace_append hprefix tailTrace_258565
  have hstable : (prefixWord ++ tailWord_258565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_258565).length < 2 ^ (prefixWord ++ tailWord_258565).sum := by decide
  have hdescent : baseEnd_258565 < baseStart_258565 := by decide
  rcases family_descends (prefixWord ++ tailWord_258565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_258672 : List Nat := [2, 1, 1, 1, 7, 1, 1, 1, 8]
def baseStart_258672 : Nat := 118140960795 + 258672 * 2 ^ 59
def prefixEnd_258672 : Nat := 4983230072969 + 3 ^ 40 * 258672 * 2
def baseEnd_258672 : Nat := 14758118651101908701155

theorem tailTrace_258672 : CollatzResearch.WordTrace tailWord_258672 prefixEnd_258672 14758118651101908701155 := by
  unfold tailWord_258672
  simp only [CollatzResearch.WordTrace]
  refine ⟨4717271459441498252773135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6289695279255331003697513 4717271459441498252773135)
  ·
    refine ⟨7075907189162247379159703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4717271459441498252773135 7075907189162247379159703)
    ·
      refine ⟨10613860783743371068739555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7075907189162247379159703 10613860783743371068739555)
      ·
        refine ⟨15920791175615056603109333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10613860783743371068739555 15920791175615056603109333)
        ·
          refine ⟨373143543178477889135375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 15920791175615056603109333 373143543178477889135375)
          ·
            refine ⟨559715314767716833703063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 373143543178477889135375 559715314767716833703063)
            ·
              refine ⟨839572972151575250554595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 559715314767716833703063 839572972151575250554595)
              ·
                refine ⟨1259359458227362875831893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 839572972151575250554595 1259359458227362875831893)
                ·
                  refine ⟨14758118651101908701155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1259359458227362875831893 14758118651101908701155)
                  ·
                    rfl

theorem cell23_258672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 1, 1, 8].length) (baseStart_258672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_258672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_258672 prefixEnd_258672 := by exact prefixLift 258672
  have htrace : WordTrace (prefixWord ++ tailWord_258672) baseStart_258672 baseEnd_258672 := by
    simpa [prefixWord, tailWord_258672, baseEnd_258672] using wordTrace_append hprefix tailTrace_258672
  have hstable : (prefixWord ++ tailWord_258672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_258672).length < 2 ^ (prefixWord ++ tailWord_258672).sum := by decide
  have hdescent : baseEnd_258672 < baseStart_258672 := by decide
  rcases family_descends (prefixWord ++ tailWord_258672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_258689 : List Nat := [1, 2, 4, 2, 1, 1, 5, 1, 6]
def baseStart_258689 : Nat := 118140960795 + 258689 * 2 ^ 59
def prefixEnd_258689 : Nat := 4983230072969 + 3 ^ 40 * 258689 * 2
def baseEnd_258689 : Nat := 14759088559004845755313

theorem tailTrace_258689 : CollatzResearch.WordTrace tailWord_258689 prefixEnd_258689 14759088559004845755313 := by
  unfold tailWord_258689
  simp only [CollatzResearch.WordTrace]
  refine ⟨9435162959821408408915121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6290108639880938939276747 9435162959821408408915121)
  ·
    refine ⟨7076372219866056306686341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9435162959821408408915121 7076372219866056306686341)
    ·
      refine ⟨1326819791224885557503689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7076372219866056306686341 1326819791224885557503689)
      ·
        refine ⟨995114843418664168127767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1326819791224885557503689 995114843418664168127767)
        ·
          refine ⟨1492672265127996252191651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 995114843418664168127767 1492672265127996252191651)
          ·
            refine ⟨2239008397691994378287477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1492672265127996252191651 2239008397691994378287477)
            ·
              refine ⟨209907037283624472964451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2239008397691994378287477 209907037283624472964451)
              ·
                refine ⟨314860555925436709446677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 209907037283624472964451 314860555925436709446677)
                ·
                  refine ⟨14759088559004845755313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 314860555925436709446677 14759088559004845755313)
                  ·
                    rfl

theorem cell23_258689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 5, 1, 6].length) (baseStart_258689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_258689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_258689 prefixEnd_258689 := by exact prefixLift 258689
  have htrace : WordTrace (prefixWord ++ tailWord_258689) baseStart_258689 baseEnd_258689 := by
    simpa [prefixWord, tailWord_258689, baseEnd_258689] using wordTrace_append hprefix tailTrace_258689
  have hstable : (prefixWord ++ tailWord_258689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_258689).length < 2 ^ (prefixWord ++ tailWord_258689).sum := by decide
  have hdescent : baseEnd_258689 < baseStart_258689 := by decide
  rcases family_descends (prefixWord ++ tailWord_258689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_258715 : List Nat := [1, 1, 1, 1, 1, 1, 2, 2, 7, 6]
def baseStart_258715 : Nat := 118140960795 + 258715 * 2 ^ 59
def prefixEnd_258715 : Nat := 4983230072969 + 3 ^ 40 * 258715 * 2
def baseEnd_258715 : Nat := 44281715842686836690899

theorem tailTrace_258715 : CollatzResearch.WordTrace tailWord_258715 prefixEnd_258715 44281715842686836690899 := by
  unfold tailWord_258715
  simp only [CollatzResearch.WordTrace]
  refine ⟨9436111257727214849361599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6290740838484809899574399 9436111257727214849361599)
  ·
    refine ⟨14154166886590822274042399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9436111257727214849361599 14154166886590822274042399)
    ·
      refine ⟨21231250329886233411063599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14154166886590822274042399 21231250329886233411063599)
      ·
        refine ⟨31846875494829350116595399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21231250329886233411063599 31846875494829350116595399)
        ·
          refine ⟨47770313242244025174893099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31846875494829350116595399 47770313242244025174893099)
          ·
            refine ⟨71655469863366037762339649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47770313242244025174893099 71655469863366037762339649)
            ·
              refine ⟨53741602397524528321754737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71655469863366037762339649 53741602397524528321754737)
              ·
                refine ⟨40306201798143396241316053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53741602397524528321754737 40306201798143396241316053)
                ·
                  refine ⟨944676604643985849405845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 40306201798143396241316053 944676604643985849405845)
                  ·
                    refine ⟨44281715842686836690899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 944676604643985849405845 44281715842686836690899)
                    ·
                      rfl

theorem cell23_258715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 7, 6].length) (baseStart_258715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_258715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_258715 prefixEnd_258715 := by exact prefixLift 258715
  have htrace : WordTrace (prefixWord ++ tailWord_258715) baseStart_258715 baseEnd_258715 := by
    simpa [prefixWord, tailWord_258715, baseEnd_258715] using wordTrace_append hprefix tailTrace_258715
  have hstable : (prefixWord ++ tailWord_258715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_258715).length < 2 ^ (prefixWord ++ tailWord_258715).sum := by decide
  have hdescent : baseEnd_258715 < baseStart_258715 := by decide
  rcases family_descends (prefixWord ++ tailWord_258715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_258733 : List Nat := [1, 5, 2, 1, 1, 4, 1, 1, 3, 1, 3]
def baseStart_258733 : Nat := 118140960795 + 258733 * 2 ^ 59
def prefixEnd_258733 : Nat := 4983230072969 + 3 ^ 40 * 258733 * 2
def baseEnd_258733 : Nat := 132854390179841439647615

theorem tailTrace_258733 : CollatzResearch.WordTrace tailWord_258733 prefixEnd_258733 132854390179841439647615 := by
  unfold tailWord_258733
  simp only [CollatzResearch.WordTrace]
  refine ⟨9436767771662003923516853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6291178514441335949011235 9436767771662003923516853)
  ·
    refine ⟨884696978593312867829705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9436767771662003923516853 884696978593312867829705)
    ·
      refine ⟨663522733944984650872279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 884696978593312867829705 663522733944984650872279)
      ·
        refine ⟨995284100917476976308419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 663522733944984650872279 995284100917476976308419)
        ·
          refine ⟨1492926151376215464462629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 995284100917476976308419 1492926151376215464462629)
          ·
            refine ⟨279923653383040399586743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1492926151376215464462629 279923653383040399586743)
            ·
              refine ⟨419885480074560599380115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 279923653383040399586743 419885480074560599380115)
              ·
                refine ⟨629828220111840899070173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 419885480074560599380115 629828220111840899070173)
                ·
                  refine ⟨236185582541940337151315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 629828220111840899070173 236185582541940337151315)
                  ·
                    refine ⟨354278373812910505726973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 236185582541940337151315 354278373812910505726973)
                    ·
                      refine ⟨132854390179841439647615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 354278373812910505726973 132854390179841439647615)
                      ·
                        rfl

theorem cell23_258733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 4, 1, 1, 3, 1, 3].length) (baseStart_258733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_258733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_258733 prefixEnd_258733 := by exact prefixLift 258733
  have htrace : WordTrace (prefixWord ++ tailWord_258733) baseStart_258733 baseEnd_258733 := by
    simpa [prefixWord, tailWord_258733, baseEnd_258733] using wordTrace_append hprefix tailTrace_258733
  have hstable : (prefixWord ++ tailWord_258733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_258733).length < 2 ^ (prefixWord ++ tailWord_258733).sum := by decide
  have hdescent : baseEnd_258733 < baseStart_258733 := by decide
  rcases family_descends (prefixWord ++ tailWord_258733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_258752 : List Nat := [2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 6]
def baseStart_258752 : Nat := 118140960795 + 258752 * 2 ^ 59
def prefixEnd_258752 : Nat := 4983230072969 + 3 ^ 40 * 258752 * 2
def baseEnd_258752 : Nat := 132864146312276865310027

theorem tailTrace_258752 : CollatzResearch.WordTrace tailWord_258752 prefixEnd_258752 132864146312276865310027 := by
  unfold tailWord_258752
  simp only [CollatzResearch.WordTrace]
  refine ⟨4718730379296585084229255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6291640505728780112305673 4718730379296585084229255)
  ·
    refine ⟨7078095568944877626343883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4718730379296585084229255 7078095568944877626343883)
    ·
      refine ⟨10617143353417316439515825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7078095568944877626343883 10617143353417316439515825)
      ·
        refine ⟨7962857515062987329636869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10617143353417316439515825 7962857515062987329636869)
        ·
          refine ⟨1493035784074310124306913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7962857515062987329636869 1493035784074310124306913)
          ·
            refine ⟨1119776838055732593230185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1493035784074310124306913 1119776838055732593230185)
            ·
              refine ⟨839832628541799444922639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1119776838055732593230185 839832628541799444922639)
              ·
                refine ⟨1259748942812699167383959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 839832628541799444922639 1259748942812699167383959)
                ·
                  refine ⟨1889623414219048751075939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1259748942812699167383959 1889623414219048751075939)
                  ·
                    refine ⟨2834435121328573126613909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1889623414219048751075939 2834435121328573126613909)
                    ·
                      refine ⟨132864146312276865310027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 2834435121328573126613909 132864146312276865310027)
                      ·
                        rfl

theorem cell23_258752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 6].length) (baseStart_258752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_258752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_258752 prefixEnd_258752 := by exact prefixLift 258752
  have htrace : WordTrace (prefixWord ++ tailWord_258752) baseStart_258752 baseEnd_258752 := by
    simpa [prefixWord, tailWord_258752, baseEnd_258752] using wordTrace_append hprefix tailTrace_258752
  have hstable : (prefixWord ++ tailWord_258752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_258752).length < 2 ^ (prefixWord ++ tailWord_258752).sum := by decide
  have hdescent : baseEnd_258752 < baseStart_258752 := by decide
  rcases family_descends (prefixWord ++ tailWord_258752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_258756 : List Nat := [2, 3, 3, 1, 1, 2, 3, 2, 1, 1, 4]
def baseStart_258756 : Nat := 118140960795 + 258756 * 2 ^ 59
def prefixEnd_258756 : Nat := 4983230072969 + 3 ^ 40 * 258756 * 2
def baseEnd_258756 : Nat := 132866200234894849660009

theorem tailTrace_258756 : CollatzResearch.WordTrace tailWord_258756 prefixEnd_258756 132866200234894849660009 := by
  unfold tailWord_258756
  simp only [CollatzResearch.WordTrace]
  refine ⟨4718803325289339425802061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6291737767052452567736081 4718803325289339425802061)
  ·
    refine ⟨1769551246983502284675773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4718803325289339425802061 1769551246983502284675773)
    ·
      refine ⟨663581717618813356753415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1769551246983502284675773 663581717618813356753415)
      ·
        refine ⟨995372576428220035130123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 663581717618813356753415 995372576428220035130123)
        ·
          refine ⟨1493058864642330052695185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 995372576428220035130123 1493058864642330052695185)
          ·
            refine ⟨1119794148481747539521389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1493058864642330052695185 1119794148481747539521389)
            ·
              refine ⟨419922805680655327320521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1119794148481747539521389 419922805680655327320521)
              ·
                refine ⟨314942104260491495490391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 419922805680655327320521 314942104260491495490391)
                ·
                  refine ⟨472413156390737243235587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 314942104260491495490391 472413156390737243235587)
                  ·
                    refine ⟨708619734586105864853381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 472413156390737243235587 708619734586105864853381)
                    ·
                      refine ⟨132866200234894849660009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 708619734586105864853381 132866200234894849660009)
                      ·
                        rfl

theorem cell23_258756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 3, 2, 1, 1, 4].length) (baseStart_258756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_258756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_258756 prefixEnd_258756 := by exact prefixLift 258756
  have htrace : WordTrace (prefixWord ++ tailWord_258756) baseStart_258756 baseEnd_258756 := by
    simpa [prefixWord, tailWord_258756, baseEnd_258756] using wordTrace_append hprefix tailTrace_258756
  have hstable : (prefixWord ++ tailWord_258756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_258756).length < 2 ^ (prefixWord ++ tailWord_258756).sum := by decide
  have hdescent : baseEnd_258756 < baseStart_258756 := by decide
  rcases family_descends (prefixWord ++ tailWord_258756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_258759 : List Nat := [1, 1, 4, 1, 1, 1, 2, 6, 1, 2, 3]
def baseStart_258759 : Nat := 118140960795 + 258759 * 2 ^ 59
def prefixEnd_258759 : Nat := 4983230072969 + 3 ^ 40 * 258759 * 2
def baseEnd_258759 : Nat := 132867740676858337922495

theorem tailTrace_258759 : CollatzResearch.WordTrace tailWord_258759 prefixEnd_258759 132867740676858337922495 := by
  unfold tailWord_258759
  simp only [CollatzResearch.WordTrace]
  refine ⟨9437716069567810363963331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6291810713045206909308887 9437716069567810363963331)
  ·
    refine ⟨14156574104351715545944997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9437716069567810363963331 14156574104351715545944997)
    ·
      refine ⟨2654357644565946664864687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14156574104351715545944997 2654357644565946664864687)
      ·
        refine ⟨3981536466848919997297031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2654357644565946664864687 3981536466848919997297031)
        ·
          refine ⟨5972304700273379995945547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3981536466848919997297031 5972304700273379995945547)
          ·
            refine ⟨8958457050410069993918321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5972304700273379995945547 8958457050410069993918321)
            ·
              refine ⟨6718842787807552495438741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8958457050410069993918321 6718842787807552495438741)
              ·
                refine ⟨314945755678479023223691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 6718842787807552495438741 314945755678479023223691)
                ·
                  refine ⟨472418633517718534835537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 314945755678479023223691 472418633517718534835537)
                  ·
                    refine ⟨354313975138288901126653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 472418633517718534835537 354313975138288901126653)
                    ·
                      refine ⟨132867740676858337922495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 354313975138288901126653 132867740676858337922495)
                      ·
                        rfl

theorem cell23_258759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 6, 1, 2, 3].length) (baseStart_258759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_258759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_258759 prefixEnd_258759 := by exact prefixLift 258759
  have htrace : WordTrace (prefixWord ++ tailWord_258759) baseStart_258759 baseEnd_258759 := by
    simpa [prefixWord, tailWord_258759, baseEnd_258759] using wordTrace_append hprefix tailTrace_258759
  have hstable : (prefixWord ++ tailWord_258759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_258759).length < 2 ^ (prefixWord ++ tailWord_258759).sum := by decide
  have hdescent : baseEnd_258759 < baseStart_258759 := by decide
  rcases family_descends (prefixWord ++ tailWord_258759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_258762 : List Nat := [3, 1, 2, 1, 4, 1, 2, 9]
def baseStart_258762 : Nat := 118140960795 + 258762 * 2 ^ 59
def prefixEnd_258762 : Nat := 4983230072969 + 3 ^ 40 * 258762 * 2
def baseEnd_258762 : Nat := 4921084485882289858703

theorem tailTrace_258762 : CollatzResearch.WordTrace tailWord_258762 prefixEnd_258762 4921084485882289858703 := by
  unfold tailWord_258762
  simp only [CollatzResearch.WordTrace]
  refine ⟨2359456372139235469080635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6291883659037961250881693 2359456372139235469080635)
  ·
    refine ⟨3539184558208853203620953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2359456372139235469080635 3539184558208853203620953)
    ·
      refine ⟨2654388418656639902715715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3539184558208853203620953 2654388418656639902715715)
      ·
        refine ⟨3981582627984959854073573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2654388418656639902715715 3981582627984959854073573)
        ·
          refine ⟨746546742747179972638795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3981582627984959854073573 746546742747179972638795)
          ·
            refine ⟨1119820114120769958958193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 746546742747179972638795 1119820114120769958958193)
            ·
              refine ⟨839865085590577469218645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1119820114120769958958193 839865085590577469218645)
              ·
                refine ⟨4921084485882289858703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 839865085590577469218645 4921084485882289858703)
                ·
                  rfl

theorem cell23_258762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 2, 9].length) (baseStart_258762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_258762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_258762 prefixEnd_258762 := by exact prefixLift 258762
  have htrace : WordTrace (prefixWord ++ tailWord_258762) baseStart_258762 baseEnd_258762 := by
    simpa [prefixWord, tailWord_258762, baseEnd_258762] using wordTrace_append hprefix tailTrace_258762
  have hstable : (prefixWord ++ tailWord_258762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_258762).length < 2 ^ (prefixWord ++ tailWord_258762).sum := by decide
  have hdescent : baseEnd_258762 < baseStart_258762 := by decide
  rcases family_descends (prefixWord ++ tailWord_258762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_258806 : List Nat := [5, 1, 1, 1, 1, 2, 4, 1, 1, 3, 3]
def baseStart_258806 : Nat := 118140960795 + 258806 * 2 ^ 59
def prefixEnd_258806 : Nat := 4983230072969 + 3 ^ 40 * 258806 * 2
def baseEnd_258806 : Nat := 132891874267619654034779

theorem tailTrace_258806 : CollatzResearch.WordTrace tailWord_258806 prefixEnd_258806 132891874267619654034779 := by
  unfold tailWord_258806
  simp only [CollatzResearch.WordTrace]
  refine ⟨589964393774846086932767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6292953533598358260616181 589964393774846086932767)
  ·
    refine ⟨884946590662269130399151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 589964393774846086932767 884946590662269130399151)
    ·
      refine ⟨1327419885993403695598727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 884946590662269130399151 1327419885993403695598727)
      ·
        refine ⟨1991129828990105543398091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1327419885993403695598727 1991129828990105543398091)
        ·
          refine ⟨2986694743485158315097137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1991129828990105543398091 2986694743485158315097137)
          ·
            refine ⟨2240021057613868736322853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2986694743485158315097137 2240021057613868736322853)
            ·
              refine ⟨420003948302600388060535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2240021057613868736322853 420003948302600388060535)
              ·
                refine ⟨630005922453900582090803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 420003948302600388060535 630005922453900582090803)
                ·
                  refine ⟨945008883680850873136205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 630005922453900582090803 945008883680850873136205)
                  ·
                    refine ⟨354378331380319077426077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 945008883680850873136205 354378331380319077426077)
                    ·
                      refine ⟨132891874267619654034779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 354378331380319077426077 132891874267619654034779)
                      ·
                        rfl

theorem cell23_258806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 4, 1, 1, 3, 3].length) (baseStart_258806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_258806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_258806 prefixEnd_258806 := by exact prefixLift 258806
  have htrace : WordTrace (prefixWord ++ tailWord_258806) baseStart_258806 baseEnd_258806 := by
    simpa [prefixWord, tailWord_258806, baseEnd_258806] using wordTrace_append hprefix tailTrace_258806
  have hstable : (prefixWord ++ tailWord_258806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_258806).length < 2 ^ (prefixWord ++ tailWord_258806).sum := by decide
  have hdescent : baseEnd_258806 < baseStart_258806 := by decide
  rcases family_descends (prefixWord ++ tailWord_258806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_258833 : List Nat := [1, 2, 2, 1, 1, 3, 6, 1, 1, 3, 2]
def baseStart_258833 : Nat := 118140960795 + 258833 * 2 ^ 59
def prefixEnd_258833 : Nat := 4983230072969 + 3 ^ 40 * 258833 * 2
def baseEnd_258833 : Nat := 132905738245291048397155

theorem tailTrace_258833 : CollatzResearch.WordTrace tailWord_258833 prefixEnd_258833 132905738245291048397155 := by
  unfold tailWord_258833
  simp only [CollatzResearch.WordTrace]
  refine ⟨9440415071299721002157153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6293610047533147334771435 9440415071299721002157153)
  ·
    refine ⟨7080311303474790751617865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9440415071299721002157153 7080311303474790751617865)
    ·
      refine ⟨5310233477606093063713399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7080311303474790751617865 5310233477606093063713399)
      ·
        refine ⟨7965350216409139595570099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5310233477606093063713399 7965350216409139595570099)
        ·
          refine ⟨11948025324613709393355149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7965350216409139595570099 11948025324613709393355149)
          ·
            refine ⟨4480509496730141022508181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11948025324613709393355149 4480509496730141022508181)
            ·
              refine ⟨210023882659225360430071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 4480509496730141022508181 210023882659225360430071)
              ·
                refine ⟨315035823988838040645107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 210023882659225360430071 315035823988838040645107)
                ·
                  refine ⟨472553735983257060967661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 315035823988838040645107 472553735983257060967661)
                  ·
                    refine ⟨177207650993721397862873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 472553735983257060967661 177207650993721397862873)
                    ·
                      refine ⟨132905738245291048397155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 177207650993721397862873 132905738245291048397155)
                      ·
                        rfl

theorem cell23_258833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 6, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 6, 1, 1, 3, 2].length) (baseStart_258833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_258833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_258833 prefixEnd_258833 := by exact prefixLift 258833
  have htrace : WordTrace (prefixWord ++ tailWord_258833) baseStart_258833 baseEnd_258833 := by
    simpa [prefixWord, tailWord_258833, baseEnd_258833] using wordTrace_append hprefix tailTrace_258833
  have hstable : (prefixWord ++ tailWord_258833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_258833).length < 2 ^ (prefixWord ++ tailWord_258833).sum := by decide
  have hdescent : baseEnd_258833 < baseStart_258833 := by decide
  rcases family_descends (prefixWord ++ tailWord_258833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_258869 : List Nat := [1, 3, 3, 1, 3, 1, 2, 2, 7]
def baseStart_258869 : Nat := 118140960795 + 258869 * 2 ^ 59
def prefixEnd_258869 : Nat := 4983230072969 + 3 ^ 40 * 258869 * 2
def baseEnd_258869 : Nat := 14769358172094767505221

theorem tailTrace_258869 : CollatzResearch.WordTrace tailWord_258869 prefixEnd_258869 14769358172094767505221 := by
  unfold tailWord_258869
  simp only [CollatzResearch.WordTrace]
  refine ⟨9441728099169299150467661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6294485399446199433645107 9441728099169299150467661)
  ·
    refine ⟨3540648037188487181425373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9441728099169299150467661 3540648037188487181425373)
    ·
      refine ⟨1327743013945682693034515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3540648037188487181425373 1327743013945682693034515)
      ·
        refine ⟨1991614520918524039551773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1327743013945682693034515 1991614520918524039551773)
        ·
          refine ⟨746855445344446514831915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1991614520918524039551773 746855445344446514831915)
          ·
            refine ⟨1120283168016669772247873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 746855445344446514831915 1120283168016669772247873)
            ·
              refine ⟨840212376012502329185905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1120283168016669772247873 840212376012502329185905)
              ·
                refine ⟨630159282009376746889429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 840212376012502329185905 630159282009376746889429)
                ·
                  refine ⟨14769358172094767505221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 630159282009376746889429 14769358172094767505221)
                  ·
                    rfl

theorem cell23_258869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 2, 2, 7].length) (baseStart_258869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_258869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_258869 prefixEnd_258869 := by exact prefixLift 258869
  have htrace : WordTrace (prefixWord ++ tailWord_258869) baseStart_258869 baseEnd_258869 := by
    simpa [prefixWord, tailWord_258869, baseEnd_258869] using wordTrace_append hprefix tailTrace_258869
  have hstable : (prefixWord ++ tailWord_258869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_258869).length < 2 ^ (prefixWord ++ tailWord_258869).sum := by decide
  have hdescent : baseEnd_258869 < baseStart_258869 := by decide
  rcases family_descends (prefixWord ++ tailWord_258869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_258903 : List Nat := [1, 1, 3, 2, 4, 2, 3, 2, 5]
def baseStart_258903 : Nat := 118140960795 + 258903 * 2 ^ 59
def prefixEnd_258903 : Nat := 4983230072969 + 3 ^ 40 * 258903 * 2
def baseEnd_258903 : Nat := 14771297987900641613537

theorem tailTrace_258903 : CollatzResearch.WordTrace tailWord_258903 prefixEnd_258903 14771297987900641613537 := by
  unfold tailWord_258903
  simp only [CollatzResearch.WordTrace]
  refine ⟨9442968181046122957205363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6295312120697415304803575 9442968181046122957205363)
  ·
    refine ⟨14164452271569184435808045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9442968181046122957205363 14164452271569184435808045)
    ·
      refine ⟨5311669601838444163428017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14164452271569184435808045 5311669601838444163428017)
      ·
        refine ⟨3983752201378833122571013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5311669601838444163428017 3983752201378833122571013)
        ·
          refine ⟨746953537758531210482065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3983752201378833122571013 746953537758531210482065)
          ·
            refine ⟨560215153318898407861549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 746953537758531210482065 560215153318898407861549)
            ·
              refine ⟨210080682494586902948081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 560215153318898407861549 210080682494586902948081)
              ·
                refine ⟨157560511870940177211061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 210080682494586902948081 157560511870940177211061)
                ·
                  refine ⟨14771297987900641613537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 157560511870940177211061 14771297987900641613537)
                  ·
                    rfl

theorem cell23_258903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 3, 2, 5].length) (baseStart_258903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_258903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_258903 prefixEnd_258903 := by exact prefixLift 258903
  have htrace : WordTrace (prefixWord ++ tailWord_258903) baseStart_258903 baseEnd_258903 := by
    simpa [prefixWord, tailWord_258903, baseEnd_258903] using wordTrace_append hprefix tailTrace_258903
  have hstable : (prefixWord ++ tailWord_258903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_258903).length < 2 ^ (prefixWord ++ tailWord_258903).sum := by decide
  have hdescent : baseEnd_258903 < baseStart_258903 := by decide
  rcases family_descends (prefixWord ++ tailWord_258903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_258914 : List Nat := [3, 3, 2, 1, 3, 2, 2, 1, 2, 2, 2]
def baseStart_258914 : Nat := 118140960795 + 258914 * 2 ^ 59
def prefixEnd_258914 : Nat := 4983230072969 + 3 ^ 40 * 258914 * 2
def baseEnd_258914 : Nat := 132947330178305231484283

theorem tailTrace_258914 : CollatzResearch.WordTrace tailWord_258914 prefixEnd_258914 132947330178305231484283 := by
  unfold tailWord_258914
  simp only [CollatzResearch.WordTrace]
  refine ⟨2360842346001567958963949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6295579589337514557237197 2360842346001567958963949)
  ·
    refine ⟨885315879750587984611481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2360842346001567958963949 885315879750587984611481)
    ·
      refine ⟨663986909812940988458611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 885315879750587984611481 663986909812940988458611)
      ·
        refine ⟨995980364719411482687917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 663986909812940988458611 995980364719411482687917)
        ·
          refine ⟨373492636769779306007969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 995980364719411482687917 373492636769779306007969)
          ·
            refine ⟨280119477577334479505977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 373492636769779306007969 280119477577334479505977)
            ·
              refine ⟨210089608183000859629483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 280119477577334479505977 210089608183000859629483)
              ·
                refine ⟨315134412274501289444225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 210089608183000859629483 315134412274501289444225)
                ·
                  refine ⟨236350809205875967083169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 315134412274501289444225 236350809205875967083169)
                  ·
                    refine ⟨177263106904406975312377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 236350809205875967083169 177263106904406975312377)
                    ·
                      refine ⟨132947330178305231484283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 177263106904406975312377 132947330178305231484283)
                      ·
                        rfl

theorem cell23_258914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 2, 2, 1, 2, 2, 2].length) (baseStart_258914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_258914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_258914 prefixEnd_258914 := by exact prefixLift 258914
  have htrace : WordTrace (prefixWord ++ tailWord_258914) baseStart_258914 baseEnd_258914 := by
    simpa [prefixWord, tailWord_258914, baseEnd_258914] using wordTrace_append hprefix tailTrace_258914
  have hstable : (prefixWord ++ tailWord_258914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_258914).length < 2 ^ (prefixWord ++ tailWord_258914).sum := by decide
  have hdescent : baseEnd_258914 < baseStart_258914 := by decide
  rcases family_descends (prefixWord ++ tailWord_258914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_258939 : List Nat := [1, 1, 1, 1, 1, 5, 2, 3, 1, 4, 3]
def baseStart_258939 : Nat := 118140960795 + 258939 * 2 ^ 59
def prefixEnd_258939 : Nat := 4983230072969 + 3 ^ 40 * 258939 * 2
def baseEnd_258939 : Nat := 132960167194667633671667

theorem tailTrace_258939 : CollatzResearch.WordTrace tailWord_258939 prefixEnd_258939 132960167194667633671667 := by
  unfold tailWord_258939
  simp only [CollatzResearch.WordTrace]
  refine ⟨9444281208915701105515871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6296187472610467403677247 9444281208915701105515871)
  ·
    refine ⟨14166421813373551658273807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9444281208915701105515871 14166421813373551658273807)
    ·
      refine ⟨21249632720060327487410711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14166421813373551658273807 21249632720060327487410711)
      ·
        refine ⟨31874449080090491231116067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21249632720060327487410711 31874449080090491231116067)
        ·
          refine ⟨47811673620135736846674101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31874449080090491231116067 47811673620135736846674101)
          ·
            refine ⟨4482344401887725329375697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 47811673620135736846674101 4482344401887725329375697)
            ·
              refine ⟨3361758301415793997031773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4482344401887725329375697 3361758301415793997031773)
              ·
                refine ⟨1260659363030922748886915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3361758301415793997031773 1260659363030922748886915)
                ·
                  refine ⟨1890989044546384123330373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1260659363030922748886915 1890989044546384123330373)
                  ·
                    refine ⟨354560445852447023124445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1890989044546384123330373 354560445852447023124445)
                    ·
                      refine ⟨132960167194667633671667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 354560445852447023124445 132960167194667633671667)
                      ·
                        rfl

theorem cell23_258939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 3, 1, 4, 3].length) (baseStart_258939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_258939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_258939 prefixEnd_258939 := by exact prefixLift 258939
  have htrace : WordTrace (prefixWord ++ tailWord_258939) baseStart_258939 baseEnd_258939 := by
    simpa [prefixWord, tailWord_258939, baseEnd_258939] using wordTrace_append hprefix tailTrace_258939
  have hstable : (prefixWord ++ tailWord_258939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_258939).length < 2 ^ (prefixWord ++ tailWord_258939).sum := by decide
  have hdescent : baseEnd_258939 < baseStart_258939 := by decide
  rcases family_descends (prefixWord ++ tailWord_258939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_258956 : List Nat := [2, 2, 1, 2, 1, 2, 4, 2, 2, 2, 3]
def baseStart_258956 : Nat := 118140960795 + 258956 * 2 ^ 59
def prefixEnd_258956 : Nat := 4983230072969 + 3 ^ 40 * 258956 * 2
def baseEnd_258956 : Nat := 132968896365794067159089

theorem tailTrace_258956 : CollatzResearch.WordTrace tailWord_258956 prefixEnd_258956 132968896365794067159089 := by
  unfold tailWord_258956
  simp only [CollatzResearch.WordTrace]
  refine ⟨4722450624927056504442361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6296600833236075339256481 4722450624927056504442361)
  ·
    refine ⟨3541837968695292378331771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4722450624927056504442361 3541837968695292378331771)
    ·
      refine ⟨5312756953042938567497657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3541837968695292378331771 5312756953042938567497657)
      ·
        refine ⟨3984567714782203925623243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5312756953042938567497657 3984567714782203925623243)
        ·
          refine ⟨5976851572173305888434865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3984567714782203925623243 5976851572173305888434865)
          ·
            refine ⟨4482638679129979416326149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5976851572173305888434865 4482638679129979416326149)
            ·
              refine ⟨840494752336871140561153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4482638679129979416326149 840494752336871140561153)
              ·
                refine ⟨630371064252653355420865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 840494752336871140561153 630371064252653355420865)
                ·
                  refine ⟨472778298189490016565649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 630371064252653355420865 472778298189490016565649)
                  ·
                    refine ⟨354583723642117512424237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 472778298189490016565649 354583723642117512424237)
                    ·
                      refine ⟨132968896365794067159089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 354583723642117512424237 132968896365794067159089)
                      ·
                        rfl

theorem cell23_258956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 4, 2, 2, 2, 3].length) (baseStart_258956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_258956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_258956 prefixEnd_258956 := by exact prefixLift 258956
  have htrace : WordTrace (prefixWord ++ tailWord_258956) baseStart_258956 baseEnd_258956 := by
    simpa [prefixWord, tailWord_258956, baseEnd_258956] using wordTrace_append hprefix tailTrace_258956
  have hstable : (prefixWord ++ tailWord_258956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_258956).length < 2 ^ (prefixWord ++ tailWord_258956).sum := by decide
  have hdescent : baseEnd_258956 < baseStart_258956 := by decide
  rcases family_descends (prefixWord ++ tailWord_258956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_258969 : List Nat := [1, 2, 1, 2, 1, 3, 1, 2, 2, 5, 3]
def baseStart_258969 : Nat := 118140960795 + 258969 * 2 ^ 59
def prefixEnd_258969 : Nat := 4983230072969 + 3 ^ 40 * 258969 * 2
def baseEnd_258969 : Nat := 132975571614302516296529

theorem tailTrace_258969 : CollatzResearch.WordTrace tailWord_258969 prefixEnd_258969 132975571614302516296529 := by
  unfold tailWord_258969
  simp only [CollatzResearch.WordTrace]
  refine ⟨9445375398807016229107961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6296916932538010819405307 9445375398807016229107961)
  ·
    refine ⟨7084031549105262171830971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9445375398807016229107961 7084031549105262171830971)
    ·
      refine ⟨10626047323657893257746457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7084031549105262171830971 10626047323657893257746457)
      ·
        refine ⟨7969535492743419943309843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10626047323657893257746457 7969535492743419943309843)
        ·
          refine ⟨11954303239115129914964765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7969535492743419943309843 11954303239115129914964765)
          ·
            refine ⟨4482863714668173718111787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11954303239115129914964765 4482863714668173718111787)
            ·
              refine ⟨6724295572002260577167681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4482863714668173718111787 6724295572002260577167681)
              ·
                refine ⟨5043221679001695432875761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6724295572002260577167681 5043221679001695432875761)
                ·
                  refine ⟨3782416259251271574656821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5043221679001695432875761 3782416259251271574656821)
                  ·
                    refine ⟨354601524304806710124077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3782416259251271574656821 354601524304806710124077)
                    ·
                      refine ⟨132975571614302516296529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 354601524304806710124077 132975571614302516296529)
                      ·
                        rfl

theorem cell23_258969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 2, 2, 5, 3].length) (baseStart_258969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_258969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_258969 prefixEnd_258969 := by exact prefixLift 258969
  have htrace : WordTrace (prefixWord ++ tailWord_258969) baseStart_258969 baseEnd_258969 := by
    simpa [prefixWord, tailWord_258969, baseEnd_258969] using wordTrace_append hprefix tailTrace_258969
  have hstable : (prefixWord ++ tailWord_258969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_258969).length < 2 ^ (prefixWord ++ tailWord_258969).sum := by decide
  have hdescent : baseEnd_258969 < baseStart_258969 := by decide
  rcases family_descends (prefixWord ++ tailWord_258969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_259020 : List Nat := [2, 2, 1, 4, 1, 1, 1, 6, 1, 1, 3]
def baseStart_259020 : Nat := 118140960795 + 259020 * 2 ^ 59
def prefixEnd_259020 : Nat := 4983230072969 + 3 ^ 40 * 259020 * 2
def baseEnd_259020 : Nat := 133001759127681816758795

theorem tailTrace_259020 : CollatzResearch.WordTrace tailWord_259020 prefixEnd_259020 133001759127681816758795 := by
  unfold tailWord_259020
  simp only [CollatzResearch.WordTrace]
  refine ⟨4723617760811125969607257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6298157014414834626143009 4723617760811125969607257)
  ·
    refine ⟨3542713320608344477205443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4723617760811125969607257 3542713320608344477205443)
    ·
      refine ⟨5314069980912516715808165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3542713320608344477205443 5314069980912516715808165)
      ·
        refine ⟨996388121421096884214031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5314069980912516715808165 996388121421096884214031)
        ·
          refine ⟨1494582182131645326321047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 996388121421096884214031 1494582182131645326321047)
          ·
            refine ⟨2241873273197467989481571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1494582182131645326321047 2241873273197467989481571)
            ·
              refine ⟨3362809909796201984222357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2241873273197467989481571 3362809909796201984222357)
              ·
                refine ⟨157631714521696968010423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3362809909796201984222357 157631714521696968010423)
                ·
                  refine ⟨236447571782545452015635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 157631714521696968010423 236447571782545452015635)
                  ·
                    refine ⟨354671357673818178023453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 236447571782545452015635 354671357673818178023453)
                    ·
                      refine ⟨133001759127681816758795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 354671357673818178023453 133001759127681816758795)
                      ·
                        rfl

theorem cell23_259020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 6, 1, 1, 3].length) (baseStart_259020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_259020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_259020 prefixEnd_259020 := by exact prefixLift 259020
  have htrace : WordTrace (prefixWord ++ tailWord_259020) baseStart_259020 baseEnd_259020 := by
    simpa [prefixWord, tailWord_259020, baseEnd_259020] using wordTrace_append hprefix tailTrace_259020
  have hstable : (prefixWord ++ tailWord_259020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_259020).length < 2 ^ (prefixWord ++ tailWord_259020).sum := by decide
  have hdescent : baseEnd_259020 < baseStart_259020 := by decide
  rcases family_descends (prefixWord ++ tailWord_259020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_259030 : List Nat := [5, 2, 1, 1, 2, 1, 1, 2, 1, 5, 2]
def baseStart_259030 : Nat := 118140960795 + 259030 * 2 ^ 59
def prefixEnd_259030 : Nat := 4983230072969 + 3 ^ 40 * 259030 * 2
def baseEnd_259030 : Nat := 133006893934226777633749

theorem tailTrace_259030 : CollatzResearch.WordTrace tailWord_259030 prefixEnd_259030 133006893934226777633749 := by
  unfold tailWord_259030
  simp only [CollatzResearch.WordTrace]
  refine ⟨590475015724126477942409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6298400167724015764719029 590475015724126477942409)
  ·
    refine ⟨442856261793094858456807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 590475015724126477942409 442856261793094858456807)
    ·
      refine ⟨664284392689642287685211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 442856261793094858456807 664284392689642287685211)
      ·
        refine ⟨996426589034463431527817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 664284392689642287685211 996426589034463431527817)
        ·
          refine ⟨747319941775847573645863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 996426589034463431527817 747319941775847573645863)
          ·
            refine ⟨1120979912663771360468795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 747319941775847573645863 1120979912663771360468795)
            ·
              refine ⟨1681469868995657040703193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1120979912663771360468795 1681469868995657040703193)
              ·
                refine ⟨1261102401746742780527395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1681469868995657040703193 1261102401746742780527395)
                ·
                  refine ⟨1891653602620114170791093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1261102401746742780527395 1891653602620114170791093)
                  ·
                    refine ⟨177342525245635703511665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1891653602620114170791093 177342525245635703511665)
                    ·
                      refine ⟨133006893934226777633749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 177342525245635703511665 133006893934226777633749)
                      ·
                        rfl

theorem cell23_259030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 2, 1, 5, 2].length) (baseStart_259030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_259030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_259030 prefixEnd_259030 := by exact prefixLift 259030
  have htrace : WordTrace (prefixWord ++ tailWord_259030) baseStart_259030 baseEnd_259030 := by
    simpa [prefixWord, tailWord_259030, baseEnd_259030] using wordTrace_append hprefix tailTrace_259030
  have hstable : (prefixWord ++ tailWord_259030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_259030).length < 2 ^ (prefixWord ++ tailWord_259030).sum := by decide
  have hdescent : baseEnd_259030 < baseStart_259030 := by decide
  rcases family_descends (prefixWord ++ tailWord_259030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_259043 : List Nat := [1, 1, 1, 6, 1, 1, 4, 2, 1, 1, 4]
def baseStart_259043 : Nat := 118140960795 + 259043 * 2 ^ 59
def prefixEnd_259043 : Nat := 4983230072969 + 3 ^ 40 * 259043 * 2
def baseEnd_259043 : Nat := 133013569182735226771189

theorem tailTrace_259043 : CollatzResearch.WordTrace tailWord_259043 prefixEnd_259043 133013569182735226771189 := by
  unfold tailWord_259043
  simp only [CollatzResearch.WordTrace]
  refine ⟨9448074400538926867301783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6298716267025951244867855 9448074400538926867301783)
  ·
    refine ⟨14172111600808390300952675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9448074400538926867301783 14172111600808390300952675)
    ·
      refine ⟨21258167401212585451429013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14172111600808390300952675 21258167401212585451429013)
      ·
        refine ⟨996476596931839943035735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 21258167401212585451429013 996476596931839943035735)
        ·
          refine ⟨1494714895397759914553603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 996476596931839943035735 1494714895397759914553603)
          ·
            refine ⟨2242072343096639871830405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1494714895397759914553603 2242072343096639871830405)
            ·
              refine ⟨420388564330619975968201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2242072343096639871830405 420388564330619975968201)
              ·
                refine ⟨315291423247964981976151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 420388564330619975968201 315291423247964981976151)
                ·
                  refine ⟨472937134871947472964227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 315291423247964981976151 472937134871947472964227)
                  ·
                    refine ⟨709405702307921209446341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 472937134871947472964227 709405702307921209446341)
                    ·
                      refine ⟨133013569182735226771189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 709405702307921209446341 133013569182735226771189)
                      ·
                        rfl

theorem cell23_259043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 4, 2, 1, 1, 4].length) (baseStart_259043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_259043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_259043 prefixEnd_259043 := by exact prefixLift 259043
  have htrace : WordTrace (prefixWord ++ tailWord_259043) baseStart_259043 baseEnd_259043 := by
    simpa [prefixWord, tailWord_259043, baseEnd_259043] using wordTrace_append hprefix tailTrace_259043
  have hstable : (prefixWord ++ tailWord_259043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_259043).length < 2 ^ (prefixWord ++ tailWord_259043).sum := by decide
  have hdescent : baseEnd_259043 < baseStart_259043 := by decide
  rcases family_descends (prefixWord ++ tailWord_259043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_259054 : List Nat := [4, 1, 2, 1, 4, 2, 1, 3, 1, 1, 3]
def baseStart_259054 : Nat := 118140960795 + 259054 * 2 ^ 59
def prefixEnd_259054 : Nat := 4983230072969 + 3 ^ 40 * 259054 * 2
def baseEnd_259054 : Nat := 133019217469934683733639

theorem tailTrace_259054 : CollatzResearch.WordTrace tailWord_259054 prefixEnd_259054 133019217469934683733639 := by
  unfold tailWord_259054
  simp only [CollatzResearch.WordTrace]
  refine ⟨1181059450437384468244027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6298983735666050497301477 1181059450437384468244027)
  ·
    refine ⟨1771589175656076702366041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1181059450437384468244027 1771589175656076702366041)
    ·
      refine ⟨1328691881742057526774531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1771589175656076702366041 1328691881742057526774531)
      ·
        refine ⟨1993037822613086290161797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1328691881742057526774531 1993037822613086290161797)
        ·
          refine ⟨373694591739953679405337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1993037822613086290161797 373694591739953679405337)
          ·
            refine ⟨280270943804965259554003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 373694591739953679405337 280270943804965259554003)
            ·
              refine ⟨420406415707447889331005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 280270943804965259554003 420406415707447889331005)
              ·
                refine ⟨157652405890292958499127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 420406415707447889331005 157652405890292958499127)
                ·
                  refine ⟨236478608835439437748691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 157652405890292958499127 236478608835439437748691)
                  ·
                    refine ⟨354717913253159156623037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 236478608835439437748691 354717913253159156623037)
                    ·
                      refine ⟨133019217469934683733639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 354717913253159156623037 133019217469934683733639)
                      ·
                        rfl

theorem cell23_259054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 2, 1, 3, 1, 1, 3].length) (baseStart_259054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_259054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_259054 prefixEnd_259054 := by exact prefixLift 259054
  have htrace : WordTrace (prefixWord ++ tailWord_259054) baseStart_259054 baseEnd_259054 := by
    simpa [prefixWord, tailWord_259054, baseEnd_259054] using wordTrace_append hprefix tailTrace_259054
  have hstable : (prefixWord ++ tailWord_259054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_259054).length < 2 ^ (prefixWord ++ tailWord_259054).sum := by decide
  have hdescent : baseEnd_259054 < baseStart_259054 := by decide
  rcases family_descends (prefixWord ++ tailWord_259054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_259136 : List Nat := [2, 1, 1, 2, 2, 3, 1, 1, 1, 6, 3]
def baseStart_259136 : Nat := 118140960795 + 259136 * 2 ^ 59
def prefixEnd_259136 : Nat := 4983230072969 + 3 ^ 40 * 259136 * 2
def baseEnd_259136 : Nat := 133061322883603362908261

theorem tailTrace_259136 : CollatzResearch.WordTrace tailWord_259136 prefixEnd_259136 133061322883603362908261 := by
  unfold tailWord_259136
  simp only [CollatzResearch.WordTrace]
  refine ⟨4725733194601001875218631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6300977592801335833624841 4725733194601001875218631)
  ·
    refine ⟨7088599791901502812827947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4725733194601001875218631 7088599791901502812827947)
    ·
      refine ⟨10632899687852254219241921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7088599791901502812827947 10632899687852254219241921)
      ·
        refine ⟨7974674765889190664431441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10632899687852254219241921 7974674765889190664431441)
        ·
          refine ⟨5981006074416892998323581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7974674765889190664431441 5981006074416892998323581)
          ·
            refine ⟨2242877277906334874371343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5981006074416892998323581 2242877277906334874371343)
            ·
              refine ⟨3364315916859502311557015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2242877277906334874371343 3364315916859502311557015)
              ·
                refine ⟨5046473875289253467335523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3364315916859502311557015 5046473875289253467335523)
                ·
                  refine ⟨7569710812933880201003285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5046473875289253467335523 7569710812933880201003285)
                  ·
                    refine ⟨354830194356275634422029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7569710812933880201003285 354830194356275634422029)
                    ·
                      refine ⟨133061322883603362908261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 354830194356275634422029 133061322883603362908261)
                      ·
                        rfl

theorem cell23_259136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 1, 1, 6, 3].length) (baseStart_259136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_259136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_259136 prefixEnd_259136 := by exact prefixLift 259136
  have htrace : WordTrace (prefixWord ++ tailWord_259136) baseStart_259136 baseEnd_259136 := by
    simpa [prefixWord, tailWord_259136, baseEnd_259136] using wordTrace_append hprefix tailTrace_259136
  have hstable : (prefixWord ++ tailWord_259136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_259136).length < 2 ^ (prefixWord ++ tailWord_259136).sum := by decide
  have hdescent : baseEnd_259136 < baseStart_259136 := by decide
  rcases family_descends (prefixWord ++ tailWord_259136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_259146 : List Nat := [3, 1, 2, 1, 1, 2, 3, 1, 1, 4, 4]
def baseStart_259146 : Nat := 118140960795 + 259146 * 2 ^ 59
def prefixEnd_259146 : Nat := 4983230072969 + 3 ^ 40 * 259146 * 2
def baseEnd_259146 : Nat := 133066457690148323783215

theorem tailTrace_259146 : CollatzResearch.WordTrace tailWord_259146 prefixEnd_259146 133066457690148323783215 := by
  unfold tailWord_259146
  simp only [CollatzResearch.WordTrace]
  refine ⟨2362957779791443864575323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6301220746110516972200861 2362957779791443864575323)
  ·
    refine ⟨3544436669687165796862985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2362957779791443864575323 3544436669687165796862985)
    ·
      refine ⟨2658327502265374347647239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3544436669687165796862985 2658327502265374347647239)
      ·
        refine ⟨3987491253398061521470859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2658327502265374347647239 3987491253398061521470859)
        ·
          refine ⟨5981236880097092282206289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3987491253398061521470859 5981236880097092282206289)
          ·
            refine ⟨4485927660072819211654717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5981236880097092282206289 4485927660072819211654717)
            ·
              refine ⟨1682222872527307204370519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4485927660072819211654717 1682222872527307204370519)
              ·
                refine ⟨2523334308790960806555779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1682222872527307204370519 2523334308790960806555779)
                ·
                  refine ⟨3785001463186441209833669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2523334308790960806555779 3785001463186441209833669)
                  ·
                    refine ⟨709687774347457726843813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3785001463186441209833669 709687774347457726843813)
                    ·
                      refine ⟨133066457690148323783215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 709687774347457726843813 133066457690148323783215)
                      ·
                        rfl

theorem cell23_259146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 1, 1, 4, 4].length) (baseStart_259146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_259146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_259146 prefixEnd_259146 := by exact prefixLift 259146
  have htrace : WordTrace (prefixWord ++ tailWord_259146) baseStart_259146 baseEnd_259146 := by
    simpa [prefixWord, tailWord_259146, baseEnd_259146] using wordTrace_append hprefix tailTrace_259146
  have hstable : (prefixWord ++ tailWord_259146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_259146).length < 2 ^ (prefixWord ++ tailWord_259146).sum := by decide
  have hdescent : baseEnd_259146 < baseStart_259146 := by decide
  rcases family_descends (prefixWord ++ tailWord_259146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_259150 : List Nat := [4, 1, 1, 1, 1, 3, 4, 1, 1, 4, 2]
def baseStart_259150 : Nat := 118140960795 + 259150 * 2 ^ 59
def prefixEnd_259150 : Nat := 4983230072969 + 3 ^ 40 * 259150 * 2
def baseEnd_259150 : Nat := 133068511612766308133197

theorem tailTrace_259150 : CollatzResearch.WordTrace tailWord_259150 prefixEnd_259150 133068511612766308133197 := by
  unfold tailWord_259150
  simp only [CollatzResearch.WordTrace]
  refine ⟨1181497126393910517680863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6301318007434189427631269 1181497126393910517680863)
  ·
    refine ⟨1772245689590865776521295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1181497126393910517680863 1772245689590865776521295)
    ·
      refine ⟨2658368534386298664781943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1772245689590865776521295 2658368534386298664781943)
      ·
        refine ⟨3987552801579447997172915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2658368534386298664781943 3987552801579447997172915)
        ·
          refine ⟨5981329202369171995759373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3987552801579447997172915 5981329202369171995759373)
          ·
            refine ⟨2242998450888439498409765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5981329202369171995759373 2242998450888439498409765)
            ·
              refine ⟨420562209541582405951831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2242998450888439498409765 420562209541582405951831)
              ·
                refine ⟨630843314312373608927747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 420562209541582405951831 630843314312373608927747)
                ·
                  refine ⟨946264971468560413391621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 630843314312373608927747 946264971468560413391621)
                  ·
                    refine ⟨177424682150355077510929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 946264971468560413391621 177424682150355077510929)
                    ·
                      refine ⟨133068511612766308133197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 177424682150355077510929 133068511612766308133197)
                      ·
                        rfl

theorem cell23_259150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 4, 1, 1, 4, 2].length) (baseStart_259150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_259150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_259150 prefixEnd_259150 := by exact prefixLift 259150
  have htrace : WordTrace (prefixWord ++ tailWord_259150) baseStart_259150 baseEnd_259150 := by
    simpa [prefixWord, tailWord_259150, baseEnd_259150] using wordTrace_append hprefix tailTrace_259150
  have hstable : (prefixWord ++ tailWord_259150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_259150).length < 2 ^ (prefixWord ++ tailWord_259150).sum := by decide
  have hdescent : baseEnd_259150 < baseStart_259150 := by decide
  rcases family_descends (prefixWord ++ tailWord_259150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_259156 : List Nat := [2, 4, 1, 1, 1, 1, 3, 1, 9]
def baseStart_259156 : Nat := 118140960795 + 259156 * 2 ^ 59
def prefixEnd_259156 : Nat := 4983230072969 + 3 ^ 40 * 259156 * 2
def baseEnd_259156 : Nat := 14785732499632587184241

theorem tailTrace_259156 : CollatzResearch.WordTrace tailWord_259156 prefixEnd_259156 14785732499632587184241 := by
  unfold tailWord_259156
  simp only [CollatzResearch.WordTrace]
  refine ⟨4726097924564773583082661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6301463899419698110776881 4726097924564773583082661)
  ·
    refine ⟨886143360855895046827999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4726097924564773583082661 886143360855895046827999)
    ·
      refine ⟨1329215041283842570241999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 886143360855895046827999 1329215041283842570241999)
      ·
        refine ⟨1993822561925763855362999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1329215041283842570241999 1993822561925763855362999)
        ·
          refine ⟨2990733842888645783044499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1993822561925763855362999 2990733842888645783044499)
          ·
            refine ⟨4486100764332968674566749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2990733842888645783044499 4486100764332968674566749)
            ·
              refine ⟨1682287786624863252962531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4486100764332968674566749 1682287786624863252962531)
              ·
                refine ⟨2523431679937294879443797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1682287786624863252962531 2523431679937294879443797)
                ·
                  refine ⟨14785732499632587184241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 2523431679937294879443797 14785732499632587184241)
                  ·
                    rfl

theorem cell23_259156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 1, 9].length) (baseStart_259156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_259156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_259156 prefixEnd_259156 := by exact prefixLift 259156
  have htrace : WordTrace (prefixWord ++ tailWord_259156) baseStart_259156 baseEnd_259156 := by
    simpa [prefixWord, tailWord_259156, baseEnd_259156] using wordTrace_append hprefix tailTrace_259156
  have hstable : (prefixWord ++ tailWord_259156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_259156).length < 2 ^ (prefixWord ++ tailWord_259156).sum := by decide
  have hdescent : baseEnd_259156 < baseStart_259156 := by decide
  rcases family_descends (prefixWord ++ tailWord_259156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_259190 : List Nat := [5, 1, 1, 2, 1, 1, 1, 6, 5]
def baseStart_259190 : Nat := 118140960795 + 259190 * 2 ^ 59
def prefixEnd_259190 : Nat := 4983230072969 + 3 ^ 40 * 259190 * 2
def baseEnd_259190 : Nat := 14787672315438461292557

theorem tailTrace_259190 : CollatzResearch.WordTrace tailWord_259190 prefixEnd_259190 14787672315438461292557 := by
  unfold tailWord_259190
  simp only [CollatzResearch.WordTrace]
  refine ⟨590839745687898185806439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6302290620670913981935349 590839745687898185806439)
  ·
    refine ⟨886259618531847278709659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 590839745687898185806439 886259618531847278709659)
    ·
      refine ⟨1329389427797770918064489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 886259618531847278709659 1329389427797770918064489)
      ·
        refine ⟨997042070848328188548367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1329389427797770918064489 997042070848328188548367)
        ·
          refine ⟨1495563106272492282822551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 997042070848328188548367 1495563106272492282822551)
          ·
            refine ⟨2243344659408738424233827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1495563106272492282822551 2243344659408738424233827)
            ·
              refine ⟨3365016989113107636350741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2243344659408738424233827 3365016989113107636350741)
              ·
                refine ⟨157735171364676920453941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3365016989113107636350741 157735171364676920453941)
                ·
                  refine ⟨14787672315438461292557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 157735171364676920453941 14787672315438461292557)
                  ·
                    rfl

theorem cell23_259190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 6, 5].length) (baseStart_259190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_259190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_259190 prefixEnd_259190 := by exact prefixLift 259190
  have htrace : WordTrace (prefixWord ++ tailWord_259190) baseStart_259190 baseEnd_259190 := by
    simpa [prefixWord, tailWord_259190, baseEnd_259190] using wordTrace_append hprefix tailTrace_259190
  have hstable : (prefixWord ++ tailWord_259190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_259190).length < 2 ^ (prefixWord ++ tailWord_259190).sum := by decide
  have hdescent : baseEnd_259190 < baseStart_259190 := by decide
  rcases family_descends (prefixWord ++ tailWord_259190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_259196 : List Nat := [2, 2, 2, 1, 1, 3, 2, 1, 1, 1, 7]
def baseStart_259196 : Nat := 118140960795 + 259196 * 2 ^ 59
def prefixEnd_259196 : Nat := 4983230072969 + 3 ^ 40 * 259196 * 2
def baseEnd_259196 : Nat := 133092131722873128157985

theorem tailTrace_259196 : CollatzResearch.WordTrace tailWord_259196 prefixEnd_259196 133092131722873128157985 := by
  unfold tailWord_259196
  simp only [CollatzResearch.WordTrace]
  refine ⟨4726827384492316998810721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6302436512656422665080961 4726827384492316998810721)
  ·
    refine ⟨3545120538369237749108041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4726827384492316998810721 3545120538369237749108041)
    ·
      refine ⟨2658840403776928311831031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3545120538369237749108041 2658840403776928311831031)
      ·
        refine ⟨3988260605665392467746547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2658840403776928311831031 3988260605665392467746547)
        ·
          refine ⟨5982390908498088701619821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3988260605665392467746547 5982390908498088701619821)
          ·
            refine ⟨2243396590686783263107433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5982390908498088701619821 2243396590686783263107433)
            ·
              refine ⟨1682547443015087447330575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2243396590686783263107433 1682547443015087447330575)
              ·
                refine ⟨2523821164522631170995863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1682547443015087447330575 2523821164522631170995863)
                ·
                  refine ⟨3785731746783946756493795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2523821164522631170995863 3785731746783946756493795)
                  ·
                    refine ⟨5678597620175920134740693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3785731746783946756493795 5678597620175920134740693)
                    ·
                      refine ⟨133092131722873128157985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 5678597620175920134740693 133092131722873128157985)
                      ·
                        rfl

theorem cell23_259196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 1, 1, 1, 7].length) (baseStart_259196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_259196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_259196 prefixEnd_259196 := by exact prefixLift 259196
  have htrace : WordTrace (prefixWord ++ tailWord_259196) baseStart_259196 baseEnd_259196 := by
    simpa [prefixWord, tailWord_259196, baseEnd_259196] using wordTrace_append hprefix tailTrace_259196
  have hstable : (prefixWord ++ tailWord_259196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_259196).length < 2 ^ (prefixWord ++ tailWord_259196).sum := by decide
  have hdescent : baseEnd_259196 < baseStart_259196 := by decide
  rcases family_descends (prefixWord ++ tailWord_259196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_259223 : List Nat := [1, 1, 3, 3, 3, 1, 2, 1, 1, 3, 4]
def baseStart_259223 : Nat := 118140960795 + 259223 * 2 ^ 59
def prefixEnd_259223 : Nat := 4983230072969 + 3 ^ 40 * 259223 * 2
def baseEnd_259223 : Nat := 133105995700544522520361

theorem tailTrace_259223 : CollatzResearch.WordTrace tailWord_259223 prefixEnd_259223 133105995700544522520361 := by
  unfold tailWord_259223
  simp only [CollatzResearch.WordTrace]
  refine ⟨9454639539886817608854323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6303093026591211739236215 9454639539886817608854323)
  ·
    refine ⟨14181959309830226413281485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9454639539886817608854323 14181959309830226413281485)
    ·
      refine ⟨5318234741186334904980557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14181959309830226413281485 5318234741186334904980557)
      ·
        refine ⟨1994338027944875589367709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5318234741186334904980557 1994338027944875589367709)
        ·
          refine ⟨747876760479328346012891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1994338027944875589367709 747876760479328346012891)
          ·
            refine ⟨1121815140718992519019337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 747876760479328346012891 1121815140718992519019337)
            ·
              refine ⟨841361355539244389264503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1121815140718992519019337 841361355539244389264503)
              ·
                refine ⟨1262042033308866583896755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 841361355539244389264503 1262042033308866583896755)
                ·
                  refine ⟨1893063049963299875845133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1262042033308866583896755 1893063049963299875845133)
                  ·
                    refine ⟨709898643736237453441925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1893063049963299875845133 709898643736237453441925)
                    ·
                      refine ⟨133105995700544522520361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 709898643736237453441925 133105995700544522520361)
                      ·
                        rfl

theorem cell23_259223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 2, 1, 1, 3, 4].length) (baseStart_259223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_259223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_259223 prefixEnd_259223 := by exact prefixLift 259223
  have htrace : WordTrace (prefixWord ++ tailWord_259223) baseStart_259223 baseEnd_259223 := by
    simpa [prefixWord, tailWord_259223, baseEnd_259223] using wordTrace_append hprefix tailTrace_259223
  have hstable : (prefixWord ++ tailWord_259223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_259223).length < 2 ^ (prefixWord ++ tailWord_259223).sum := by decide
  have hdescent : baseEnd_259223 < baseStart_259223 := by decide
  rcases family_descends (prefixWord ++ tailWord_259223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_259250 : List Nat := [3, 2, 1, 1, 1, 4, 3, 1, 3, 4]
def baseStart_259250 : Nat := 118140960795 + 259250 * 2 ^ 59
def prefixEnd_259250 : Nat := 4983230072969 + 3 ^ 40 * 259250 * 2
def baseEnd_259250 : Nat := 44373286559405305627579

theorem tailTrace_259250 : CollatzResearch.WordTrace tailWord_259250 prefixEnd_259250 44373286559405305627579 := by
  unfold tailWord_259250
  simp only [CollatzResearch.WordTrace]
  refine ⟨2363906077697250305021801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6303749540526000813391469 2363906077697250305021801)
  ·
    refine ⟨1772929558272937728766351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2363906077697250305021801 1772929558272937728766351)
    ·
      refine ⟨2659394337409406593149527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1772929558272937728766351 2659394337409406593149527)
      ·
        refine ⟨3989091506114109889724291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2659394337409406593149527 3989091506114109889724291)
        ·
          refine ⟨5983637259171164834586437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3989091506114109889724291 5983637259171164834586437)
          ·
            refine ⟨1121931986094593406484957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5983637259171164834586437 1121931986094593406484957)
            ·
              refine ⟨420724494785472527431859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1121931986094593406484957 420724494785472527431859)
              ·
                refine ⟨631086742178208791147789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 420724494785472527431859 631086742178208791147789)
                ·
                  refine ⟨236657528316828296680421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 631086742178208791147789 236657528316828296680421)
                  ·
                    refine ⟨44373286559405305627579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 236657528316828296680421 44373286559405305627579)
                    ·
                      rfl

theorem cell23_259250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 3, 1, 3, 4].length) (baseStart_259250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_259250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_259250 prefixEnd_259250 := by exact prefixLift 259250
  have htrace : WordTrace (prefixWord ++ tailWord_259250) baseStart_259250 baseEnd_259250 := by
    simpa [prefixWord, tailWord_259250, baseEnd_259250] using wordTrace_append hprefix tailTrace_259250
  have hstable : (prefixWord ++ tailWord_259250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_259250).length < 2 ^ (prefixWord ++ tailWord_259250).sum := by decide
  have hdescent : baseEnd_259250 < baseStart_259250 := by decide
  rcases family_descends (prefixWord ++ tailWord_259250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_259301 : List Nat := [1, 3, 1, 4, 3, 2, 2, 2, 1, 4]
def baseStart_259301 : Nat := 118140960795 + 259301 * 2 ^ 59
def prefixEnd_259301 : Nat := 4983230072969 + 3 ^ 40 * 259301 * 2
def baseEnd_259301 : Nat := 44382015730531739115001

theorem tailTrace_259301 : CollatzResearch.WordTrace tailWord_259301 prefixEnd_259301 44382015730531739115001 := by
  unfold tailWord_259301
  simp only [CollatzResearch.WordTrace]
  refine ⟨9457484433604236930193757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6304989622402824620129171 9457484433604236930193757)
  ·
    refine ⟨3546556662601588848822659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9457484433604236930193757 3546556662601588848822659)
    ·
      refine ⟨5319834993902383273233989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3546556662601588848822659 5319834993902383273233989)
      ·
        refine ⟨997469061356696863731373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5319834993902383273233989 997469061356696863731373)
        ·
          refine ⟨374050898008761323899265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 997469061356696863731373 374050898008761323899265)
          ·
            refine ⟨280538173506570992924449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 374050898008761323899265 280538173506570992924449)
            ·
              refine ⟨210403630129928244693337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 280538173506570992924449 210403630129928244693337)
              ·
                refine ⟨157802722597446183520003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 210403630129928244693337 157802722597446183520003)
                ·
                  refine ⟨236704083896169275280005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 157802722597446183520003 236704083896169275280005)
                  ·
                    refine ⟨44382015730531739115001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 236704083896169275280005 44382015730531739115001)
                    ·
                      rfl

theorem cell23_259301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 2, 2, 2, 1, 4].length) (baseStart_259301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_259301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_259301 prefixEnd_259301 := by exact prefixLift 259301
  have htrace : WordTrace (prefixWord ++ tailWord_259301) baseStart_259301 baseEnd_259301 := by
    simpa [prefixWord, tailWord_259301, baseEnd_259301] using wordTrace_append hprefix tailTrace_259301
  have hstable : (prefixWord ++ tailWord_259301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_259301).length < 2 ^ (prefixWord ++ tailWord_259301).sum := by decide
  have hdescent : baseEnd_259301 < baseStart_259301 := by decide
  rcases family_descends (prefixWord ++ tailWord_259301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_259357 : List Nat := [1, 4, 2, 3, 1, 2, 1, 1, 4, 4]
def baseStart_259357 : Nat := 118140960795 + 259357 * 2 ^ 59
def prefixEnd_259357 : Nat := 4983230072969 + 3 ^ 40 * 259357 * 2
def baseEnd_259357 : Nat := 44391600702748999414915

theorem tailTrace_259357 : CollatzResearch.WordTrace tailWord_259357 prefixEnd_259357 44391600702748999414915 := by
  unfold tailWord_259357
  simp only [CollatzResearch.WordTrace]
  refine ⟨9459526921401358494232325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6306351280934238996154883 9459526921401358494232325)
  ·
    refine ⟨1773661297762754717668561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9459526921401358494232325 1773661297762754717668561)
    ·
      refine ⟨1330245973322066038251421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1773661297762754717668561 1330245973322066038251421)
      ·
        refine ⟨498842239995774764344283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1330245973322066038251421 498842239995774764344283)
        ·
          refine ⟨748263359993662146516425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 498842239995774764344283 748263359993662146516425)
          ·
            refine ⟨561197519995246609887319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 748263359993662146516425 561197519995246609887319)
            ·
              refine ⟨841796279992869914830979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 561197519995246609887319 841796279992869914830979)
              ·
                refine ⟨1262694419989304872246469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 841796279992869914830979 1262694419989304872246469)
                ·
                  refine ⟨236755203747994663546213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1262694419989304872246469 236755203747994663546213)
                  ·
                    refine ⟨44391600702748999414915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 236755203747994663546213 44391600702748999414915)
                    ·
                      rfl

theorem cell23_259357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 1, 1, 4, 4].length) (baseStart_259357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_259357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_259357 prefixEnd_259357 := by exact prefixLift 259357
  have htrace : WordTrace (prefixWord ++ tailWord_259357) baseStart_259357 baseEnd_259357 := by
    simpa [prefixWord, tailWord_259357, baseEnd_259357] using wordTrace_append hprefix tailTrace_259357
  have hstable : (prefixWord ++ tailWord_259357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_259357).length < 2 ^ (prefixWord ++ tailWord_259357).sum := by decide
  have hdescent : baseEnd_259357 < baseStart_259357 := by decide
  rcases family_descends (prefixWord ++ tailWord_259357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_259364 : List Nat := [2, 3, 1, 3, 1, 1, 4, 1, 3, 2, 2]
def baseStart_259364 : Nat := 118140960795 + 259364 * 2 ^ 59
def prefixEnd_259364 : Nat := 4983230072969 + 3 ^ 40 * 259364 * 2
def baseEnd_259364 : Nat := 133178396472828470857213

theorem tailTrace_259364 : CollatzResearch.WordTrace tailWord_259364 prefixEnd_259364 133178396472828470857213 := by
  unfold tailWord_259364
  simp only [CollatzResearch.WordTrace]
  refine ⟨4729891116187999344868573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6306521488250665793158097 4729891116187999344868573)
  ·
    refine ⟨1773709168570499754325715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4729891116187999344868573 1773709168570499754325715)
    ·
      refine ⟨2660563752855749631488573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1773709168570499754325715 2660563752855749631488573)
      ·
        refine ⟨997711407320906111808215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2660563752855749631488573 997711407320906111808215)
        ·
          refine ⟨1496567110981359167712323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 997711407320906111808215 1496567110981359167712323)
          ·
            refine ⟨2244850666472038751568485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1496567110981359167712323 2244850666472038751568485)
            ·
              refine ⟨420909499963507265919091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2244850666472038751568485 420909499963507265919091)
              ·
                refine ⟨631364249945260898878637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 420909499963507265919091 631364249945260898878637)
                ·
                  refine ⟨236761593729472837079489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 631364249945260898878637 236761593729472837079489)
                  ·
                    refine ⟨177571195297104627809617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 236761593729472837079489 177571195297104627809617)
                    ·
                      refine ⟨133178396472828470857213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 177571195297104627809617 133178396472828470857213)
                      ·
                        rfl

theorem cell23_259364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 4, 1, 3, 2, 2].length) (baseStart_259364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_259364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_259364 prefixEnd_259364 := by exact prefixLift 259364
  have htrace : WordTrace (prefixWord ++ tailWord_259364) baseStart_259364 baseEnd_259364 := by
    simpa [prefixWord, tailWord_259364, baseEnd_259364] using wordTrace_append hprefix tailTrace_259364
  have hstable : (prefixWord ++ tailWord_259364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_259364).length < 2 ^ (prefixWord ++ tailWord_259364).sum := by decide
  have hdescent : baseEnd_259364 < baseStart_259364 := by decide
  rcases family_descends (prefixWord ++ tailWord_259364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_259377 : List Nat := [1, 2, 2, 3, 3, 3, 1, 1, 1, 2, 4]
def baseStart_259377 : Nat := 118140960795 + 259377 * 2 ^ 59
def prefixEnd_259377 : Nat := 4983230072969 + 3 ^ 40 * 259377 * 2
def baseEnd_259377 : Nat := 133185071721336919994653

theorem tailTrace_259377 : CollatzResearch.WordTrace tailWord_259377 prefixEnd_259377 133185071721336919994653 := by
  unfold tailWord_259377
  simp only [CollatzResearch.WordTrace]
  refine ⟨9460256381328901909960385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6306837587552601273306923 9460256381328901909960385)
  ·
    refine ⟨7095192285996676432470289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9460256381328901909960385 7095192285996676432470289)
    ·
      refine ⟨5321394214497507324352717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7095192285996676432470289 5321394214497507324352717)
      ·
        refine ⟨1995522830436565246632269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5321394214497507324352717 1995522830436565246632269)
        ·
          refine ⟨748321061413711967487101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1995522830436565246632269 748321061413711967487101)
          ·
            refine ⟨280620398030141987807663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 748321061413711967487101 280620398030141987807663)
            ·
              refine ⟨420930597045212981711495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 280620398030141987807663 420930597045212981711495)
              ·
                refine ⟨631395895567819472567243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 420930597045212981711495 631395895567819472567243)
                ·
                  refine ⟨947093843351729208850865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 631395895567819472567243 947093843351729208850865)
                  ·
                    refine ⟨710320382513796906638149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 947093843351729208850865 710320382513796906638149)
                    ·
                      refine ⟨133185071721336919994653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 710320382513796906638149 133185071721336919994653)
                      ·
                        rfl

theorem cell23_259377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 3, 1, 1, 1, 2, 4].length) (baseStart_259377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_259377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_259377 prefixEnd_259377 := by exact prefixLift 259377
  have htrace : WordTrace (prefixWord ++ tailWord_259377) baseStart_259377 baseEnd_259377 := by
    simpa [prefixWord, tailWord_259377, baseEnd_259377] using wordTrace_append hprefix tailTrace_259377
  have hstable : (prefixWord ++ tailWord_259377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_259377).length < 2 ^ (prefixWord ++ tailWord_259377).sum := by decide
  have hdescent : baseEnd_259377 < baseStart_259377 := by decide
  rcases family_descends (prefixWord ++ tailWord_259377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_259423 : List Nat := [1, 1, 2, 3, 1, 2, 1, 1, 3, 3, 5]
def baseStart_259423 : Nat := 118140960795 + 259423 * 2 ^ 59
def prefixEnd_259423 : Nat := 4983230072969 + 3 ^ 40 * 259423 * 2
def baseEnd_259423 : Nat := 133208691831443740019441

theorem tailTrace_259423 : CollatzResearch.WordTrace tailWord_259423 prefixEnd_259423 133208691831443740019441 := by
  unfold tailWord_259423
  simp only [CollatzResearch.WordTrace]
  refine ⟨9461934139162251766134923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6307956092774834510756615 9461934139162251766134923)
  ·
    refine ⟨14192901208743377649202385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9461934139162251766134923 14192901208743377649202385)
    ·
      refine ⟨10644675906557533236901789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14192901208743377649202385 10644675906557533236901789)
      ·
        refine ⟨3991753464959074963838171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10644675906557533236901789 3991753464959074963838171)
        ·
          refine ⟨5987630197438612445757257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3991753464959074963838171 5987630197438612445757257)
          ·
            refine ⟨4490722648078959334317943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5987630197438612445757257 4490722648078959334317943)
            ·
              refine ⟨6736083972118439001476915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4490722648078959334317943 6736083972118439001476915)
              ·
                refine ⟨10104125958177658502215373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6736083972118439001476915 10104125958177658502215373)
                ·
                  refine ⟨3789047234316621938330765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10104125958177658502215373 3789047234316621938330765)
                  ·
                    refine ⟨1420892712868733226874037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3789047234316621938330765 1420892712868733226874037)
                    ·
                      refine ⟨133208691831443740019441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1420892712868733226874037 133208691831443740019441)
                      ·
                        rfl

theorem cell23_259423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 1, 3, 3, 5].length) (baseStart_259423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_259423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_259423 prefixEnd_259423 := by exact prefixLift 259423
  have htrace : WordTrace (prefixWord ++ tailWord_259423) baseStart_259423 baseEnd_259423 := by
    simpa [prefixWord, tailWord_259423, baseEnd_259423] using wordTrace_append hprefix tailTrace_259423
  have hstable : (prefixWord ++ tailWord_259423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_259423).length < 2 ^ (prefixWord ++ tailWord_259423).sum := by decide
  have hdescent : baseEnd_259423 < baseStart_259423 := by decide
  rcases family_descends (prefixWord ++ tailWord_259423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_259484 : List Nat := [2, 2, 3, 4, 1, 1, 1, 1, 2, 2, 4]
def baseStart_259484 : Nat := 118140960795 + 259484 * 2 ^ 59
def prefixEnd_259484 : Nat := 4983230072969 + 3 ^ 40 * 259484 * 2
def baseEnd_259484 : Nat := 133240014151368001356661

theorem tailTrace_259484 : CollatzResearch.WordTrace tailWord_259484 prefixEnd_259484 133240014151368001356661 := by
  unfold tailWord_259484
  simp only [CollatzResearch.WordTrace]
  refine ⟨4732079495970629592052753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6309439327960839456070337 4732079495970629592052753)
  ·
    refine ⟨3549059621977972194039565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4732079495970629592052753 3549059621977972194039565)
    ·
      refine ⟨1330897358241739572764837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3549059621977972194039565 1330897358241739572764837)
      ·
        refine ⟨249543254670326169893407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1330897358241739572764837 249543254670326169893407)
        ·
          refine ⟨374314882005489254840111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 249543254670326169893407 374314882005489254840111)
          ·
            refine ⟨561472323008233882260167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 374314882005489254840111 561472323008233882260167)
            ·
              refine ⟨842208484512350823390251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 561472323008233882260167 842208484512350823390251)
              ·
                refine ⟨1263312726768526235085377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 842208484512350823390251 1263312726768526235085377)
                ·
                  refine ⟨947484545076394676314033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1263312726768526235085377 947484545076394676314033)
                  ·
                    refine ⟨710613408807296007235525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 947484545076394676314033 710613408807296007235525)
                    ·
                      refine ⟨133240014151368001356661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 710613408807296007235525 133240014151368001356661)
                      ·
                        rfl

theorem cell23_259484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 1, 1, 2, 2, 4].length) (baseStart_259484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_259484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_259484 prefixEnd_259484 := by exact prefixLift 259484
  have htrace : WordTrace (prefixWord ++ tailWord_259484) baseStart_259484 baseEnd_259484 := by
    simpa [prefixWord, tailWord_259484, baseEnd_259484] using wordTrace_append hprefix tailTrace_259484
  have hstable : (prefixWord ++ tailWord_259484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_259484).length < 2 ^ (prefixWord ++ tailWord_259484).sum := by decide
  have hdescent : baseEnd_259484 < baseStart_259484 := by decide
  rcases family_descends (prefixWord ++ tailWord_259484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_259487 : List Nat := [1, 1, 2, 5, 1, 3, 1, 1, 2, 3, 3]
def baseStart_259487 : Nat := 118140960795 + 259487 * 2 ^ 59
def prefixEnd_259487 : Nat := 4983230072969 + 3 ^ 40 * 259487 * 2
def baseEnd_259487 : Nat := 133241554593331489619147

theorem tailTrace_259487 : CollatzResearch.WordTrace tailWord_259487 prefixEnd_259487 133241554593331489619147 := by
  unfold tailWord_259487
  simp only [CollatzResearch.WordTrace]
  refine ⟨9464268410930390696464715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6309512273953593797643143 9464268410930390696464715)
  ·
    refine ⟨14196402616395586044697073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9464268410930390696464715 14196402616395586044697073)
    ·
      refine ⟨10647301962296689533522805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14196402616395586044697073 10647301962296689533522805)
      ·
        refine ⟨998184558965314643767763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10647301962296689533522805 998184558965314643767763)
        ·
          refine ⟨1497276838447971965651645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 998184558965314643767763 1497276838447971965651645)
          ·
            refine ⟨561478814417989487119367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1497276838447971965651645 561478814417989487119367)
            ·
              refine ⟨842218221626984230679051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 561478814417989487119367 842218221626984230679051)
              ·
                refine ⟨1263327332440476346018577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 842218221626984230679051 1263327332440476346018577)
                ·
                  refine ⟨947495499330357259513933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1263327332440476346018577 947495499330357259513933)
                  ·
                    refine ⟨355310812248883972317725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 947495499330357259513933 355310812248883972317725)
                    ·
                      refine ⟨133241554593331489619147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 355310812248883972317725 133241554593331489619147)
                      ·
                        rfl

theorem cell23_259487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 1, 1, 2, 3, 3].length) (baseStart_259487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_259487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_259487 prefixEnd_259487 := by exact prefixLift 259487
  have htrace : WordTrace (prefixWord ++ tailWord_259487) baseStart_259487 baseEnd_259487 := by
    simpa [prefixWord, tailWord_259487, baseEnd_259487] using wordTrace_append hprefix tailTrace_259487
  have hstable : (prefixWord ++ tailWord_259487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_259487).length < 2 ^ (prefixWord ++ tailWord_259487).sum := by decide
  have hdescent : baseEnd_259487 < baseStart_259487 := by decide
  rcases family_descends (prefixWord ++ tailWord_259487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_259522 : List Nat := [3, 5, 2, 1, 1, 1, 1, 1, 4, 2, 2]
def baseStart_259522 : Nat := 118140960795 + 259522 * 2 ^ 59
def prefixEnd_259522 : Nat := 4983230072969 + 3 ^ 40 * 259522 * 2
def baseEnd_259522 : Nat := 133259526416238852681487

theorem tailTrace_259522 : CollatzResearch.WordTrace tailWord_259522 prefixEnd_259522 133259526416238852681487 := by
  unfold tailWord_259522
  simp only [CollatzResearch.WordTrace]
  refine ⟨2366386241450897918497205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6310363310535727782659213 2366386241450897918497205)
  ·
    refine ⟨221848710136021679859113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2366386241450897918497205 221848710136021679859113)
    ·
      refine ⟨166386532602016259894335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221848710136021679859113 166386532602016259894335)
      ·
        refine ⟨249579798903024389841503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166386532602016259894335 249579798903024389841503)
        ·
          refine ⟨374369698354536584762255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 249579798903024389841503 374369698354536584762255)
          ·
            refine ⟨561554547531804877143383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 374369698354536584762255 561554547531804877143383)
            ·
              refine ⟨842331821297707315715075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 561554547531804877143383 842331821297707315715075)
              ·
                refine ⟨1263497731946560973572613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 842331821297707315715075 1263497731946560973572613)
                ·
                  refine ⟨236905824739980182544865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1263497731946560973572613 236905824739980182544865)
                  ·
                    refine ⟨177679368554985136908649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 236905824739980182544865 177679368554985136908649)
                    ·
                      refine ⟨133259526416238852681487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 177679368554985136908649 133259526416238852681487)
                      ·
                        rfl

theorem cell23_259522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 1, 1, 4, 2, 2].length) (baseStart_259522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_259522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_259522 prefixEnd_259522 := by exact prefixLift 259522
  have htrace : WordTrace (prefixWord ++ tailWord_259522) baseStart_259522 baseEnd_259522 := by
    simpa [prefixWord, tailWord_259522, baseEnd_259522] using wordTrace_append hprefix tailTrace_259522
  have hstable : (prefixWord ++ tailWord_259522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_259522).length < 2 ^ (prefixWord ++ tailWord_259522).sum := by decide
  have hdescent : baseEnd_259522 < baseStart_259522 := by decide
  rcases family_descends (prefixWord ++ tailWord_259522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_259527 : List Nat := [1, 1, 4, 1, 1, 3, 1, 1, 4, 4, 2]
def baseStart_259527 : Nat := 118140960795 + 259527 * 2 ^ 59
def prefixEnd_259527 : Nat := 4983230072969 + 3 ^ 40 * 259527 * 2
def baseEnd_259527 : Nat := 133262093819511333118963

theorem tailTrace_259527 : CollatzResearch.WordTrace tailWord_259527 prefixEnd_259527 133262093819511333118963 := by
  unfold tailWord_259527
  simp only [CollatzResearch.WordTrace]
  refine ⟨9465727330785477527920835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6310484887190318351947223 9465727330785477527920835)
  ·
    refine ⟨14198590996178216291881253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9465727330785477527920835 14198590996178216291881253)
    ·
      refine ⟨2662235811783415554727735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14198590996178216291881253 2662235811783415554727735)
      ·
        refine ⟨3993353717675123332091603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2662235811783415554727735 3993353717675123332091603)
        ·
          refine ⟨5990030576512684998137405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3993353717675123332091603 5990030576512684998137405)
          ·
            refine ⟨2246261466192256874301527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5990030576512684998137405 2246261466192256874301527)
            ·
              refine ⟨3369392199288385311452291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2246261466192256874301527 3369392199288385311452291)
              ·
                refine ⟨5054088298932577967178437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3369392199288385311452291 5054088298932577967178437)
                ·
                  refine ⟨947641556049858368845957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5054088298932577967178437 947641556049858368845957)
                  ·
                    refine ⟨177682791759348444158617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 947641556049858368845957 177682791759348444158617)
                    ·
                      refine ⟨133262093819511333118963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 177682791759348444158617 133262093819511333118963)
                      ·
                        rfl

theorem cell23_259527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 1, 4, 4, 2].length) (baseStart_259527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_259527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_259527 prefixEnd_259527 := by exact prefixLift 259527
  have htrace : WordTrace (prefixWord ++ tailWord_259527) baseStart_259527 baseEnd_259527 := by
    simpa [prefixWord, tailWord_259527, baseEnd_259527] using wordTrace_append hprefix tailTrace_259527
  have hstable : (prefixWord ++ tailWord_259527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_259527).length < 2 ^ (prefixWord ++ tailWord_259527).sum := by decide
  have hdescent : baseEnd_259527 < baseStart_259527 := by decide
  rcases family_descends (prefixWord ++ tailWord_259527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_259587 : List Nat := [1, 1, 1, 3, 2, 1, 2, 2, 3, 5, 2]
def baseStart_259587 : Nat := 118140960795 + 259587 * 2 ^ 59
def prefixEnd_259587 : Nat := 4983230072969 + 3 ^ 40 * 259587 * 2
def baseEnd_259587 : Nat := 133292902658781098368687

theorem tailTrace_259587 : CollatzResearch.WordTrace tailWord_259587 prefixEnd_259587 133292902658781098368687 := by
  unfold tailWord_259587
  simp only [CollatzResearch.WordTrace]
  refine ⟨9467915710568107775105015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6311943807045405183403343 9467915710568107775105015)
  ·
    refine ⟨14201873565852161662657523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9467915710568107775105015 14201873565852161662657523)
    ·
      refine ⟨21302810348778242493986285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14201873565852161662657523 21302810348778242493986285)
      ·
        refine ⟨7988553880791840935244857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21302810348778242493986285 7988553880791840935244857)
        ·
          refine ⟨5991415410593880701433643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7988553880791840935244857 5991415410593880701433643)
          ·
            refine ⟨8987123115890821052150465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5991415410593880701433643 8987123115890821052150465)
            ·
              refine ⟨6740342336918115789112849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8987123115890821052150465 6740342336918115789112849)
              ·
                refine ⟨5055256752688586841834637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6740342336918115789112849 5055256752688586841834637)
                ·
                  refine ⟨1895721282258220065687989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5055256752688586841834637 1895721282258220065687989)
                  ·
                    refine ⟨177723870211708131158249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1895721282258220065687989 177723870211708131158249)
                    ·
                      refine ⟨133292902658781098368687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 177723870211708131158249 133292902658781098368687)
                      ·
                        rfl

theorem cell23_259587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 2, 3, 5, 2].length) (baseStart_259587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_259587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_259587 prefixEnd_259587 := by exact prefixLift 259587
  have htrace : WordTrace (prefixWord ++ tailWord_259587) baseStart_259587 baseEnd_259587 := by
    simpa [prefixWord, tailWord_259587, baseEnd_259587] using wordTrace_append hprefix tailTrace_259587
  have hstable : (prefixWord ++ tailWord_259587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_259587).length < 2 ^ (prefixWord ++ tailWord_259587).sum := by decide
  have hdescent : baseEnd_259587 < baseStart_259587 := by decide
  rcases family_descends (prefixWord ++ tailWord_259587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_259588 : List Nat := [2, 3, 2, 3, 3, 1, 1, 1, 3, 4]
def baseStart_259588 : Nat := 118140960795 + 259588 * 2 ^ 59
def prefixEnd_259588 : Nat := 4983230072969 + 3 ^ 40 * 259588 * 2
def baseEnd_259588 : Nat := 44431138713145198152061

theorem tailTrace_259588 : CollatzResearch.WordTrace tailWord_259588 prefixEnd_259588 44431138713145198152061 := by
  unfold tailWord_259588
  simp only [CollatzResearch.WordTrace]
  refine ⟨4733976091782242472945709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6311968122376323297260945 4733976091782242472945709)
  ·
    refine ⟨1775241034418340927354641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4733976091782242472945709 1775241034418340927354641)
    ·
      refine ⟨1331430775813755695515981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1775241034418340927354641 1331430775813755695515981)
      ·
        refine ⟨499286540930158385818493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1331430775813755695515981 499286540930158385818493)
        ·
          refine ⟨187232452848809394681935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 499286540930158385818493 187232452848809394681935)
          ·
            refine ⟨280848679273214092022903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187232452848809394681935 280848679273214092022903)
            ·
              refine ⟨421273018909821138034355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 280848679273214092022903 421273018909821138034355)
              ·
                refine ⟨631909528364731707051533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 421273018909821138034355 631909528364731707051533)
                ·
                  refine ⟨236966073136774390144325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 631909528364731707051533 236966073136774390144325)
                  ·
                    refine ⟨44431138713145198152061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 236966073136774390144325 44431138713145198152061)
                    ·
                      rfl

theorem cell23_259588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 1, 1, 1, 3, 4].length) (baseStart_259588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_259588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_259588 prefixEnd_259588 := by exact prefixLift 259588
  have htrace : WordTrace (prefixWord ++ tailWord_259588) baseStart_259588 baseEnd_259588 := by
    simpa [prefixWord, tailWord_259588, baseEnd_259588] using wordTrace_append hprefix tailTrace_259588
  have hstable : (prefixWord ++ tailWord_259588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_259588).length < 2 ^ (prefixWord ++ tailWord_259588).sum := by decide
  have hdescent : baseEnd_259588 < baseStart_259588 := by decide
  rcases family_descends (prefixWord ++ tailWord_259588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_259640 : List Nat := [2, 1, 2, 1, 4, 13]
def baseStart_259640 : Nat := 118140960795 + 259640 * 2 ^ 59
def prefixEnd_259640 : Nat := 4983230072969 + 3 ^ 40 * 259640 * 2
def baseEnd_259640 : Nat := 548642457339380209901

theorem tailTrace_259640 : CollatzResearch.WordTrace tailWord_259640 prefixEnd_259640 548642457339380209901 := by
  unfold tailWord_259640
  simp only [CollatzResearch.WordTrace]
  refine ⟨4734924389688048913392187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6313232519584065217856249 4734924389688048913392187)
  ·
    refine ⟨7102386584532073370088281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4734924389688048913392187 7102386584532073370088281)
    ·
      refine ⟨5326789938399055027566211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7102386584532073370088281 5326789938399055027566211)
      ·
        refine ⟨7990184907598582541349317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5326789938399055027566211 7990184907598582541349317)
        ·
          refine ⟨1498159670174734226502997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7990184907598582541349317 1498159670174734226502997)
          ·
            refine ⟨548642457339380209901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 1498159670174734226502997 548642457339380209901)
            ·
              rfl

theorem cell23_259640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 13].length) (baseStart_259640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_259640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_259640 prefixEnd_259640 := by exact prefixLift 259640
  have htrace : WordTrace (prefixWord ++ tailWord_259640) baseStart_259640 baseEnd_259640 := by
    simpa [prefixWord, tailWord_259640, baseEnd_259640] using wordTrace_append hprefix tailTrace_259640
  have hstable : (prefixWord ++ tailWord_259640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_259640).length < 2 ^ (prefixWord ++ tailWord_259640).sum := by decide
  have hdescent : baseEnd_259640 < baseStart_259640 := by decide
  rcases family_descends (prefixWord ++ tailWord_259640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_259661 : List Nat := [1, 6, 1, 1, 3, 1, 2, 1, 1, 6]
def baseStart_259661 : Nat := 118140960795 + 259661 * 2 ^ 59
def prefixEnd_259661 : Nat := 4983230072969 + 3 ^ 40 * 259661 * 2
def baseEnd_259661 : Nat := 44443633409071269614449

theorem tailTrace_259661 : CollatzResearch.WordTrace tailWord_259661 prefixEnd_259661 44443633409071269614449 := by
  unfold tailWord_259661
  simp only [CollatzResearch.WordTrace]
  refine ⟨9470614712300018413298837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6313743141533345608865891 9470614712300018413298837)
  ·
    refine ⟨443935064639063363123383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 9470614712300018413298837 443935064639063363123383)
    ·
      refine ⟨665902596958595044685075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 443935064639063363123383 665902596958595044685075)
      ·
        refine ⟨998853895437892567027613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 665902596958595044685075 998853895437892567027613)
        ·
          refine ⟨374570210789209712635355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 998853895437892567027613 374570210789209712635355)
          ·
            refine ⟨561855316183814568953033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 374570210789209712635355 561855316183814568953033)
            ·
              refine ⟨421391487137860926714775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 561855316183814568953033 421391487137860926714775)
              ·
                refine ⟨632087230706791390072163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 421391487137860926714775 632087230706791390072163)
                ·
                  refine ⟨948130846060187085108245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 632087230706791390072163 948130846060187085108245)
                  ·
                    refine ⟨44443633409071269614449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 948130846060187085108245 44443633409071269614449)
                    ·
                      rfl

theorem cell23_259661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 2, 1, 1, 6].length) (baseStart_259661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_259661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_259661 prefixEnd_259661 := by exact prefixLift 259661
  have htrace : WordTrace (prefixWord ++ tailWord_259661) baseStart_259661 baseEnd_259661 := by
    simpa [prefixWord, tailWord_259661, baseEnd_259661] using wordTrace_append hprefix tailTrace_259661
  have hstable : (prefixWord ++ tailWord_259661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_259661).length < 2 ^ (prefixWord ++ tailWord_259661).sum := by decide
  have hdescent : baseEnd_259661 < baseStart_259661 := by decide
  rcases family_descends (prefixWord ++ tailWord_259661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_259684 : List Nat := [2, 3, 1, 1, 2, 3, 2, 2, 1, 3, 3]
def baseStart_259684 : Nat := 118140960795 + 259684 * 2 ^ 59
def prefixEnd_259684 : Nat := 4983230072969 + 3 ^ 40 * 259684 * 2
def baseEnd_259684 : Nat := 133342710282267218855741

theorem tailTrace_259684 : CollatzResearch.WordTrace tailWord_259684 prefixEnd_259684 133342710282267218855741 := by
  unfold tailWord_259684
  simp only [CollatzResearch.WordTrace]
  refine ⟨4735726795608346670693053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6314302394144462227590737 4735726795608346670693053)
  ·
    refine ⟨1775897548353130001509895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4735726795608346670693053 1775897548353130001509895)
    ·
      refine ⟨2663846322529695002264843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1775897548353130001509895 2663846322529695002264843)
      ·
        refine ⟨3995769483794542503397265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2663846322529695002264843 3995769483794542503397265)
        ·
          refine ⟨2996827112845906877547949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3995769483794542503397265 2996827112845906877547949)
          ·
            refine ⟨1123810167317215079080481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2996827112845906877547949 1123810167317215079080481)
            ·
              refine ⟨842857625487911309310361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1123810167317215079080481 842857625487911309310361)
              ·
                refine ⟨632143219115933481982771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 842857625487911309310361 632143219115933481982771)
                ·
                  refine ⟨948214828673900222974157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 632143219115933481982771 948214828673900222974157)
                  ·
                    refine ⟨355580560752712583615309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 948214828673900222974157 355580560752712583615309)
                    ·
                      refine ⟨133342710282267218855741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 355580560752712583615309 133342710282267218855741)
                      ·
                        rfl

theorem cell23_259684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 2, 2, 1, 3, 3].length) (baseStart_259684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_259684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_259684 prefixEnd_259684 := by exact prefixLift 259684
  have htrace : WordTrace (prefixWord ++ tailWord_259684) baseStart_259684 baseEnd_259684 := by
    simpa [prefixWord, tailWord_259684, baseEnd_259684] using wordTrace_append hprefix tailTrace_259684
  have hstable : (prefixWord ++ tailWord_259684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_259684).length < 2 ^ (prefixWord ++ tailWord_259684).sum := by decide
  have hdescent : baseEnd_259684 < baseStart_259684 := by decide
  rcases family_descends (prefixWord ++ tailWord_259684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_259685 : List Nat := [1, 3, 1, 3, 3, 2, 2, 3, 1, 2, 2]
def baseStart_259685 : Nat := 118140960795 + 259685 * 2 ^ 59
def prefixEnd_259685 : Nat := 4983230072969 + 3 ^ 40 * 259685 * 2
def baseEnd_259685 : Nat := 133343223762921714943237

theorem tailTrace_259685 : CollatzResearch.WordTrace tailWord_259685 prefixEnd_259685 133343223762921714943237 := by
  unfold tailWord_259685
  simp only [CollatzResearch.WordTrace]
  refine ⟨9471490064213070512172509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6314326709475380341448339 9471490064213070512172509)
  ·
    refine ⟨3551808774079901442064691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9471490064213070512172509 3551808774079901442064691)
    ·
      refine ⟨5327713161119852163097037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3551808774079901442064691 5327713161119852163097037)
      ·
        refine ⟨1997892435419944561161389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5327713161119852163097037 1997892435419944561161389)
        ·
          refine ⟨749209663282479210435521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1997892435419944561161389 749209663282479210435521)
          ·
            refine ⟨561907247461859407826641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 749209663282479210435521 561907247461859407826641)
            ·
              refine ⟨421430435596394555869981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 561907247461859407826641 421430435596394555869981)
              ·
                refine ⟨158036413348647958451243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 421430435596394555869981 158036413348647958451243)
                ·
                  refine ⟨237054620022971937676865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 158036413348647958451243 237054620022971937676865)
                  ·
                    refine ⟨177790965017228953257649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 237054620022971937676865 177790965017228953257649)
                    ·
                      refine ⟨133343223762921714943237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 177790965017228953257649 133343223762921714943237)
                      ·
                        rfl

theorem cell23_259685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 2, 3, 1, 2, 2].length) (baseStart_259685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_259685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_259685 prefixEnd_259685 := by exact prefixLift 259685
  have htrace : WordTrace (prefixWord ++ tailWord_259685) baseStart_259685 baseEnd_259685 := by
    simpa [prefixWord, tailWord_259685, baseEnd_259685] using wordTrace_append hprefix tailTrace_259685
  have hstable : (prefixWord ++ tailWord_259685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_259685).length < 2 ^ (prefixWord ++ tailWord_259685).sum := by decide
  have hdescent : baseEnd_259685 < baseStart_259685 := by decide
  rcases family_descends (prefixWord ++ tailWord_259685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_259688 : List Nat := [2, 1, 4, 3, 1, 1, 4, 1, 1, 2, 3]
def baseStart_259688 : Nat := 118140960795 + 259688 * 2 ^ 59
def prefixEnd_259688 : Nat := 4983230072969 + 3 ^ 40 * 259688 * 2
def baseEnd_259688 : Nat := 133344764204885203205723

theorem tailTrace_259688 : CollatzResearch.WordTrace tailWord_259688 prefixEnd_259688 133344764204885203205723 := by
  unfold tailWord_259688
  simp only [CollatzResearch.WordTrace]
  refine ⟨4735799741601101012265859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6314399655468134683021145 4735799741601101012265859)
  ·
    refine ⟨7103699612401651518398789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4735799741601101012265859 7103699612401651518398789)
    ·
      refine ⟨1331943677325309659699773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7103699612401651518398789 1331943677325309659699773)
      ·
        refine ⟨499478878996991122387415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1331943677325309659699773 499478878996991122387415)
        ·
          refine ⟨749218318495486683581123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 499478878996991122387415 749218318495486683581123)
          ·
            refine ⟨1123827477743230025371685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 749218318495486683581123 1123827477743230025371685)
            ·
              refine ⟨210717652076855629757191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1123827477743230025371685 210717652076855629757191)
              ·
                refine ⟨316076478115283444635787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 210717652076855629757191 316076478115283444635787)
                ·
                  refine ⟨474114717172925166953681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 316076478115283444635787 474114717172925166953681)
                  ·
                    refine ⟨355586037879693875215261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 474114717172925166953681 355586037879693875215261)
                    ·
                      refine ⟨133344764204885203205723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 355586037879693875215261 133344764204885203205723)
                      ·
                        rfl

theorem cell23_259688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 4, 1, 1, 2, 3].length) (baseStart_259688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_259688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_259688 prefixEnd_259688 := by exact prefixLift 259688
  have htrace : WordTrace (prefixWord ++ tailWord_259688) baseStart_259688 baseEnd_259688 := by
    simpa [prefixWord, tailWord_259688, baseEnd_259688] using wordTrace_append hprefix tailTrace_259688
  have hstable : (prefixWord ++ tailWord_259688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_259688).length < 2 ^ (prefixWord ++ tailWord_259688).sum := by decide
  have hdescent : baseEnd_259688 < baseStart_259688 := by decide
  rcases family_descends (prefixWord ++ tailWord_259688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_259717 : List Nat := [1, 3, 1, 1, 4, 1, 1, 3, 2, 6]
def baseStart_259717 : Nat := 118140960795 + 259717 * 2 ^ 59
def prefixEnd_259717 : Nat := 4983230072969 + 3 ^ 40 * 259717 * 2
def baseEnd_259717 : Nat := 44453218381288529914363

theorem tailTrace_259717 : CollatzResearch.WordTrace tailWord_259717 prefixEnd_259717 44453218381288529914363 := by
  unfold tailWord_259717
  simp only [CollatzResearch.WordTrace]
  refine ⟨9472657200097139977337405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6315104800064759984891603 9472657200097139977337405)
  ·
    refine ⟨3552246450036427491501527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9472657200097139977337405 3552246450036427491501527)
    ·
      refine ⟨5328369675054641237252291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3552246450036427491501527 5328369675054641237252291)
      ·
        refine ⟨7992554512581961855878437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5328369675054641237252291 7992554512581961855878437)
        ·
          refine ⟨1498603971109117847977207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7992554512581961855878437 1498603971109117847977207)
          ·
            refine ⟨2247905956663676771965811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1498603971109117847977207 2247905956663676771965811)
            ·
              refine ⟨3371858934995515157948717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2247905956663676771965811 3371858934995515157948717)
              ·
                refine ⟨1264447100623318184230769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3371858934995515157948717 1264447100623318184230769)
                ·
                  refine ⟨948335325467488638173077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1264447100623318184230769 948335325467488638173077)
                  ·
                    refine ⟨44453218381288529914363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 948335325467488638173077 44453218381288529914363)
                    ·
                      rfl

theorem cell23_259717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 3, 2, 6].length) (baseStart_259717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_259717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_259717 prefixEnd_259717 := by exact prefixLift 259717
  have htrace : WordTrace (prefixWord ++ tailWord_259717) baseStart_259717 baseEnd_259717 := by
    simpa [prefixWord, tailWord_259717, baseEnd_259717] using wordTrace_append hprefix tailTrace_259717
  have hstable : (prefixWord ++ tailWord_259717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_259717).length < 2 ^ (prefixWord ++ tailWord_259717).sum := by decide
  have hdescent : baseEnd_259717 < baseStart_259717 := by decide
  rcases family_descends (prefixWord ++ tailWord_259717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_259737 : List Nat := [1, 2, 1, 2, 1, 2, 2, 2, 4, 2, 4]
def baseStart_259737 : Nat := 118140960795 + 259737 * 2 ^ 59
def prefixEnd_259737 : Nat := 4983230072969 + 3 ^ 40 * 259737 * 2
def baseEnd_259737 : Nat := 133369924756955511492997

theorem tailTrace_259737 : CollatzResearch.WordTrace tailWord_259737 prefixEnd_259737 133369924756955511492997 := by
  unfold tailWord_259737
  simp only [CollatzResearch.WordTrace]
  refine ⟨9473386660024683393065465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6315591106683122262043643 9473386660024683393065465)
  ·
    refine ⟨7105039995018512544799099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9473386660024683393065465 7105039995018512544799099)
    ·
      refine ⟨10657559992527768817198649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7105039995018512544799099 10657559992527768817198649)
      ·
        refine ⟨7993169994395826612898987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10657559992527768817198649 7993169994395826612898987)
        ·
          refine ⟨11989754991593739919348481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7993169994395826612898987 11989754991593739919348481)
          ·
            refine ⟨8992316243695304939511361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11989754991593739919348481 8992316243695304939511361)
            ·
              refine ⟨6744237182771478704633521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8992316243695304939511361 6744237182771478704633521)
              ·
                refine ⟨5058177887078609028475141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6744237182771478704633521 5058177887078609028475141)
                ·
                  refine ⟨948408353827239192839089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5058177887078609028475141 948408353827239192839089)
                  ·
                    refine ⟨711306265370429394629317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 948408353827239192839089 711306265370429394629317)
                    ·
                      refine ⟨133369924756955511492997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 711306265370429394629317 133369924756955511492997)
                      ·
                        rfl

theorem cell23_259737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 2, 4, 2, 4].length) (baseStart_259737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_259737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_259737 prefixEnd_259737 := by exact prefixLift 259737
  have htrace : WordTrace (prefixWord ++ tailWord_259737) baseStart_259737 baseEnd_259737 := by
    simpa [prefixWord, tailWord_259737, baseEnd_259737] using wordTrace_append hprefix tailTrace_259737
  have hstable : (prefixWord ++ tailWord_259737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_259737).length < 2 ^ (prefixWord ++ tailWord_259737).sum := by decide
  have hdescent : baseEnd_259737 < baseStart_259737 := by decide
  rcases family_descends (prefixWord ++ tailWord_259737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_259744 : List Nat := [2, 1, 1, 4, 3, 2, 1, 1, 2, 1, 5]
def baseStart_259744 : Nat := 118140960795 + 259744 * 2 ^ 59
def prefixEnd_259744 : Nat := 4983230072969 + 3 ^ 40 * 259744 * 2
def baseEnd_259744 : Nat := 133373519121536984105465

theorem tailTrace_259744 : CollatzResearch.WordTrace tailWord_259744 prefixEnd_259744 133373519121536984105465 := by
  unfold tailWord_259744
  simp only [CollatzResearch.WordTrace]
  refine ⟨4736820985499661794285143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6315761313999549059046857 4736820985499661794285143)
  ·
    refine ⟨7105231478249492691427715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4736820985499661794285143 7105231478249492691427715)
    ·
      refine ⟨10657847217374239037141573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7105231478249492691427715 10657847217374239037141573)
      ·
        refine ⟨1998346353257669819464045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10657847217374239037141573 1998346353257669819464045)
        ·
          refine ⟨749379882471626182299017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1998346353257669819464045 749379882471626182299017)
          ·
            refine ⟨562034911853719636724263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 749379882471626182299017 562034911853719636724263)
            ·
              refine ⟨843052367780579455086395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 562034911853719636724263 843052367780579455086395)
              ·
                refine ⟨1264578551670869182629593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 843052367780579455086395 1264578551670869182629593)
                ·
                  refine ⟨948433913753151886972195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1264578551670869182629593 948433913753151886972195)
                  ·
                    refine ⟨1422650870629727830458293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 948433913753151886972195 1422650870629727830458293)
                    ·
                      refine ⟨133373519121536984105465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1422650870629727830458293 133373519121536984105465)
                      ·
                        rfl

theorem cell23_259744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 1, 1, 2, 1, 5].length) (baseStart_259744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_259744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_259744 prefixEnd_259744 := by exact prefixLift 259744
  have htrace : WordTrace (prefixWord ++ tailWord_259744) baseStart_259744 baseEnd_259744 := by
    simpa [prefixWord, tailWord_259744, baseEnd_259744] using wordTrace_append hprefix tailTrace_259744
  have hstable : (prefixWord ++ tailWord_259744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_259744).length < 2 ^ (prefixWord ++ tailWord_259744).sum := by decide
  have hdescent : baseEnd_259744 < baseStart_259744 := by decide
  rcases family_descends (prefixWord ++ tailWord_259744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_259817 : List Nat := [1, 2, 1, 1, 1, 2, 3, 1, 1, 5, 5]
def baseStart_259817 : Nat := 118140960795 + 259817 * 2 ^ 59
def prefixEnd_259817 : Nat := 4983230072969 + 3 ^ 40 * 259817 * 2
def baseEnd_259817 : Nat := 133411003209315198492629

theorem tailTrace_259817 : CollatzResearch.WordTrace tailWord_259817 prefixEnd_259817 133411003209315198492629 := by
  unfold tailWord_259817
  simp only [CollatzResearch.WordTrace]
  refine ⟨9476304499734857055977705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6317536333156571370651803 9476304499734857055977705)
  ·
    refine ⟨7107228374801142791983279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9476304499734857055977705 7107228374801142791983279)
    ·
      refine ⟨10660842562201714187974919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7107228374801142791983279 10660842562201714187974919)
      ·
        refine ⟨15991263843302571281962379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10660842562201714187974919 15991263843302571281962379)
        ·
          refine ⟨23986895764953856922943569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15991263843302571281962379 23986895764953856922943569)
          ·
            refine ⟨17990171823715392692207677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23986895764953856922943569 17990171823715392692207677)
            ·
              refine ⟨6746314433893272259577879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17990171823715392692207677 6746314433893272259577879)
              ·
                refine ⟨10119471650839908389366819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6746314433893272259577879 10119471650839908389366819)
                ·
                  refine ⟨15179207476259862584050229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10119471650839908389366819 15179207476259862584050229)
                  ·
                    refine ⟨1423050700899362117254709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15179207476259862584050229 1423050700899362117254709)
                    ·
                      refine ⟨133411003209315198492629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1423050700899362117254709 133411003209315198492629)
                      ·
                        rfl

theorem cell23_259817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 1, 1, 5, 5].length) (baseStart_259817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_259817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_259817 prefixEnd_259817 := by exact prefixLift 259817
  have htrace : WordTrace (prefixWord ++ tailWord_259817) baseStart_259817 baseEnd_259817 := by
    simpa [prefixWord, tailWord_259817, baseEnd_259817] using wordTrace_append hprefix tailTrace_259817
  have hstable : (prefixWord ++ tailWord_259817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_259817).length < 2 ^ (prefixWord ++ tailWord_259817).sum := by decide
  have hdescent : baseEnd_259817 < baseStart_259817 := by decide
  rcases family_descends (prefixWord ++ tailWord_259817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_259834 : List Nat := [3, 1, 1, 1, 1, 3, 1, 4, 1, 4, 3]
def baseStart_259834 : Nat := 118140960795 + 259834 * 2 ^ 59
def prefixEnd_259834 : Nat := 4983230072969 + 3 ^ 40 * 259834 * 2
def baseEnd_259834 : Nat := 133419732380441631980051

theorem tailTrace_259834 : CollatzResearch.WordTrace tailWord_259834 prefixEnd_259834 133419732380441631980051 := by
  unfold tailWord_259834
  simp only [CollatzResearch.WordTrace]
  refine ⟨2369231135168317239836639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6317949693782179306231037 2369231135168317239836639)
  ·
    refine ⟨3553846702752475859754959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2369231135168317239836639 3553846702752475859754959)
    ·
      refine ⟨5330770054128713789632439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3553846702752475859754959 5330770054128713789632439)
      ·
        refine ⟨7996155081193070684448659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5330770054128713789632439 7996155081193070684448659)
        ·
          refine ⟨11994232621789606026672989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7996155081193070684448659 11994232621789606026672989)
          ·
            refine ⟨4497837233171102260002371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11994232621789606026672989 4497837233171102260002371)
            ·
              refine ⟨6746755849756653390003557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4497837233171102260002371 6746755849756653390003557)
              ·
                refine ⟨1265016721829372510625667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6746755849756653390003557 1265016721829372510625667)
                ·
                  refine ⟨1897525082744058765938501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1265016721829372510625667 1897525082744058765938501)
                  ·
                    refine ⟨355785953014511018613469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1897525082744058765938501 355785953014511018613469)
                    ·
                      refine ⟨133419732380441631980051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 355785953014511018613469 133419732380441631980051)
                      ·
                        rfl

theorem cell23_259834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 4, 1, 4, 3].length) (baseStart_259834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_259834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_259834 prefixEnd_259834 := by exact prefixLift 259834
  have htrace : WordTrace (prefixWord ++ tailWord_259834) baseStart_259834 baseEnd_259834 := by
    simpa [prefixWord, tailWord_259834, baseEnd_259834] using wordTrace_append hprefix tailTrace_259834
  have hstable : (prefixWord ++ tailWord_259834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_259834).length < 2 ^ (prefixWord ++ tailWord_259834).sum := by decide
  have hdescent : baseEnd_259834 < baseStart_259834 := by decide
  rcases family_descends (prefixWord ++ tailWord_259834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_259851 : List Nat := [1, 1, 1, 1, 5, 1, 5, 1, 2, 2, 3]
def baseStart_259851 : Nat := 118140960795 + 259851 * 2 ^ 59
def prefixEnd_259851 : Nat := 4983230072969 + 3 ^ 40 * 259851 * 2
def baseEnd_259851 : Nat := 133428461551568065467473

theorem tailTrace_259851 : CollatzResearch.WordTrace tailWord_259851 prefixEnd_259851 133428461551568065467473 := by
  unfold tailWord_259851
  simp only [CollatzResearch.WordTrace]
  refine ⟨9477544581611680862715407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6318363054407787241810271 9477544581611680862715407)
  ·
    refine ⟨14216316872417521294073111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9477544581611680862715407 14216316872417521294073111)
    ·
      refine ⟨21324475308626281941109667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14216316872417521294073111 21324475308626281941109667)
      ·
        refine ⟨31986712962939422911664501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21324475308626281941109667 31986712962939422911664501)
        ·
          refine ⟨2998754340275570897968547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 31986712962939422911664501 2998754340275570897968547)
          ·
            refine ⟨4498131510413356346952821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2998754340275570897968547 4498131510413356346952821)
            ·
              refine ⟨421699829101252157526827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4498131510413356346952821 421699829101252157526827)
              ·
                refine ⟨632549743651878236290241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 421699829101252157526827 632549743651878236290241)
                ·
                  refine ⟨474412307738908677217681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 632549743651878236290241 474412307738908677217681)
                  ·
                    refine ⟨355809230804181507913261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 474412307738908677217681 355809230804181507913261)
                    ·
                      refine ⟨133428461551568065467473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 355809230804181507913261 133428461551568065467473)
                      ·
                        rfl

theorem cell23_259851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 5, 1, 2, 2, 3].length) (baseStart_259851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_259851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_259851 prefixEnd_259851 := by exact prefixLift 259851
  have htrace : WordTrace (prefixWord ++ tailWord_259851) baseStart_259851 baseEnd_259851 := by
    simpa [prefixWord, tailWord_259851, baseEnd_259851] using wordTrace_append hprefix tailTrace_259851
  have hstable : (prefixWord ++ tailWord_259851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_259851).length < 2 ^ (prefixWord ++ tailWord_259851).sum := by decide
  have hdescent : baseEnd_259851 < baseStart_259851 := by decide
  rcases family_descends (prefixWord ++ tailWord_259851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_259874 : List Nat := [3, 3, 1, 1, 2, 1, 1, 1, 1, 1, 8]
def baseStart_259874 : Nat := 118140960795 + 259874 * 2 ^ 59
def prefixEnd_259874 : Nat := 4983230072969 + 3 ^ 40 * 259874 * 2
def baseEnd_259874 : Nat := 133440271606621475479867

theorem tailTrace_259874 : CollatzResearch.WordTrace tailWord_259874 prefixEnd_259874 133440271606621475479867 := by
  unfold tailWord_259874
  simp only [CollatzResearch.WordTrace]
  refine ⟨2369595865132088947700669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6318922307018903860535117 2369595865132088947700669)
  ·
    refine ⟨888598449424533355387751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2369595865132088947700669 888598449424533355387751)
    ·
      refine ⟨1332897674136800033081627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 888598449424533355387751 1332897674136800033081627)
      ·
        refine ⟨1999346511205200049622441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1332897674136800033081627 1999346511205200049622441)
        ·
          refine ⟨1499509883403900037216831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1999346511205200049622441 1499509883403900037216831)
          ·
            refine ⟨2249264825105850055825247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1499509883403900037216831 2249264825105850055825247)
            ·
              refine ⟨3373897237658775083737871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2249264825105850055825247 3373897237658775083737871)
              ·
                refine ⟨5060845856488162625606807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3373897237658775083737871 5060845856488162625606807)
                ·
                  refine ⟨7591268784732243938410211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5060845856488162625606807 7591268784732243938410211)
                  ·
                    refine ⟨11386903177098365907615317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7591268784732243938410211 11386903177098365907615317)
                    ·
                      refine ⟨133440271606621475479867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 11386903177098365907615317 133440271606621475479867)
                      ·
                        rfl

theorem cell23_259874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 1, 1, 1, 8].length) (baseStart_259874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_259874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_259874 prefixEnd_259874 := by exact prefixLift 259874
  have htrace : WordTrace (prefixWord ++ tailWord_259874) baseStart_259874 baseEnd_259874 := by
    simpa [prefixWord, tailWord_259874, baseEnd_259874] using wordTrace_append hprefix tailTrace_259874
  have hstable : (prefixWord ++ tailWord_259874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_259874).length < 2 ^ (prefixWord ++ tailWord_259874).sum := by decide
  have hdescent : baseEnd_259874 < baseStart_259874 := by decide
  rcases family_descends (prefixWord ++ tailWord_259874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_259898 : List Nat := [3, 1, 1, 1, 5, 1, 2, 2, 3, 1, 3]
def baseStart_259898 : Nat := 118140960795 + 259898 * 2 ^ 59
def prefixEnd_259898 : Nat := 4983230072969 + 3 ^ 40 * 259898 * 2
def baseEnd_259898 : Nat := 133452595142329381579757

theorem tailTrace_259898 : CollatzResearch.WordTrace tailWord_259898 prefixEnd_259898 133452595142329381579757 := by
  unfold tailWord_259898
  simp only [CollatzResearch.WordTrace]
  refine ⟨2369814703110351972419087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6319505874960938593117565 2369814703110351972419087)
  ·
    refine ⟨3554722054665527958628631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2369814703110351972419087 3554722054665527958628631)
    ·
      refine ⟨5332083081998291937942947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3554722054665527958628631 5332083081998291937942947)
      ·
        refine ⟨7998124622997437906914421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5332083081998291937942947 7998124622997437906914421)
        ·
          refine ⟨749824183406009803773227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7998124622997437906914421 749824183406009803773227)
          ·
            refine ⟨1124736275109014705659841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 749824183406009803773227 1124736275109014705659841)
            ·
              refine ⟨843552206331761029244881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1124736275109014705659841 843552206331761029244881)
              ·
                refine ⟨632664154748820771933661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 843552206331761029244881 632664154748820771933661)
                ·
                  refine ⟨237249058030807789475123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 632664154748820771933661 237249058030807789475123)
                  ·
                    refine ⟨355873587046211684212685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 237249058030807789475123 355873587046211684212685)
                    ·
                      refine ⟨133452595142329381579757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 355873587046211684212685 133452595142329381579757)
                      ·
                        rfl

theorem cell23_259898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 2, 2, 3, 1, 3].length) (baseStart_259898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_259898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_259898 prefixEnd_259898 := by exact prefixLift 259898
  have htrace : WordTrace (prefixWord ++ tailWord_259898) baseStart_259898 baseEnd_259898 := by
    simpa [prefixWord, tailWord_259898, baseEnd_259898] using wordTrace_append hprefix tailTrace_259898
  have hstable : (prefixWord ++ tailWord_259898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_259898).length < 2 ^ (prefixWord ++ tailWord_259898).sum := by decide
  have hdescent : baseEnd_259898 < baseStart_259898 := by decide
  rcases family_descends (prefixWord ++ tailWord_259898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_259914 : List Nat := [3, 1, 2, 1, 1, 1, 4, 1, 3, 6]
def baseStart_259914 : Nat := 118140960795 + 259914 * 2 ^ 59
def prefixEnd_259914 : Nat := 4983230072969 + 3 ^ 40 * 259914 * 2
def baseEnd_259914 : Nat := 44486936944267106326561

theorem tailTrace_259914 : CollatzResearch.WordTrace tailWord_259914 prefixEnd_259914 44486936944267106326561 := by
  unfold tailWord_259914
  simp only [CollatzResearch.WordTrace]
  refine ⟨2369960595095860655564699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6319894920255628414839197 2369960595095860655564699)
  ·
    refine ⟨3554940892643790983347049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2369960595095860655564699 3554940892643790983347049)
    ·
      refine ⟨2666205669482843237510287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3554940892643790983347049 2666205669482843237510287)
      ·
        refine ⟨3999308504224264856265431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2666205669482843237510287 3999308504224264856265431)
        ·
          refine ⟨5998962756336397284398147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3999308504224264856265431 5998962756336397284398147)
          ·
            refine ⟨8998444134504595926597221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5998962756336397284398147 8998444134504595926597221)
            ·
              refine ⟨1687208275219611736236979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8998444134504595926597221 1687208275219611736236979)
              ·
                refine ⟨2530812412829417604355469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1687208275219611736236979 2530812412829417604355469)
                ·
                  refine ⟨949054654811031601633301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2530812412829417604355469 949054654811031601633301)
                  ·
                    refine ⟨44486936944267106326561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 949054654811031601633301 44486936944267106326561)
                    ·
                      rfl

theorem cell23_259914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 1, 3, 6].length) (baseStart_259914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_259914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_259914 prefixEnd_259914 := by exact prefixLift 259914
  have htrace : WordTrace (prefixWord ++ tailWord_259914) baseStart_259914 baseEnd_259914 := by
    simpa [prefixWord, tailWord_259914, baseEnd_259914] using wordTrace_append hprefix tailTrace_259914
  have hstable : (prefixWord ++ tailWord_259914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_259914).length < 2 ^ (prefixWord ++ tailWord_259914).sum := by decide
  have hdescent : baseEnd_259914 < baseStart_259914 := by decide
  rcases family_descends (prefixWord ++ tailWord_259914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_259932 : List Nat := [2, 2, 4, 2, 2, 2, 1, 1, 3, 1, 3]
def baseStart_259932 : Nat := 118140960795 + 259932 * 2 ^ 59
def prefixEnd_259932 : Nat := 4983230072969 + 3 ^ 40 * 259932 * 2
def baseEnd_259932 : Nat := 133470053484582248554601

theorem tailTrace_259932 : CollatzResearch.WordTrace tailWord_259932 prefixEnd_259932 133470053484582248554601 := by
  unfold tailWord_259932
  simp only [CollatzResearch.WordTrace]
  refine ⟨4740249447159115848207025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6320332596212154464276033 4740249447159115848207025)
  ·
    refine ⟨3555187085369336886155269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4740249447159115848207025 3555187085369336886155269)
    ·
      refine ⟨666597578506750666154113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3555187085369336886155269 666597578506750666154113)
      ·
        refine ⟨499948183880062999615585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 666597578506750666154113 499948183880062999615585)
        ·
          refine ⟨374961137910047249711689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 499948183880062999615585 374961137910047249711689)
          ·
            refine ⟨281220853432535437283767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 374961137910047249711689 281220853432535437283767)
            ·
              refine ⟨421831280148803155925651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 281220853432535437283767 421831280148803155925651)
              ·
                refine ⟨632746920223204733888477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 421831280148803155925651 632746920223204733888477)
                ·
                  refine ⟨237280095083701775208179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 632746920223204733888477 237280095083701775208179)
                  ·
                    refine ⟨355920142625552662812269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 237280095083701775208179 355920142625552662812269)
                    ·
                      refine ⟨133470053484582248554601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 355920142625552662812269 133470053484582248554601)
                      ·
                        rfl

theorem cell23_259932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 2, 1, 1, 3, 1, 3].length) (baseStart_259932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_259932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_259932 prefixEnd_259932 := by exact prefixLift 259932
  have htrace : WordTrace (prefixWord ++ tailWord_259932) baseStart_259932 baseEnd_259932 := by
    simpa [prefixWord, tailWord_259932, baseEnd_259932] using wordTrace_append hprefix tailTrace_259932
  have hstable : (prefixWord ++ tailWord_259932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_259932).length < 2 ^ (prefixWord ++ tailWord_259932).sum := by decide
  have hdescent : baseEnd_259932 < baseStart_259932 := by decide
  rcases family_descends (prefixWord ++ tailWord_259932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_259941 : List Nat := [1, 3, 1, 3, 1, 1, 1, 4, 3, 2, 3]
def baseStart_259941 : Nat := 118140960795 + 259941 * 2 ^ 59
def prefixEnd_259941 : Nat := 4983230072969 + 3 ^ 40 * 259941 * 2
def baseEnd_259941 : Nat := 133474674810472713342059

theorem tailTrace_259941 : CollatzResearch.WordTrace tailWord_259941 prefixEnd_259941 133474674810472713342059 := by
  unfold tailWord_259941
  simp only [CollatzResearch.WordTrace]
  refine ⟨9480827151285626233491677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6320551434190417488994451 9480827151285626233491677)
  ·
    refine ⟨3555310181732109837559379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9480827151285626233491677 3555310181732109837559379)
    ·
      refine ⟨5332965272598164756339069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3555310181732109837559379 5332965272598164756339069)
      ·
        refine ⟨1999861977224311783627151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5332965272598164756339069 1999861977224311783627151)
        ·
          refine ⟨2999792965836467675440727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1999861977224311783627151 2999792965836467675440727)
          ·
            refine ⟨4499689448754701513161091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2999792965836467675440727 4499689448754701513161091)
            ·
              refine ⟨6749534173132052269741637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4499689448754701513161091 6749534173132052269741637)
              ·
                refine ⟨1265537657462259800576557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6749534173132052269741637 1265537657462259800576557)
                ·
                  refine ⟨474576621548347425216209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1265537657462259800576557 474576621548347425216209)
                  ·
                    refine ⟨355932466161260568912157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 474576621548347425216209 355932466161260568912157)
                    ·
                      refine ⟨133474674810472713342059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 355932466161260568912157 133474674810472713342059)
                      ·
                        rfl

theorem cell23_259941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 4, 3, 2, 3].length) (baseStart_259941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_259941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_259941 prefixEnd_259941 := by exact prefixLift 259941
  have htrace : WordTrace (prefixWord ++ tailWord_259941) baseStart_259941 baseEnd_259941 := by
    simpa [prefixWord, tailWord_259941, baseEnd_259941] using wordTrace_append hprefix tailTrace_259941
  have hstable : (prefixWord ++ tailWord_259941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_259941).length < 2 ^ (prefixWord ++ tailWord_259941).sum := by decide
  have hdescent : baseEnd_259941 < baseStart_259941 := by decide
  rcases family_descends (prefixWord ++ tailWord_259941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_259948 : List Nat := [2, 2, 1, 1, 4, 3, 1, 3, 2, 4]
def baseStart_259948 : Nat := 118140960795 + 259948 * 2 ^ 59
def prefixEnd_259948 : Nat := 4983230072969 + 3 ^ 40 * 259948 * 2
def baseEnd_259948 : Nat := 44492756391684728651509

theorem tailTrace_259948 : CollatzResearch.WordTrace tailWord_259948 prefixEnd_259948 44492756391684728651509 := by
  unfold tailWord_259948
  simp only [CollatzResearch.WordTrace]
  refine ⟨4740541231130133214498249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6320721641506844285997665 4740541231130133214498249)
  ·
    refine ⟨3555405923347599910873687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4740541231130133214498249 3555405923347599910873687)
    ·
      refine ⟨5333108885021399866310531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3555405923347599910873687 5333108885021399866310531)
      ·
        refine ⟨7999663327532099799465797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5333108885021399866310531 7999663327532099799465797)
        ·
          refine ⟨1499936873912268712399837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7999663327532099799465797 1499936873912268712399837)
          ·
            refine ⟨562476327717100767149939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1499936873912268712399837 562476327717100767149939)
            ·
              refine ⟨843714491575651150724909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 562476327717100767149939 843714491575651150724909)
              ·
                refine ⟨316392934340869181521841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 843714491575651150724909 316392934340869181521841)
                ·
                  refine ⟨237294700755651886141381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 316392934340869181521841 237294700755651886141381)
                  ·
                    refine ⟨44492756391684728651509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 237294700755651886141381 44492756391684728651509)
                    ·
                      rfl

theorem cell23_259948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 4].length) (baseStart_259948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_259948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_259948 prefixEnd_259948 := by exact prefixLift 259948
  have htrace : WordTrace (prefixWord ++ tailWord_259948) baseStart_259948 baseEnd_259948 := by
    simpa [prefixWord, tailWord_259948, baseEnd_259948] using wordTrace_append hprefix tailTrace_259948
  have hstable : (prefixWord ++ tailWord_259948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_259948).length < 2 ^ (prefixWord ++ tailWord_259948).sum := by decide
  have hdescent : baseEnd_259948 < baseStart_259948 := by decide
  rcases family_descends (prefixWord ++ tailWord_259948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_259971 : List Nat := [1, 1, 1, 3, 4, 2, 1, 1, 3, 3, 3]
def baseStart_259971 : Nat := 118140960795 + 259971 * 2 ^ 59
def prefixEnd_259971 : Nat := 4983230072969 + 3 ^ 40 * 259971 * 2
def baseEnd_259971 : Nat := 133490079230107595966921

theorem tailTrace_259971 : CollatzResearch.WordTrace tailWord_259971 prefixEnd_259971 133490079230107595966921 := by
  unfold tailWord_259971
  simp only [CollatzResearch.WordTrace]
  refine ⟨9481921341176941357083767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6321280894117960904722511 9481921341176941357083767)
  ·
    refine ⟨14222882011765412035625651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9481921341176941357083767 14222882011765412035625651)
    ·
      refine ⟨21334323017648118053438477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14222882011765412035625651 21334323017648118053438477)
      ·
        refine ⟨8000371131618044270039429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21334323017648118053438477 8000371131618044270039429)
        ·
          refine ⟨1500069587178383300632393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8000371131618044270039429 1500069587178383300632393)
          ·
            refine ⟨1125052190383787475474295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1500069587178383300632393 1125052190383787475474295)
            ·
              refine ⟨1687578285575681213211443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1125052190383787475474295 1687578285575681213211443)
              ·
                refine ⟨2531367428363521819817165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1687578285575681213211443 2531367428363521819817165)
                ·
                  refine ⟨949262785636320682431437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2531367428363521819817165 949262785636320682431437)
                  ·
                    refine ⟨355973544613620255911789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 949262785636320682431437 355973544613620255911789)
                    ·
                      refine ⟨133490079230107595966921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 355973544613620255911789 133490079230107595966921)
                      ·
                        rfl

theorem cell23_259971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 1, 3, 3, 3].length) (baseStart_259971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_259971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_259971 prefixEnd_259971 := by exact prefixLift 259971
  have htrace : WordTrace (prefixWord ++ tailWord_259971) baseStart_259971 baseEnd_259971 := by
    simpa [prefixWord, tailWord_259971, baseEnd_259971] using wordTrace_append hprefix tailTrace_259971
  have hstable : (prefixWord ++ tailWord_259971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_259971).length < 2 ^ (prefixWord ++ tailWord_259971).sum := by decide
  have hdescent : baseEnd_259971 < baseStart_259971 := by decide
  rcases family_descends (prefixWord ++ tailWord_259971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_259975 : List Nat := [1, 1, 4, 2, 5, 1, 1, 1, 1, 1, 5]
def baseStart_259975 : Nat := 118140960795 + 259975 * 2 ^ 59
def prefixEnd_259975 : Nat := 4983230072969 + 3 ^ 40 * 259975 * 2
def baseEnd_259975 : Nat := 133492133152725580316903

theorem tailTrace_259975 : CollatzResearch.WordTrace tailWord_259975 prefixEnd_259975 133492133152725580316903 := by
  unfold tailWord_259975
  simp only [CollatzResearch.WordTrace]
  refine ⟨9482067233162450040229379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6321378155441633360152919 9482067233162450040229379)
  ·
    refine ⟨14223100849743675060344069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9482067233162450040229379 14223100849743675060344069)
    ·
      refine ⟨2666831409326939073814513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14223100849743675060344069 2666831409326939073814513)
      ·
        refine ⟨2000123556995204305360885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2666831409326939073814513 2000123556995204305360885)
        ·
          refine ⟨187511583468300403627583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2000123556995204305360885 187511583468300403627583)
          ·
            refine ⟨281267375202450605441375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187511583468300403627583 281267375202450605441375)
            ·
              refine ⟨421901062803675908162063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 281267375202450605441375 421901062803675908162063)
              ·
                refine ⟨632851594205513862243095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 421901062803675908162063 632851594205513862243095)
                ·
                  refine ⟨949277391308270793364643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 632851594205513862243095 949277391308270793364643)
                  ·
                    refine ⟨1423916086962406190046965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 949277391308270793364643 1423916086962406190046965)
                    ·
                      refine ⟨133492133152725580316903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1423916086962406190046965 133492133152725580316903)
                      ·
                        rfl

theorem cell23_259975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 1, 1, 1, 1, 1, 5].length) (baseStart_259975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_259975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_259975 prefixEnd_259975 := by exact prefixLift 259975
  have htrace : WordTrace (prefixWord ++ tailWord_259975) baseStart_259975 baseEnd_259975 := by
    simpa [prefixWord, tailWord_259975, baseEnd_259975] using wordTrace_append hprefix tailTrace_259975
  have hstable : (prefixWord ++ tailWord_259975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_259975).length < 2 ^ (prefixWord ++ tailWord_259975).sum := by decide
  have hdescent : baseEnd_259975 < baseStart_259975 := by decide
  rcases family_descends (prefixWord ++ tailWord_259975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_259982 : List Nat := [4, 1, 1, 5, 1, 1, 2, 2, 2, 4]
def baseStart_259982 : Nat := 118140960795 + 259982 * 2 ^ 59
def prefixEnd_259982 : Nat := 4983230072969 + 3 ^ 40 * 259982 * 2
def baseEnd_259982 : Nat := 44498575839102350976457

theorem tailTrace_259982 : CollatzResearch.WordTrace tailWord_259982 prefixEnd_259982 44498575839102350976457 := by
  unfold tailWord_259982
  simp only [CollatzResearch.WordTrace]
  refine ⟨1185290318017136279466775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6321548362758060157156133 1185290318017136279466775)
  ·
    refine ⟨1777935477025704419200163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1185290318017136279466775 1777935477025704419200163)
    ·
      refine ⟨2666903215538556628800245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1777935477025704419200163 2666903215538556628800245)
      ·
        refine ⟨250022176456739683950023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2666903215538556628800245 250022176456739683950023)
        ·
          refine ⟨375033264685109525925035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 250022176456739683950023 375033264685109525925035)
          ·
            refine ⟨562549897027664288887553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 375033264685109525925035 562549897027664288887553)
            ·
              refine ⟨421912422770748216665665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 562549897027664288887553 421912422770748216665665)
              ·
                refine ⟨316434317078061162499249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 421912422770748216665665 316434317078061162499249)
                ·
                  refine ⟨237325737808545871874437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 316434317078061162499249 237325737808545871874437)
                  ·
                    refine ⟨44498575839102350976457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 237325737808545871874437 44498575839102350976457)
                    ·
                      rfl

theorem cell23_259982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 2, 2, 2, 4].length) (baseStart_259982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_259982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_259982 prefixEnd_259982 := by exact prefixLift 259982
  have htrace : WordTrace (prefixWord ++ tailWord_259982) baseStart_259982 baseEnd_259982 := by
    simpa [prefixWord, tailWord_259982, baseEnd_259982] using wordTrace_append hprefix tailTrace_259982
  have hstable : (prefixWord ++ tailWord_259982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_259982).length < 2 ^ (prefixWord ++ tailWord_259982).sum := by decide
  have hdescent : baseEnd_259982 < baseStart_259982 := by decide
  rcases family_descends (prefixWord ++ tailWord_259982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_259984 : List Nat := [2, 1, 1, 1, 1, 1, 2, 3, 4, 2, 5]
def baseStart_259984 : Nat := 118140960795 + 259984 * 2 ^ 59
def prefixEnd_259984 : Nat := 4983230072969 + 3 ^ 40 * 259984 * 2
def baseEnd_259984 : Nat := 133496754478616045104361

theorem tailTrace_259984 : CollatzResearch.WordTrace tailWord_259984 prefixEnd_259984 133496754478616045104361 := by
  unfold tailWord_259984
  simp only [CollatzResearch.WordTrace]
  refine ⟨4741197745064922288653503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6321596993419896384871337 4741197745064922288653503)
  ·
    refine ⟨7111796617597383432980255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4741197745064922288653503 7111796617597383432980255)
    ·
      refine ⟨10667694926396075149470383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7111796617597383432980255 10667694926396075149470383)
      ·
        refine ⟨16001542389594112724205575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10667694926396075149470383 16001542389594112724205575)
        ·
          refine ⟨24002313584391169086308363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16001542389594112724205575 24002313584391169086308363)
          ·
            refine ⟨36003470376586753629462545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24002313584391169086308363 36003470376586753629462545)
            ·
              refine ⟨27002602782440065222096909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36003470376586753629462545 27002602782440065222096909)
              ·
                refine ⟨10125976043415024458286341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27002602782440065222096909 10125976043415024458286341)
                ·
                  refine ⟨1898620508140317085928689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10125976043415024458286341 1898620508140317085928689)
                  ·
                    refine ⟨1423965381105237814446517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1898620508140317085928689 1423965381105237814446517)
                    ·
                      refine ⟨133496754478616045104361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1423965381105237814446517 133496754478616045104361)
                      ·
                        rfl

theorem cell23_259984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 3, 4, 2, 5].length) (baseStart_259984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_259984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_259984 prefixEnd_259984 := by exact prefixLift 259984
  have htrace : WordTrace (prefixWord ++ tailWord_259984) baseStart_259984 baseEnd_259984 := by
    simpa [prefixWord, tailWord_259984, baseEnd_259984] using wordTrace_append hprefix tailTrace_259984
  have hstable : (prefixWord ++ tailWord_259984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_259984).length < 2 ^ (prefixWord ++ tailWord_259984).sum := by decide
  have hdescent : baseEnd_259984 < baseStart_259984 := by decide
  rcases family_descends (prefixWord ++ tailWord_259984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_260185 : List Nat := [1, 2, 1, 2, 2, 1, 5, 2, 3, 1, 3]
def baseStart_260185 : Nat := 118140960795 + 260185 * 2 ^ 59
def prefixEnd_260185 : Nat := 4983230072969 + 3 ^ 40 * 260185 * 2
def baseEnd_260185 : Nat := 133599964090169758690937

theorem tailTrace_260185 : CollatzResearch.WordTrace tailWord_260185 prefixEnd_260185 133599964090169758690937 := by
  unfold tailWord_260185
  simp only [CollatzResearch.WordTrace]
  refine ⟨9489726562401655905374009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6326484374934437270249339 9489726562401655905374009)
  ·
    refine ⟨7117294921801241929030507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9489726562401655905374009 7117294921801241929030507)
    ·
      refine ⟨10675942382701862893545761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7117294921801241929030507 10675942382701862893545761)
      ·
        refine ⟨8006956787026397170159321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10675942382701862893545761 8006956787026397170159321)
        ·
          refine ⟨6005217590269797877619491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8006956787026397170159321 6005217590269797877619491)
          ·
            refine ⟨9007826385404696816429237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6005217590269797877619491 9007826385404696816429237)
            ·
              refine ⟨844483723631690326540241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9007826385404696816429237 844483723631690326540241)
              ·
                refine ⟨633362792723767744905181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 844483723631690326540241 633362792723767744905181)
                ·
                  refine ⟨237511047271412904339443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 633362792723767744905181 237511047271412904339443)
                  ·
                    refine ⟨356266570907119356509165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 237511047271412904339443 356266570907119356509165)
                    ·
                      refine ⟨133599964090169758690937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 356266570907119356509165 133599964090169758690937)
                      ·
                        rfl

theorem cell23_260185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 5, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 5, 2, 3, 1, 3].length) (baseStart_260185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_260185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_260185 prefixEnd_260185 := by exact prefixLift 260185
  have htrace : WordTrace (prefixWord ++ tailWord_260185) baseStart_260185 baseEnd_260185 := by
    simpa [prefixWord, tailWord_260185, baseEnd_260185] using wordTrace_append hprefix tailTrace_260185
  have hstable : (prefixWord ++ tailWord_260185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_260185).length < 2 ^ (prefixWord ++ tailWord_260185).sum := by decide
  have hdescent : baseEnd_260185 < baseStart_260185 := by decide
  rcases family_descends (prefixWord ++ tailWord_260185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_260189 : List Nat := [1, 4, 4, 1, 1, 3, 1, 1, 2, 2, 3]
def baseStart_260189 : Nat := 118140960795 + 260189 * 2 ^ 59
def prefixEnd_260189 : Nat := 4983230072969 + 3 ^ 40 * 260189 * 2
def baseEnd_260189 : Nat := 133602018012787743040919

theorem tailTrace_260189 : CollatzResearch.WordTrace tailWord_260189 prefixEnd_260189 133602018012787743040919 := by
  unfold tailWord_260189
  simp only [CollatzResearch.WordTrace]
  refine ⟨9489872454387164588519621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6326581636258109725679747 9489872454387164588519621)
  ·
    refine ⟨1779351085197593360347429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9489872454387164588519621 1779351085197593360347429)
    ·
      refine ⟨333628328474548755065143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1779351085197593360347429 333628328474548755065143)
      ·
        refine ⟨500442492711823132597715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 333628328474548755065143 500442492711823132597715)
        ·
          refine ⟨750663739067734698896573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 500442492711823132597715 750663739067734698896573)
          ·
            refine ⟨281498902150400512086215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 750663739067734698896573 281498902150400512086215)
            ·
              refine ⟨422248353225600768129323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 281498902150400512086215 422248353225600768129323)
              ·
                refine ⟨633372529838401152193985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 422248353225600768129323 633372529838401152193985)
                ·
                  refine ⟨475029397378800864145489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 633372529838401152193985 475029397378800864145489)
                  ·
                    refine ⟨356272048034100648109117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 475029397378800864145489 356272048034100648109117)
                    ·
                      refine ⟨133602018012787743040919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 356272048034100648109117 133602018012787743040919)
                      ·
                        rfl

theorem cell23_260189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 3, 1, 1, 2, 2, 3].length) (baseStart_260189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_260189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_260189 prefixEnd_260189 := by exact prefixLift 260189
  have htrace : WordTrace (prefixWord ++ tailWord_260189) baseStart_260189 baseEnd_260189 := by
    simpa [prefixWord, tailWord_260189, baseEnd_260189] using wordTrace_append hprefix tailTrace_260189
  have hstable : (prefixWord ++ tailWord_260189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_260189).length < 2 ^ (prefixWord ++ tailWord_260189).sum := by decide
  have hdescent : baseEnd_260189 < baseStart_260189 := by decide
  rcases family_descends (prefixWord ++ tailWord_260189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_260205 : List Nat := [1, 5, 1, 1, 2, 1, 3, 3, 1, 5]
def baseStart_260205 : Nat := 118140960795 + 260205 * 2 ^ 59
def prefixEnd_260205 : Nat := 4983230072969 + 3 ^ 40 * 260205 * 2
def baseEnd_260205 : Nat := 44536744567753226813615

theorem tailTrace_260205 : CollatzResearch.WordTrace tailWord_260205 prefixEnd_260205 44536744567753226813615 := by
  unfold tailWord_260205
  simp only [CollatzResearch.WordTrace]
  refine ⟨9490456022329199321102069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6326970681552799547401379 9490456022329199321102069)
  ·
    refine ⟨889730252093362436353319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9490456022329199321102069 889730252093362436353319)
    ·
      refine ⟨1334595378140043654529979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 889730252093362436353319 1334595378140043654529979)
      ·
        refine ⟨2001893067210065481794969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1334595378140043654529979 2001893067210065481794969)
        ·
          refine ⟨1501419800407549111346227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2001893067210065481794969 1501419800407549111346227)
          ·
            refine ⟨2252129700611323667019341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1501419800407549111346227 2252129700611323667019341)
            ·
              refine ⟨844548637729246375132253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2252129700611323667019341 844548637729246375132253)
              ·
                refine ⟨316705739148467390674595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 844548637729246375132253 316705739148467390674595)
                ·
                  refine ⟨475058608722701086011893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 316705739148467390674595 475058608722701086011893)
                  ·
                    refine ⟨44536744567753226813615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 475058608722701086011893 44536744567753226813615)
                    ·
                      rfl

theorem cell23_260205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 3, 3, 1, 5].length) (baseStart_260205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_260205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_260205 prefixEnd_260205 := by exact prefixLift 260205
  have htrace : WordTrace (prefixWord ++ tailWord_260205) baseStart_260205 baseEnd_260205 := by
    simpa [prefixWord, tailWord_260205, baseEnd_260205] using wordTrace_append hprefix tailTrace_260205
  have hstable : (prefixWord ++ tailWord_260205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_260205).length < 2 ^ (prefixWord ++ tailWord_260205).sum := by decide
  have hdescent : baseEnd_260205 < baseStart_260205 := by decide
  rcases family_descends (prefixWord ++ tailWord_260205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_260242 : List Nat := [3, 2, 3, 1, 1, 1, 4, 2, 1, 1, 4]
def baseStart_260242 : Nat := 118140960795 + 260242 * 2 ^ 59
def prefixEnd_260242 : Nat := 4983230072969 + 3 ^ 40 * 260242 * 2
def baseEnd_260242 : Nat := 133629232487476035678175

theorem tailTrace_260242 : CollatzResearch.WordTrace tailWord_260242 prefixEnd_260242 133629232487476035678175 := by
  unfold tailWord_260242
  simp only [CollatzResearch.WordTrace]
  refine ⟨2372951380798788660049745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6327870348796769760132653 2372951380798788660049745)
  ·
    refine ⟨1779713535599091495037309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2372951380798788660049745 1779713535599091495037309)
    ·
      refine ⟨667392575849659310638991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1779713535599091495037309 667392575849659310638991)
      ·
        refine ⟨1001088863774488965958487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 667392575849659310638991 1001088863774488965958487)
        ·
          refine ⟨1501633295661733448937731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1001088863774488965958487 1501633295661733448937731)
          ·
            refine ⟨2252449943492600173406597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1501633295661733448937731 2252449943492600173406597)
            ·
              refine ⟨422334364404862532513737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2252449943492600173406597 422334364404862532513737)
              ·
                refine ⟨316750773303646899385303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 422334364404862532513737 316750773303646899385303)
                ·
                  refine ⟨475126159955470349077955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 316750773303646899385303 475126159955470349077955)
                  ·
                    refine ⟨712689239933205523616933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 475126159955470349077955 712689239933205523616933)
                    ·
                      refine ⟨133629232487476035678175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 712689239933205523616933 133629232487476035678175)
                      ·
                        rfl

theorem cell23_260242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 4, 2, 1, 1, 4].length) (baseStart_260242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_260242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_260242 prefixEnd_260242 := by exact prefixLift 260242
  have htrace : WordTrace (prefixWord ++ tailWord_260242) baseStart_260242 baseEnd_260242 := by
    simpa [prefixWord, tailWord_260242, baseEnd_260242] using wordTrace_append hprefix tailTrace_260242
  have hstable : (prefixWord ++ tailWord_260242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_260242).length < 2 ^ (prefixWord ++ tailWord_260242).sum := by decide
  have hdescent : baseEnd_260242 < baseStart_260242 := by decide
  rcases family_descends (prefixWord ++ tailWord_260242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_260270 : List Nat := [4, 1, 4, 2, 1, 1, 3, 2, 1, 1, 3]
def baseStart_260270 : Nat := 118140960795 + 260270 * 2 ^ 59
def prefixEnd_260270 : Nat := 4983230072969 + 3 ^ 40 * 260270 * 2
def baseEnd_260270 : Nat := 133643609945801926128047

theorem tailTrace_260270 : CollatzResearch.WordTrace tailWord_260270 prefixEnd_260270 133643609945801926128047 := by
  unfold tailWord_260270
  simp only [CollatzResearch.WordTrace]
  refine ⟨1186603345886714427777283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6328551178062476948145509 1186603345886714427777283)
  ·
    refine ⟨1779905018830071641665925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1186603345886714427777283 1779905018830071641665925)
    ·
      refine ⟨333732191030638432812361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1779905018830071641665925 333732191030638432812361)
      ·
        refine ⟨250299143272978824609271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 333732191030638432812361 250299143272978824609271)
        ·
          refine ⟨375448714909468236913907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 250299143272978824609271 375448714909468236913907)
          ·
            refine ⟨563173072364202355370861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 375448714909468236913907 563173072364202355370861)
            ·
              refine ⟨211189902136575883264073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 563173072364202355370861 211189902136575883264073)
              ·
                refine ⟨158392426602431912448055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 211189902136575883264073 158392426602431912448055)
                ·
                  refine ⟨237588639903647868672083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 158392426602431912448055 237588639903647868672083)
                  ·
                    refine ⟨356382959855471803008125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 237588639903647868672083 356382959855471803008125)
                    ·
                      refine ⟨133643609945801926128047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 356382959855471803008125 133643609945801926128047)
                      ·
                        rfl

theorem cell23_260270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 3, 2, 1, 1, 3].length) (baseStart_260270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_260270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_260270 prefixEnd_260270 := by exact prefixLift 260270
  have htrace : WordTrace (prefixWord ++ tailWord_260270) baseStart_260270 baseEnd_260270 := by
    simpa [prefixWord, tailWord_260270, baseEnd_260270] using wordTrace_append hprefix tailTrace_260270
  have hstable : (prefixWord ++ tailWord_260270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_260270).length < 2 ^ (prefixWord ++ tailWord_260270).sum := by decide
  have hdescent : baseEnd_260270 < baseStart_260270 := by decide
  rcases family_descends (prefixWord ++ tailWord_260270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_260285 : List Nat := [1, 4, 1, 2, 1, 1, 1, 1, 2, 7, 2]
def baseStart_260285 : Nat := 118140960795 + 260285 * 2 ^ 59
def prefixEnd_260285 : Nat := 4983230072969 + 3 ^ 40 * 260285 * 2
def baseEnd_260285 : Nat := 133651312155619367440477

theorem tailTrace_260285 : CollatzResearch.WordTrace tailWord_260285 prefixEnd_260285 133651312155619367440477 := by
  unfold tailWord_260285
  simp only [CollatzResearch.WordTrace]
  refine ⟨9493373862039372984014309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6328915908026248656009539 9493373862039372984014309)
  ·
    refine ⟨1780007599132382434502683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9493373862039372984014309 1780007599132382434502683)
    ·
      refine ⟨2670011398698573651754025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1780007599132382434502683 2670011398698573651754025)
      ·
        refine ⟨2002508549023930238815519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2670011398698573651754025 2002508549023930238815519)
        ·
          refine ⟨3003762823535895358223279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2002508549023930238815519 3003762823535895358223279)
          ·
            refine ⟨4505644235303843037334919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3003762823535895358223279 4505644235303843037334919)
            ·
              refine ⟨6758466352955764556002379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4505644235303843037334919 6758466352955764556002379)
              ·
                refine ⟨10137699529433646834003569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6758466352955764556002379 10137699529433646834003569)
                ·
                  refine ⟨7603274647075235125502677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10137699529433646834003569 7603274647075235125502677)
                  ·
                    refine ⟨178201749540825823253969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 7603274647075235125502677 178201749540825823253969)
                    ·
                      refine ⟨133651312155619367440477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 178201749540825823253969 133651312155619367440477)
                      ·
                        rfl

theorem cell23_260285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 1, 2, 7, 2].length) (baseStart_260285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_260285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_260285 prefixEnd_260285 := by exact prefixLift 260285
  have htrace : WordTrace (prefixWord ++ tailWord_260285) baseStart_260285 baseEnd_260285 := by
    simpa [prefixWord, tailWord_260285, baseEnd_260285] using wordTrace_append hprefix tailTrace_260285
  have hstable : (prefixWord ++ tailWord_260285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_260285).length < 2 ^ (prefixWord ++ tailWord_260285).sum := by decide
  have hdescent : baseEnd_260285 < baseStart_260285 := by decide
  rcases family_descends (prefixWord ++ tailWord_260285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_260286 : List Nat := [4, 2, 1, 1, 4, 2, 2, 1, 2, 4]
def baseStart_260286 : Nat := 118140960795 + 260286 * 2 ^ 59
def prefixEnd_260286 : Nat := 4983230072969 + 3 ^ 40 * 260286 * 2
def baseEnd_260286 : Nat := 44550608545424621175991

theorem tailTrace_260286 : CollatzResearch.WordTrace tailWord_260286 prefixEnd_260286 44550608545424621175991 := by
  unfold tailWord_260286
  simp only [CollatzResearch.WordTrace]
  refine ⟨1186676291879468769350089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6328940223357166769867141 1186676291879468769350089)
  ·
    refine ⟨890007218909601577012567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1186676291879468769350089 890007218909601577012567)
    ·
      refine ⟨1335010828364402365518851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 890007218909601577012567 1335010828364402365518851)
      ·
        refine ⟨2002516242546603548278277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1335010828364402365518851 2002516242546603548278277)
        ·
          refine ⟨375471795477488165302177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2002516242546603548278277 375471795477488165302177)
          ·
            refine ⟨281603846608116123976633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 375471795477488165302177 281603846608116123976633)
            ·
              refine ⟨211202884956087092982475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 281603846608116123976633 211202884956087092982475)
              ·
                refine ⟨316804327434130639473713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 211202884956087092982475 316804327434130639473713)
                ·
                  refine ⟨237603245575597979605285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 316804327434130639473713 237603245575597979605285)
                  ·
                    refine ⟨44550608545424621175991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 237603245575597979605285 44550608545424621175991)
                    ·
                      rfl

theorem cell23_260286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 2, 2, 1, 2, 4].length) (baseStart_260286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_260286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_260286 prefixEnd_260286 := by exact prefixLift 260286
  have htrace : WordTrace (prefixWord ++ tailWord_260286) baseStart_260286 baseEnd_260286 := by
    simpa [prefixWord, tailWord_260286, baseEnd_260286] using wordTrace_append hprefix tailTrace_260286
  have hstable : (prefixWord ++ tailWord_260286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_260286).length < 2 ^ (prefixWord ++ tailWord_260286).sum := by decide
  have hdescent : baseEnd_260286 < baseStart_260286 := by decide
  rcases family_descends (prefixWord ++ tailWord_260286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_260315 : List Nat := [1, 1, 1, 1, 1, 1, 1, 7, 3, 4, 2]
def baseStart_260315 : Nat := 118140960795 + 260315 * 2 ^ 59
def prefixEnd_260315 : Nat := 4983230072969 + 3 ^ 40 * 260315 * 2
def baseEnd_260315 : Nat := 133666716575254250065339

theorem tailTrace_260315 : CollatzResearch.WordTrace tailWord_260315 prefixEnd_260315 133666716575254250065339 := by
  unfold tailWord_260315
  simp only [CollatzResearch.WordTrace]
  refine ⟨9494468051930688107606399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6329645367953792071737599 9494468051930688107606399)
  ·
    refine ⟨14241702077896032161409599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9494468051930688107606399 14241702077896032161409599)
    ·
      refine ⟨21362553116844048242114399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14241702077896032161409599 21362553116844048242114399)
      ·
        refine ⟨32043829675266072363171599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21362553116844048242114399 32043829675266072363171599)
        ·
          refine ⟨48065744512899108544757399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32043829675266072363171599 48065744512899108544757399)
          ·
            refine ⟨72098616769348662817136099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48065744512899108544757399 72098616769348662817136099)
            ·
              refine ⟨108147925154022994225704149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72098616769348662817136099 108147925154022994225704149)
              ·
                refine ⟨2534716995797413927164941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 108147925154022994225704149 2534716995797413927164941)
                ·
                  refine ⟨950518873424030222686853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2534716995797413927164941 950518873424030222686853)
                  ·
                    refine ⟨178222288767005666753785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 950518873424030222686853 178222288767005666753785)
                    ·
                      refine ⟨133666716575254250065339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 178222288767005666753785 133666716575254250065339)
                      ·
                        rfl

theorem cell23_260315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 7, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 7, 3, 4, 2].length) (baseStart_260315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_260315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_260315 prefixEnd_260315 := by exact prefixLift 260315
  have htrace : WordTrace (prefixWord ++ tailWord_260315) baseStart_260315 baseEnd_260315 := by
    simpa [prefixWord, tailWord_260315, baseEnd_260315] using wordTrace_append hprefix tailTrace_260315
  have hstable : (prefixWord ++ tailWord_260315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_260315).length < 2 ^ (prefixWord ++ tailWord_260315).sum := by decide
  have hdescent : baseEnd_260315 < baseStart_260315 := by decide
  rcases family_descends (prefixWord ++ tailWord_260315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_260335 : List Nat := [1, 1, 2, 1, 6, 1, 1, 1, 2, 4, 3]
def baseStart_260335 : Nat := 118140960795 + 260335 * 2 ^ 59
def prefixEnd_260335 : Nat := 4983230072969 + 3 ^ 40 * 260335 * 2
def baseEnd_260335 : Nat := 133676986188344171815247

theorem tailTrace_260335 : CollatzResearch.WordTrace tailWord_260335 prefixEnd_260335 133676986188344171815247 := by
  unfold tailWord_260335
  simp only [CollatzResearch.WordTrace]
  refine ⟨9495197511858231523334459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6330131674572154348889639 9495197511858231523334459)
  ·
    refine ⟨14242796267787347285001689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9495197511858231523334459 14242796267787347285001689)
    ·
      refine ⟨10682097200840510463751267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14242796267787347285001689 10682097200840510463751267)
      ·
        refine ⟨16023145801260765695626901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10682097200840510463751267 16023145801260765695626901)
        ·
          refine ⟨751084959434098391982511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 16023145801260765695626901 751084959434098391982511)
          ·
            refine ⟨1126627439151147587973767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 751084959434098391982511 1126627439151147587973767)
            ·
              refine ⟨1689941158726721381960651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1126627439151147587973767 1689941158726721381960651)
              ·
                refine ⟨2534911738090082072940977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1689941158726721381960651 2534911738090082072940977)
                ·
                  refine ⟨1901183803567561554705733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2534911738090082072940977 1901183803567561554705733)
                  ·
                    refine ⟨356471963168917791507325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1901183803567561554705733 356471963168917791507325)
                    ·
                      refine ⟨133676986188344171815247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 356471963168917791507325 133676986188344171815247)
                      ·
                        rfl

theorem cell23_260335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 1, 2, 4, 3].length) (baseStart_260335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_260335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_260335 prefixEnd_260335 := by exact prefixLift 260335
  have htrace : WordTrace (prefixWord ++ tailWord_260335) baseStart_260335 baseEnd_260335 := by
    simpa [prefixWord, tailWord_260335, baseEnd_260335] using wordTrace_append hprefix tailTrace_260335
  have hstable : (prefixWord ++ tailWord_260335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_260335).length < 2 ^ (prefixWord ++ tailWord_260335).sum := by decide
  have hdescent : baseEnd_260335 < baseStart_260335 := by decide
  rcases family_descends (prefixWord ++ tailWord_260335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_260385 : List Nat := [1, 2, 3, 2, 1, 1, 2, 4, 2, 5]
def baseStart_260385 : Nat := 118140960795 + 260385 * 2 ^ 59
def prefixEnd_260385 : Nat := 4983230072969 + 3 ^ 40 * 260385 * 2
def baseEnd_260385 : Nat := 44567553407022992063339

theorem tailTrace_260385 : CollatzResearch.WordTrace tailWord_260385 prefixEnd_260385 44567553407022992063339 := by
  unfold tailWord_260385
  simp only [CollatzResearch.WordTrace]
  refine ⟨9497021161677090062654609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6331347441118060041769739 9497021161677090062654609)
  ·
    refine ⟨7122765871257817546990957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9497021161677090062654609 7122765871257817546990957)
    ·
      refine ⟨2671037201721681580121609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7122765871257817546990957 2671037201721681580121609)
      ·
        refine ⟨2003277901291261185091207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2671037201721681580121609 2003277901291261185091207)
        ·
          refine ⟨3004916851936891777636811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2003277901291261185091207 3004916851936891777636811)
          ·
            refine ⟨4507375277905337666455217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3004916851936891777636811 4507375277905337666455217)
            ·
              refine ⟨3380531458429003249841413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4507375277905337666455217 3380531458429003249841413)
              ·
                refine ⟨633849648455438109345265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3380531458429003249841413 633849648455438109345265)
                ·
                  refine ⟨475387236341578582008949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 633849648455438109345265 475387236341578582008949)
                  ·
                    refine ⟨44567553407022992063339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 475387236341578582008949 44567553407022992063339)
                    ·
                      rfl

theorem cell23_260385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 4, 2, 5].length) (baseStart_260385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_260385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_260385 prefixEnd_260385 := by exact prefixLift 260385
  have htrace : WordTrace (prefixWord ++ tailWord_260385) baseStart_260385 baseEnd_260385 := by
    simpa [prefixWord, tailWord_260385, baseEnd_260385] using wordTrace_append hprefix tailTrace_260385
  have hstable : (prefixWord ++ tailWord_260385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_260385).length < 2 ^ (prefixWord ++ tailWord_260385).sum := by decide
  have hdescent : baseEnd_260385 < baseStart_260385 := by decide
  rcases family_descends (prefixWord ++ tailWord_260385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_260405 : List Nat := [1, 3, 3, 1, 2, 1, 1, 1, 3, 3, 4]
def baseStart_260405 : Nat := 118140960795 + 260405 * 2 ^ 59
def prefixEnd_260405 : Nat := 4983230072969 + 3 ^ 40 * 260405 * 2
def baseEnd_260405 : Nat := 133712929834158897939925

theorem tailTrace_260405 : CollatzResearch.WordTrace tailWord_260405 prefixEnd_260405 133712929834158897939925 := by
  unfold tailWord_260405
  simp only [CollatzResearch.WordTrace]
  refine ⟨9497750621604633478382669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6331833747736422318921779 9497750621604633478382669)
  ·
    refine ⟨3561656483101737554393501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9497750621604633478382669 3561656483101737554393501)
    ·
      refine ⟨1335621181163151582897563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3561656483101737554393501 1335621181163151582897563)
      ·
        refine ⟨2003431771744727374346345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1335621181163151582897563 2003431771744727374346345)
        ·
          refine ⟨1502573828808545530759759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2003431771744727374346345 1502573828808545530759759)
          ·
            refine ⟨2253860743212818296139639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1502573828808545530759759 2253860743212818296139639)
            ·
              refine ⟨3380791114819227444209459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2253860743212818296139639 3380791114819227444209459)
              ·
                refine ⟨5071186672228841166314189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3380791114819227444209459 5071186672228841166314189)
                ·
                  refine ⟨1901695002085815437367821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5071186672228841166314189 1901695002085815437367821)
                  ·
                    refine ⟨713135625782180789012933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1901695002085815437367821 713135625782180789012933)
                    ·
                      refine ⟨133712929834158897939925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 713135625782180789012933 133712929834158897939925)
                      ·
                        rfl

theorem cell23_260405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 1, 3, 3, 4].length) (baseStart_260405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_260405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_260405 prefixEnd_260405 := by exact prefixLift 260405
  have htrace : WordTrace (prefixWord ++ tailWord_260405) baseStart_260405 baseEnd_260405 := by
    simpa [prefixWord, tailWord_260405, baseEnd_260405] using wordTrace_append hprefix tailTrace_260405
  have hstable : (prefixWord ++ tailWord_260405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_260405).length < 2 ^ (prefixWord ++ tailWord_260405).sum := by decide
  have hdescent : baseEnd_260405 < baseStart_260405 := by decide
  rcases family_descends (prefixWord ++ tailWord_260405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_260500 : List Nat := [2, 4, 2, 1, 3, 2, 2, 2, 1, 4]
def baseStart_260500 : Nat := 118140960795 + 260500 * 2 ^ 59
def prefixEnd_260500 : Nat := 4983230072969 + 3 ^ 40 * 260500 * 2
def baseEnd_260500 : Nat := 44587236832112008750663

theorem tailTrace_260500 : CollatzResearch.WordTrace tailWord_260500 prefixEnd_260500 44587236832112008750663 := by
  unfold tailWord_260500
  simp only [CollatzResearch.WordTrace]
  refine ⟨4750607778130232351545477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6334143704173643135393969 4750607778130232351545477)
  ·
    refine ⟨890738958399418565914777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4750607778130232351545477 890738958399418565914777)
    ·
      refine ⟨668054218799563924436083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 890738958399418565914777 668054218799563924436083)
      ·
        refine ⟨1002081328199345886654125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 668054218799563924436083 1002081328199345886654125)
        ·
          refine ⟨375780498074754707495297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1002081328199345886654125 375780498074754707495297)
          ·
            refine ⟨281835373556066030621473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 375780498074754707495297 281835373556066030621473)
            ·
              refine ⟨211376530167049522966105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 281835373556066030621473 211376530167049522966105)
              ·
                refine ⟨158532397625287142224579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 211376530167049522966105 158532397625287142224579)
                ·
                  refine ⟨237798596437930713336869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 158532397625287142224579 237798596437930713336869)
                  ·
                    refine ⟨44587236832112008750663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 237798596437930713336869 44587236832112008750663)
                    ·
                      rfl

theorem cell23_260500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 2, 2, 2, 1, 4].length) (baseStart_260500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_260500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_260500 prefixEnd_260500 := by exact prefixLift 260500
  have htrace : WordTrace (prefixWord ++ tailWord_260500) baseStart_260500 baseEnd_260500 := by
    simpa [prefixWord, tailWord_260500, baseEnd_260500] using wordTrace_append hprefix tailTrace_260500
  have hstable : (prefixWord ++ tailWord_260500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_260500).length < 2 ^ (prefixWord ++ tailWord_260500).sum := by decide
  have hdescent : baseEnd_260500 < baseStart_260500 := by decide
  rcases family_descends (prefixWord ++ tailWord_260500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_260505 : List Nat := [1, 2, 1, 2, 1, 4, 1, 2, 3, 6]
def baseStart_260505 : Nat := 118140960795 + 260505 * 2 ^ 59
def prefixEnd_260505 : Nat := 4983230072969 + 3 ^ 40 * 260505 * 2
def baseEnd_260505 : Nat := 44588092633202835563155

theorem tailTrace_260505 : CollatzResearch.WordTrace tailWord_260505 prefixEnd_260505 44588092633202835563155 := by
  unfold tailWord_260505
  simp only [CollatzResearch.WordTrace]
  refine ⟨9501397921242350557022969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6334265280828233704681979 9501397921242350557022969)
  ·
    refine ⟨7126048440931762917767227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9501397921242350557022969 7126048440931762917767227)
    ·
      refine ⟨10689072661397644376650841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7126048440931762917767227 10689072661397644376650841)
      ·
        refine ⟨8016804496048233282488131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10689072661397644376650841 8016804496048233282488131)
        ·
          refine ⟨12025206744072349923732197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8016804496048233282488131 12025206744072349923732197)
          ·
            refine ⟨2254726264513565610699787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12025206744072349923732197 2254726264513565610699787)
            ·
              refine ⟨3382089396770348416049681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2254726264513565610699787 3382089396770348416049681)
              ·
                refine ⟨2536567047577761312037261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3382089396770348416049681 2536567047577761312037261)
                ·
                  refine ⟨951212642841660492013973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2536567047577761312037261 951212642841660492013973)
                  ·
                    refine ⟨44588092633202835563155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 951212642841660492013973 44588092633202835563155)
                    ·
                      rfl

theorem cell23_260505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 2, 3, 6].length) (baseStart_260505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_260505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_260505 prefixEnd_260505 := by exact prefixLift 260505
  have htrace : WordTrace (prefixWord ++ tailWord_260505) baseStart_260505 baseEnd_260505 := by
    simpa [prefixWord, tailWord_260505, baseEnd_260505] using wordTrace_append hprefix tailTrace_260505
  have hstable : (prefixWord ++ tailWord_260505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_260505).length < 2 ^ (prefixWord ++ tailWord_260505).sum := by decide
  have hdescent : baseEnd_260505 < baseStart_260505 := by decide
  rcases family_descends (prefixWord ++ tailWord_260505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_260512 : List Nat := [2, 1, 1, 4, 1, 3, 1, 2, 3, 1, 4]
def baseStart_260512 : Nat := 118140960795 + 260512 * 2 ^ 59
def prefixEnd_260512 : Nat := 4983230072969 + 3 ^ 40 * 260512 * 2
def baseEnd_260512 : Nat := 133767872264189979301933

theorem tailTrace_260512 : CollatzResearch.WordTrace tailWord_260512 prefixEnd_260512 133767872264189979301933 := by
  unfold tailWord_260512
  simp only [CollatzResearch.WordTrace]
  refine ⟨4750826616108495376263895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6334435488144660501685193 4750826616108495376263895)
  ·
    refine ⟨7126239924162743064395843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4750826616108495376263895 7126239924162743064395843)
    ·
      refine ⟨10689359886244114596593765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7126239924162743064395843 10689359886244114596593765)
      ·
        refine ⟨2004254978670771486861331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10689359886244114596593765 2004254978670771486861331)
        ·
          refine ⟨3006382468006157230291997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2004254978670771486861331 3006382468006157230291997)
          ·
            refine ⟨1127393425502308961359499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3006382468006157230291997 1127393425502308961359499)
            ·
              refine ⟨1691090138253463442039249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1127393425502308961359499 1691090138253463442039249)
              ·
                refine ⟨1268317603690097581529437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1691090138253463442039249 1268317603690097581529437)
                ·
                  refine ⟨475619101383786593073539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1268317603690097581529437 475619101383786593073539)
                  ·
                    refine ⟨713428652075679889610309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 475619101383786593073539 713428652075679889610309)
                    ·
                      refine ⟨133767872264189979301933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 713428652075679889610309 133767872264189979301933)
                      ·
                        rfl

theorem cell23_260512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 2, 3, 1, 4].length) (baseStart_260512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_260512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_260512 prefixEnd_260512 := by exact prefixLift 260512
  have htrace : WordTrace (prefixWord ++ tailWord_260512) baseStart_260512 baseEnd_260512 := by
    simpa [prefixWord, tailWord_260512, baseEnd_260512] using wordTrace_append hprefix tailTrace_260512
  have hstable : (prefixWord ++ tailWord_260512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_260512).length < 2 ^ (prefixWord ++ tailWord_260512).sum := by decide
  have hdescent : baseEnd_260512 < baseStart_260512 := by decide
  rcases family_descends (prefixWord ++ tailWord_260512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_260533 : List Nat := [1, 3, 3, 2, 3, 2, 1, 1, 2, 3, 2]
def baseStart_260533 : Nat := 118140960795 + 260533 * 2 ^ 59
def prefixEnd_260533 : Nat := 4983230072969 + 3 ^ 40 * 260533 * 2
def baseEnd_260533 : Nat := 133778655357934397139337

theorem tailTrace_260533 : CollatzResearch.WordTrace tailWord_260533 prefixEnd_260533 133778655357934397139337 := by
  unfold tailWord_260533
  simp only [CollatzResearch.WordTrace]
  refine ⟨9502419165140911339042253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6334946110093940892694835 9502419165140911339042253)
  ·
    refine ⟨3563407186927841752140845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9502419165140911339042253 3563407186927841752140845)
    ·
      refine ⟨1336277695097940657052817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3563407186927841752140845 1336277695097940657052817)
      ·
        refine ⟨1002208271323455492789613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1336277695097940657052817 1002208271323455492789613)
        ·
          refine ⟨375828101746295809796105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1002208271323455492789613 375828101746295809796105)
          ·
            refine ⟨281871076309721857347079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 375828101746295809796105 281871076309721857347079)
            ·
              refine ⟨422806614464582786020619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 281871076309721857347079 422806614464582786020619)
              ·
                refine ⟨634209921696874179030929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 422806614464582786020619 634209921696874179030929)
                ·
                  refine ⟨475657441272655634273197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 634209921696874179030929 475657441272655634273197)
                  ·
                    refine ⟨178371540477245862852449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 475657441272655634273197 178371540477245862852449)
                    ·
                      refine ⟨133778655357934397139337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 178371540477245862852449 133778655357934397139337)
                      ·
                        rfl

theorem cell23_260533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 2, 1, 1, 2, 3, 2].length) (baseStart_260533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_260533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_260533 prefixEnd_260533 := by exact prefixLift 260533
  have htrace : WordTrace (prefixWord ++ tailWord_260533) baseStart_260533 baseEnd_260533 := by
    simpa [prefixWord, tailWord_260533, baseEnd_260533] using wordTrace_append hprefix tailTrace_260533
  have hstable : (prefixWord ++ tailWord_260533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_260533).length < 2 ^ (prefixWord ++ tailWord_260533).sum := by decide
  have hdescent : baseEnd_260533 < baseStart_260533 := by decide
  rcases family_descends (prefixWord ++ tailWord_260533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_260555 : List Nat := [1, 1, 1, 1, 3, 3, 1, 2, 2, 2, 6]
def baseStart_260555 : Nat := 118140960795 + 260555 * 2 ^ 59
def prefixEnd_260555 : Nat := 4983230072969 + 3 ^ 40 * 260555 * 2
def baseEnd_260555 : Nat := 133789951932333311064235

theorem tailTrace_260555 : CollatzResearch.WordTrace tailWord_260555 prefixEnd_260555 133789951932333311064235 := by
  unfold tailWord_260555
  simp only [CollatzResearch.WordTrace]
  refine ⟨9503221571061209096343119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6335481047374139397562079 9503221571061209096343119)
  ·
    refine ⟨14254832356591813644514679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9503221571061209096343119 14254832356591813644514679)
    ·
      refine ⟨21382248534887720466772019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14254832356591813644514679 21382248534887720466772019)
      ·
        refine ⟨32073372802331580700158029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21382248534887720466772019 32073372802331580700158029)
        ·
          refine ⟨12027514800874342762559261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32073372802331580700158029 12027514800874342762559261)
          ·
            refine ⟨4510318050327878535959723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12027514800874342762559261 4510318050327878535959723)
            ·
              refine ⟨6765477075491817803939585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4510318050327878535959723 6765477075491817803939585)
              ·
                refine ⟨5074107806618863352954689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6765477075491817803939585 5074107806618863352954689)
                ·
                  refine ⟨3805580854964147514716017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5074107806618863352954689 3805580854964147514716017)
                  ·
                    refine ⟨2854185641223110636037013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3805580854964147514716017 2854185641223110636037013)
                    ·
                      refine ⟨133789951932333311064235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 2854185641223110636037013 133789951932333311064235)
                      ·
                        rfl

theorem cell23_260555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 2, 2, 2, 6].length) (baseStart_260555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_260555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_260555 prefixEnd_260555 := by exact prefixLift 260555
  have htrace : WordTrace (prefixWord ++ tailWord_260555) baseStart_260555 baseEnd_260555 := by
    simpa [prefixWord, tailWord_260555, baseEnd_260555] using wordTrace_append hprefix tailTrace_260555
  have hstable : (prefixWord ++ tailWord_260555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_260555).length < 2 ^ (prefixWord ++ tailWord_260555).sum := by decide
  have hdescent : baseEnd_260555 < baseStart_260555 := by decide
  rcases family_descends (prefixWord ++ tailWord_260555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_260585 : List Nat := [1, 2, 1, 1, 1, 2, 1, 3, 1, 2, 8]
def baseStart_260585 : Nat := 118140960795 + 260585 * 2 ^ 59
def prefixEnd_260585 : Nat := 4983230072969 + 3 ^ 40 * 260585 * 2
def baseEnd_260585 : Nat := 133805356351968193689097

theorem tailTrace_260585 : CollatzResearch.WordTrace tailWord_260585 prefixEnd_260585 133805356351968193689097 := by
  unfold tailWord_260585
  simp only [CollatzResearch.WordTrace]
  refine ⟨9504315760952524219935209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6336210507301682813290139 9504315760952524219935209)
  ·
    refine ⟨7128236820714393164951407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9504315760952524219935209 7128236820714393164951407)
    ·
      refine ⟨10692355231071589747427111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7128236820714393164951407 10692355231071589747427111)
      ·
        refine ⟨16038532846607384621140667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10692355231071589747427111 16038532846607384621140667)
        ·
          refine ⟨24057799269911076931711001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16038532846607384621140667 24057799269911076931711001)
          ·
            refine ⟨18043349452433307698783251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24057799269911076931711001 18043349452433307698783251)
            ·
              refine ⟨27065024178649961548174877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18043349452433307698783251 27065024178649961548174877)
              ·
                refine ⟨10149384066993735580565579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27065024178649961548174877 10149384066993735580565579)
                ·
                  refine ⟨15224076100490603370848369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10149384066993735580565579 15224076100490603370848369)
                  ·
                    refine ⟨11418057075367952528136277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15224076100490603370848369 11418057075367952528136277)
                    ·
                      refine ⟨133805356351968193689097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 11418057075367952528136277 133805356351968193689097)
                      ·
                        rfl

theorem cell23_260585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 3, 1, 2, 8].length) (baseStart_260585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_260585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_260585 prefixEnd_260585 := by exact prefixLift 260585
  have htrace : WordTrace (prefixWord ++ tailWord_260585) baseStart_260585 baseEnd_260585 := by
    simpa [prefixWord, tailWord_260585, baseEnd_260585] using wordTrace_append hprefix tailTrace_260585
  have hstable : (prefixWord ++ tailWord_260585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_260585).length < 2 ^ (prefixWord ++ tailWord_260585).sum := by decide
  have hdescent : baseEnd_260585 < baseStart_260585 := by decide
  rcases family_descends (prefixWord ++ tailWord_260585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_260614 : List Nat := [6, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2]
def baseStart_260614 : Nat := 118140960795 + 260614 * 2 ^ 59
def prefixEnd_260614 : Nat := 4983230072969 + 3 ^ 40 * 260614 * 2
def baseEnd_260614 : Nat := 133820247290948580226465

theorem tailTrace_260614 : CollatzResearch.WordTrace tailWord_260614 prefixEnd_260614 133820247290948580226465 := by
  unfold tailWord_260614
  simp only [CollatzResearch.WordTrace]
  refine ⟨297042921182733192898153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 6336915651898308115160597 297042921182733192898153)
  ·
    refine ⟨222782190887049894673615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 297042921182733192898153 222782190887049894673615)
    ·
      refine ⟨334173286330574842010423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222782190887049894673615 334173286330574842010423)
      ·
        refine ⟨501259929495862263015635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 334173286330574842010423 501259929495862263015635)
        ·
          refine ⟨751889894243793394523453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 501259929495862263015635 751889894243793394523453)
          ·
            refine ⟨281958710341422522946295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 751889894243793394523453 281958710341422522946295)
            ·
              refine ⟨422938065512133784419443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 281958710341422522946295 422938065512133784419443)
              ·
                refine ⟨634407098268200676629165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 422938065512133784419443 634407098268200676629165)
                ·
                  refine ⟨237902661850575253735937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 634407098268200676629165 237902661850575253735937)
                  ·
                    refine ⟨178426996387931440301953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 237902661850575253735937 178426996387931440301953)
                    ·
                      refine ⟨133820247290948580226465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 178426996387931440301953 133820247290948580226465)
                      ·
                        rfl

theorem cell23_260614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2].length) (baseStart_260614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_260614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_260614 prefixEnd_260614 := by exact prefixLift 260614
  have htrace : WordTrace (prefixWord ++ tailWord_260614) baseStart_260614 baseEnd_260614 := by
    simpa [prefixWord, tailWord_260614, baseEnd_260614] using wordTrace_append hprefix tailTrace_260614
  have hstable : (prefixWord ++ tailWord_260614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_260614).length < 2 ^ (prefixWord ++ tailWord_260614).sum := by decide
  have hdescent : baseEnd_260614 < baseStart_260614 := by decide
  rcases family_descends (prefixWord ++ tailWord_260614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_260640 : List Nat := [2, 1, 1, 6, 2, 2, 1, 2, 1, 3, 2]
def baseStart_260640 : Nat := 118140960795 + 260640 * 2 ^ 59
def prefixEnd_260640 : Nat := 4983230072969 + 3 ^ 40 * 260640 * 2
def baseEnd_260640 : Nat := 133833597787965478501345

theorem tailTrace_260640 : CollatzResearch.WordTrace tailWord_260640 prefixEnd_260640 133833597787965478501345 := by
  unfold tailWord_260640
  simp only [CollatzResearch.WordTrace]
  refine ⟨4753160887876634306593687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6337547850502179075458249 4753160887876634306593687)
  ·
    refine ⟨7129741331814951459890531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4753160887876634306593687 7129741331814951459890531)
    ·
      refine ⟨10694611997722427189835797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7129741331814951459890531 10694611997722427189835797)
      ·
        refine ⟨501309937393238774523553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 10694611997722427189835797 501309937393238774523553)
        ·
          refine ⟨375982453044929080892665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 501309937393238774523553 375982453044929080892665)
          ·
            refine ⟨281986839783696810669499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 375982453044929080892665 281986839783696810669499)
            ·
              refine ⟨422980259675545216004249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 281986839783696810669499 422980259675545216004249)
              ·
                refine ⟨317235194756658912003187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 422980259675545216004249 317235194756658912003187)
                ·
                  refine ⟨475852792134988368004781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 317235194756658912003187 475852792134988368004781)
                  ·
                    refine ⟨178444797050620638001793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 475852792134988368004781 178444797050620638001793)
                    ·
                      refine ⟨133833597787965478501345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 178444797050620638001793 133833597787965478501345)
                      ·
                        rfl

theorem cell23_260640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 2, 1, 2, 1, 3, 2].length) (baseStart_260640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_260640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_260640 prefixEnd_260640 := by exact prefixLift 260640
  have htrace : WordTrace (prefixWord ++ tailWord_260640) baseStart_260640 baseEnd_260640 := by
    simpa [prefixWord, tailWord_260640, baseEnd_260640] using wordTrace_append hprefix tailTrace_260640
  have hstable : (prefixWord ++ tailWord_260640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_260640).length < 2 ^ (prefixWord ++ tailWord_260640).sum := by decide
  have hdescent : baseEnd_260640 < baseStart_260640 := by decide
  rcases family_descends (prefixWord ++ tailWord_260640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_260642 : List Nat := [3, 3, 1, 1, 1, 1, 1, 3, 9]
def baseStart_260642 : Nat := 118140960795 + 260642 * 2 ^ 59
def prefixEnd_260642 : Nat := 4983230072969 + 3 ^ 40 * 260642 * 2
def baseEnd_260642 : Nat := 14870513861030496741815

theorem tailTrace_260642 : CollatzResearch.WordTrace tailWord_260642 prefixEnd_260642 14870513861030496741815 := by
  unfold tailWord_260642
  simp only [CollatzResearch.WordTrace]
  refine ⟨2376598680436505738690045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6337596481164015303173453 2376598680436505738690045)
  ·
    refine ⟨891224505163689652008767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2376598680436505738690045 891224505163689652008767)
    ·
      refine ⟨1336836757745534478013151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 891224505163689652008767 1336836757745534478013151)
      ·
        refine ⟨2005255136618301717019727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1336836757745534478013151 2005255136618301717019727)
        ·
          refine ⟨3007882704927452575529591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2005255136618301717019727 3007882704927452575529591)
          ·
            refine ⟨4511824057391178863294387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3007882704927452575529591 4511824057391178863294387)
            ·
              refine ⟨6767736086086768294941581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4511824057391178863294387 6767736086086768294941581)
              ·
                refine ⟨2537901032282538110603093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6767736086086768294941581 2537901032282538110603093)
                ·
                  refine ⟨14870513861030496741815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 2537901032282538110603093 14870513861030496741815)
                  ·
                    rfl

theorem cell23_260642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 3, 9].length) (baseStart_260642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_260642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_260642 prefixEnd_260642 := by exact prefixLift 260642
  have htrace : WordTrace (prefixWord ++ tailWord_260642) baseStart_260642 baseEnd_260642 := by
    simpa [prefixWord, tailWord_260642, baseEnd_260642] using wordTrace_append hprefix tailTrace_260642
  have hstable : (prefixWord ++ tailWord_260642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_260642).length < 2 ^ (prefixWord ++ tailWord_260642).sum := by decide
  have hdescent : baseEnd_260642 < baseStart_260642 := by decide
  rcases family_descends (prefixWord ++ tailWord_260642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_260659 : List Nat := [1, 1, 1, 2, 4, 2, 2, 5, 5]
def baseStart_260659 : Nat := 118140960795 + 260659 * 2 ^ 59
def prefixEnd_260659 : Nat := 4983230072969 + 3 ^ 40 * 260659 * 2
def baseEnd_260659 : Nat := 14871483768933433795973

theorem tailTrace_260659 : CollatzResearch.WordTrace tailWord_260659 prefixEnd_260659 14871483768933433795973 := by
  unfold tailWord_260659
  simp only [CollatzResearch.WordTrace]
  refine ⟨9507014762684434858129031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6338009841789623238752687 9507014762684434858129031)
  ·
    refine ⟨14260522144026652287193547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9507014762684434858129031 14260522144026652287193547)
    ·
      refine ⟨21390783216039978430790321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14260522144026652287193547 21390783216039978430790321)
      ·
        refine ⟨16043087412029983823092741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21390783216039978430790321 16043087412029983823092741)
        ·
          refine ⟨3008078889755621966829889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16043087412029983823092741 3008078889755621966829889)
          ·
            refine ⟨2256059167316716475122417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3008078889755621966829889 2256059167316716475122417)
            ·
              refine ⟨1692044375487537356341813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2256059167316716475122417 1692044375487537356341813)
              ·
                refine ⟨158629160201956627157045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1692044375487537356341813 158629160201956627157045)
                ·
                  refine ⟨14871483768933433795973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 158629160201956627157045 14871483768933433795973)
                  ·
                    rfl

theorem cell23_260659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 5, 5].length) (baseStart_260659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_260659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_260659 prefixEnd_260659 := by exact prefixLift 260659
  have htrace : WordTrace (prefixWord ++ tailWord_260659) baseStart_260659 baseEnd_260659 := by
    simpa [prefixWord, tailWord_260659, baseEnd_260659] using wordTrace_append hprefix tailTrace_260659
  have hstable : (prefixWord ++ tailWord_260659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_260659).length < 2 ^ (prefixWord ++ tailWord_260659).sum := by decide
  have hdescent : baseEnd_260659 < baseStart_260659 := by decide
  rcases family_descends (prefixWord ++ tailWord_260659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_260736 : List Nat := [2, 1, 1, 2, 1, 6, 2, 1, 3, 4]
def baseStart_260736 : Nat := 118140960795 + 260736 * 2 ^ 59
def prefixEnd_260736 : Nat := 4983230072969 + 3 ^ 40 * 260736 * 2
def baseEnd_260736 : Nat := 44627630643599034300301

theorem tailTrace_260736 : CollatzResearch.WordTrace tailWord_260736 prefixEnd_260736 44627630643599034300301 := by
  unfold tailWord_260736
  simp only [CollatzResearch.WordTrace]
  refine ⟨4754911591702738504341031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6339882122270318005788041 4754911591702738504341031)
  ·
    refine ⟨7132367387554107756511547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4754911591702738504341031 7132367387554107756511547)
    ·
      refine ⟨10698551081331161634767321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7132367387554107756511547 10698551081331161634767321)
      ·
        refine ⟨8023913310998371226075491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10698551081331161634767321 8023913310998371226075491)
        ·
          refine ⟨12035869966497556839113237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8023913310998371226075491 12035869966497556839113237)
          ·
            refine ⟨564181404679572976833433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 12035869966497556839113237 564181404679572976833433)
            ·
              refine ⟨423136053509679732625075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 564181404679572976833433 423136053509679732625075)
              ·
                refine ⟨634704080264519598937613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 423136053509679732625075 634704080264519598937613)
                ·
                  refine ⟨238014030099194849601605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 634704080264519598937613 238014030099194849601605)
                  ·
                    refine ⟨44627630643599034300301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 238014030099194849601605 44627630643599034300301)
                    ·
                      rfl

theorem cell23_260736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 2, 1, 3, 4].length) (baseStart_260736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_260736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_260736 prefixEnd_260736 := by exact prefixLift 260736
  have htrace : WordTrace (prefixWord ++ tailWord_260736) baseStart_260736 baseEnd_260736 := by
    simpa [prefixWord, tailWord_260736, baseEnd_260736] using wordTrace_append hprefix tailTrace_260736
  have hstable : (prefixWord ++ tailWord_260736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_260736).length < 2 ^ (prefixWord ++ tailWord_260736).sum := by decide
  have hdescent : baseEnd_260736 < baseStart_260736 := by decide
  rcases family_descends (prefixWord ++ tailWord_260736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_260759 : List Nat := [1, 1, 3, 3, 2, 1, 1, 1, 2, 5, 3]
def baseStart_260759 : Nat := 118140960795 + 260759 * 2 ^ 59
def prefixEnd_260759 : Nat := 4983230072969 + 3 ^ 40 * 260759 * 2
def baseEnd_260759 : Nat := 133894701985850512913297

theorem tailTrace_260759 : CollatzResearch.WordTrace tailWord_260759 prefixEnd_260759 133894701985850512913297 := by
  unfold tailWord_260759
  simp only [CollatzResearch.WordTrace]
  refine ⟨9510662062322151936769331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6340441374881434624512887 9510662062322151936769331)
  ·
    refine ⟨14265993093483227905153997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9510662062322151936769331 14265993093483227905153997)
    ·
      refine ⟨5349747410056210464432749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14265993093483227905153997 5349747410056210464432749)
      ·
        refine ⟨2006155278771078924162281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5349747410056210464432749 2006155278771078924162281)
        ·
          refine ⟨1504616459078309193121711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2006155278771078924162281 1504616459078309193121711)
          ·
            refine ⟨2256924688617463789682567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1504616459078309193121711 2256924688617463789682567)
            ·
              refine ⟨3385387032926195684523851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2256924688617463789682567 3385387032926195684523851)
              ·
                refine ⟨5078080549389293526785777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3385387032926195684523851 5078080549389293526785777)
                ·
                  refine ⟨3808560412041970145089333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5078080549389293526785777 3808560412041970145089333)
                  ·
                    refine ⟨357052538628934701102125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3808560412041970145089333 357052538628934701102125)
                    ·
                      refine ⟨133894701985850512913297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 357052538628934701102125 133894701985850512913297)
                      ·
                        rfl

theorem cell23_260759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 1, 2, 5, 3].length) (baseStart_260759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_260759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_260759 prefixEnd_260759 := by exact prefixLift 260759
  have htrace : WordTrace (prefixWord ++ tailWord_260759) baseStart_260759 baseEnd_260759 := by
    simpa [prefixWord, tailWord_260759, baseEnd_260759] using wordTrace_append hprefix tailTrace_260759
  have hstable : (prefixWord ++ tailWord_260759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_260759).length < 2 ^ (prefixWord ++ tailWord_260759).sum := by decide
  have hdescent : baseEnd_260759 < baseStart_260759 := by decide
  rcases family_descends (prefixWord ++ tailWord_260759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_260836 : List Nat := [2, 3, 1, 1, 1, 4, 3, 1, 1, 1, 5]
def baseStart_260836 : Nat := 118140960795 + 260836 * 2 ^ 59
def prefixEnd_260836 : Nat := 4983230072969 + 3 ^ 40 * 260836 * 2
def baseEnd_260836 : Nat := 133934239996246711650443

theorem tailTrace_260836 : CollatzResearch.WordTrace tailWord_260836 prefixEnd_260836 133934239996246711650443 := by
  unfold tailWord_260836
  simp only [CollatzResearch.WordTrace]
  refine ⟨4756735241521597043661181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6342313655362129391548241 4756735241521597043661181)
  ·
    refine ⟨1783775715570598891372943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4756735241521597043661181 1783775715570598891372943)
    ·
      refine ⟨2675663573355898337059415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1783775715570598891372943 2675663573355898337059415)
      ·
        refine ⟨4013495360033847505589123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2675663573355898337059415 4013495360033847505589123)
        ·
          refine ⟨6020243040050771258383685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4013495360033847505589123 6020243040050771258383685)
          ·
            refine ⟨1128795570009519610946941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6020243040050771258383685 1128795570009519610946941)
            ·
              refine ⟨423298338753569854105103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1128795570009519610946941 423298338753569854105103)
              ·
                refine ⟨634947508130354781157655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 423298338753569854105103 634947508130354781157655)
                ·
                  refine ⟨952421262195532171736483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 634947508130354781157655 952421262195532171736483)
                  ·
                    refine ⟨1428631893293298257604725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 952421262195532171736483 1428631893293298257604725)
                    ·
                      refine ⟨133934239996246711650443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1428631893293298257604725 133934239996246711650443)
                      ·
                        rfl

theorem cell23_260836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 3, 1, 1, 1, 5].length) (baseStart_260836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_260836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_260836 prefixEnd_260836 := by exact prefixLift 260836
  have htrace : WordTrace (prefixWord ++ tailWord_260836) baseStart_260836 baseEnd_260836 := by
    simpa [prefixWord, tailWord_260836, baseEnd_260836] using wordTrace_append hprefix tailTrace_260836
  have hstable : (prefixWord ++ tailWord_260836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_260836).length < 2 ^ (prefixWord ++ tailWord_260836).sum := by decide
  have hdescent : baseEnd_260836 < baseStart_260836 := by decide
  rcases family_descends (prefixWord ++ tailWord_260836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_260879 : List Nat := [1, 1, 2, 1, 1, 1, 6, 1, 2, 2, 5]
def baseStart_260879 : Nat := 118140960795 + 260879 * 2 ^ 59
def prefixEnd_260879 : Nat := 4983230072969 + 3 ^ 40 * 260879 * 2
def baseEnd_260879 : Nat := 133956319664390043412745

theorem tailTrace_260879 : CollatzResearch.WordTrace tailWord_260879 prefixEnd_260879 133956319664390043412745 := by
  unfold tailWord_260879
  simp only [CollatzResearch.WordTrace]
  refine ⟨9515038821887412431137691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6343359214591608287425127 9515038821887412431137691)
  ·
    refine ⟨14272558232831118646706537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9515038821887412431137691 14272558232831118646706537)
    ·
      refine ⟨10704418674623338985029903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14272558232831118646706537 10704418674623338985029903)
      ·
        refine ⟨16056628011935008477544855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10704418674623338985029903 16056628011935008477544855)
        ·
          refine ⟨24084942017902512716317283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16056628011935008477544855 24084942017902512716317283)
          ·
            refine ⟨36127413026853769074475925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24084942017902512716317283 36127413026853769074475925)
            ·
              refine ⟨1693472485633770425366059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 36127413026853769074475925 1693472485633770425366059)
              ·
                refine ⟨2540208728450655638049089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1693472485633770425366059 2540208728450655638049089)
                ·
                  refine ⟨1905156546337991728536817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2540208728450655638049089 1905156546337991728536817)
                  ·
                    refine ⟨1428867409753493796402613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1905156546337991728536817 1428867409753493796402613)
                    ·
                      refine ⟨133956319664390043412745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1428867409753493796402613 133956319664390043412745)
                      ·
                        rfl

theorem cell23_260879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 1, 2, 2, 5].length) (baseStart_260879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_260879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_260879 prefixEnd_260879 := by exact prefixLift 260879
  have htrace : WordTrace (prefixWord ++ tailWord_260879) baseStart_260879 baseEnd_260879 := by
    simpa [prefixWord, tailWord_260879, baseEnd_260879] using wordTrace_append hprefix tailTrace_260879
  have hstable : (prefixWord ++ tailWord_260879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_260879).length < 2 ^ (prefixWord ++ tailWord_260879).sum := by decide
  have hdescent : baseEnd_260879 < baseStart_260879 := by decide
  rcases family_descends (prefixWord ++ tailWord_260879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_260887 : List Nat := [1, 1, 3, 4, 3, 2, 2, 1, 1, 2, 3]
def baseStart_260887 : Nat := 118140960795 + 260887 * 2 ^ 59
def prefixEnd_260887 : Nat := 4983230072969 + 3 ^ 40 * 260887 * 2
def baseEnd_260887 : Nat := 133960427509626012112709

theorem tailTrace_260887 : CollatzResearch.WordTrace tailWord_260887 prefixEnd_260887 133960427509626012112709 := by
  unfold tailWord_260887
  simp only [CollatzResearch.WordTrace]
  refine ⟨9515330605858429797428915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6343553737238953198285943 9515330605858429797428915)
  ·
    refine ⟨14272995908787644696143373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9515330605858429797428915 14272995908787644696143373)
    ·
      refine ⟨5352373465795366761053765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14272995908787644696143373 5352373465795366761053765)
      ·
        refine ⟨1003570024836631267697581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5352373465795366761053765 1003570024836631267697581)
        ·
          refine ⟨376338759313736725386593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1003570024836631267697581 376338759313736725386593)
          ·
            refine ⟨282254069485302544039945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 376338759313736725386593 282254069485302544039945)
            ·
              refine ⟨211690552113976908029959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 282254069485302544039945 211690552113976908029959)
              ·
                refine ⟨317535828170965362044939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 211690552113976908029959 317535828170965362044939)
                ·
                  refine ⟨476303742256448043067409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 317535828170965362044939 476303742256448043067409)
                  ·
                    refine ⟨357227806692336032300557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 476303742256448043067409 357227806692336032300557)
                    ·
                      refine ⟨133960427509626012112709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 357227806692336032300557 133960427509626012112709)
                      ·
                        rfl

theorem cell23_260887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 2, 2, 1, 1, 2, 3].length) (baseStart_260887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_260887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_260887 prefixEnd_260887 := by exact prefixLift 260887
  have htrace : WordTrace (prefixWord ++ tailWord_260887) baseStart_260887 baseEnd_260887 := by
    simpa [prefixWord, tailWord_260887, baseEnd_260887] using wordTrace_append hprefix tailTrace_260887
  have hstable : (prefixWord ++ tailWord_260887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_260887).length < 2 ^ (prefixWord ++ tailWord_260887).sum := by decide
  have hdescent : baseEnd_260887 < baseStart_260887 := by decide
  rcases family_descends (prefixWord ++ tailWord_260887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_260889 : List Nat := [1, 2, 1, 2, 1, 1, 1, 4, 1, 5, 4]
def baseStart_260889 : Nat := 118140960795 + 260889 * 2 ^ 59
def prefixEnd_260889 : Nat := 4983230072969 + 3 ^ 40 * 260889 * 2
def baseEnd_260889 : Nat := 133961454470935004287699

theorem tailTrace_260889 : CollatzResearch.WordTrace tailWord_260889 prefixEnd_260889 133961454470935004287699 := by
  unfold tailWord_260889
  simp only [CollatzResearch.WordTrace]
  refine ⟨9515403551851184139001721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6343602367900789426001147 9515403551851184139001721)
  ·
    refine ⟨7136552663888388104251291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9515403551851184139001721 7136552663888388104251291)
    ·
      refine ⟨10704828995832582156376937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7136552663888388104251291 10704828995832582156376937)
      ·
        refine ⟨8028621746874436617282703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10704828995832582156376937 8028621746874436617282703)
        ·
          refine ⟨12042932620311654925924055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8028621746874436617282703 12042932620311654925924055)
          ·
            refine ⟨18064398930467482388886083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12042932620311654925924055 18064398930467482388886083)
            ·
              refine ⟨27096598395701223583329125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18064398930467482388886083 27096598395701223583329125)
              ·
                refine ⟨5080612199193979421874211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27096598395701223583329125 5080612199193979421874211)
                ·
                  refine ⟨7620918298790969132811317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5080612199193979421874211 7620918298790969132811317)
                  ·
                    refine ⟨714461090511653356201061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7620918298790969132811317 714461090511653356201061)
                    ·
                      refine ⟨133961454470935004287699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 714461090511653356201061 133961454470935004287699)
                      ·
                        rfl

theorem cell23_260889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 4, 1, 5, 4].length) (baseStart_260889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_260889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_260889 prefixEnd_260889 := by exact prefixLift 260889
  have htrace : WordTrace (prefixWord ++ tailWord_260889) baseStart_260889 baseEnd_260889 := by
    simpa [prefixWord, tailWord_260889, baseEnd_260889] using wordTrace_append hprefix tailTrace_260889
  have hstable : (prefixWord ++ tailWord_260889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_260889).length < 2 ^ (prefixWord ++ tailWord_260889).sum := by decide
  have hdescent : baseEnd_260889 < baseStart_260889 := by decide
  rcases family_descends (prefixWord ++ tailWord_260889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_260900 : List Nat := [2, 3, 1, 3, 3, 1, 1, 1, 4, 1, 3]
def baseStart_260900 : Nat := 118140960795 + 260900 * 2 ^ 59
def prefixEnd_260900 : Nat := 4983230072969 + 3 ^ 40 * 260900 * 2
def baseEnd_260900 : Nat := 133967102758134461250149

theorem tailTrace_260900 : CollatzResearch.WordTrace tailWord_260900 prefixEnd_260900 133967102758134461250149 := by
  unfold tailWord_260900
  simp only [CollatzResearch.WordTrace]
  refine ⟨4757902377405666508826077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6343869836540888678434769 4757902377405666508826077)
  ·
    refine ⟨1784213391527124940809779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4757902377405666508826077 1784213391527124940809779)
    ·
      refine ⟨2676320087290687411214669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1784213391527124940809779 2676320087290687411214669)
      ·
        refine ⟨1003620032734007779205501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2676320087290687411214669 1003620032734007779205501)
        ·
          refine ⟨376357512275252917202063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1003620032734007779205501 376357512275252917202063)
          ·
            refine ⟨564536268412879375803095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 376357512275252917202063 564536268412879375803095)
            ·
              refine ⟨846804402619319063704643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 564536268412879375803095 846804402619319063704643)
              ·
                refine ⟨1270206603928978595556965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 846804402619319063704643 1270206603928978595556965)
                ·
                  refine ⟨238163738236683486666931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1270206603928978595556965 238163738236683486666931)
                  ·
                    refine ⟨357245607355025230000397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 238163738236683486666931 357245607355025230000397)
                    ·
                      refine ⟨133967102758134461250149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 357245607355025230000397 133967102758134461250149)
                      ·
                        rfl

theorem cell23_260900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 1, 1, 4, 1, 3].length) (baseStart_260900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_260900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_260900 prefixEnd_260900 := by exact prefixLift 260900
  have htrace : WordTrace (prefixWord ++ tailWord_260900) baseStart_260900 baseEnd_260900 := by
    simpa [prefixWord, tailWord_260900, baseEnd_260900] using wordTrace_append hprefix tailTrace_260900
  have hstable : (prefixWord ++ tailWord_260900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_260900).length < 2 ^ (prefixWord ++ tailWord_260900).sum := by decide
  have hdescent : baseEnd_260900 < baseStart_260900 := by decide
  rcases family_descends (prefixWord ++ tailWord_260900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_260917 : List Nat := [1, 3, 3, 1, 3, 2, 3, 1, 2, 1, 3]
def baseStart_260917 : Nat := 118140960795 + 260917 * 2 ^ 59
def prefixEnd_260917 : Nat := 4983230072969 + 3 ^ 40 * 260917 * 2
def baseEnd_260917 : Nat := 133975831929260894737571

theorem tailTrace_260917 : CollatzResearch.WordTrace tailWord_260917 prefixEnd_260917 133975831929260894737571 := by
  unfold tailWord_260917
  simp only [CollatzResearch.WordTrace]
  refine ⟨9516424795749744921021005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6344283197166496614014003 9516424795749744921021005)
  ·
    refine ⟨3568659298406154345382877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9516424795749744921021005 3568659298406154345382877)
    ·
      refine ⟨1338247236902307879518579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3568659298406154345382877 1338247236902307879518579)
      ·
        refine ⟨2007370855353461819277869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1338247236902307879518579 2007370855353461819277869)
        ·
          refine ⟨752764070757548182229201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2007370855353461819277869 752764070757548182229201)
          ·
            refine ⟨564573053068161136671901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 752764070757548182229201 564573053068161136671901)
            ·
              refine ⟨211714894900560426251963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 564573053068161136671901 211714894900560426251963)
              ·
                refine ⟨317572342350840639377945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 211714894900560426251963 317572342350840639377945)
                ·
                  refine ⟨238179256763130479533459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 317572342350840639377945 238179256763130479533459)
                  ·
                    refine ⟨357268885144695719300189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 238179256763130479533459 357268885144695719300189)
                    ·
                      refine ⟨133975831929260894737571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 357268885144695719300189 133975831929260894737571)
                      ·
                        rfl

theorem cell23_260917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 3, 1, 2, 1, 3].length) (baseStart_260917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_260917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_260917 prefixEnd_260917 := by exact prefixLift 260917
  have htrace : WordTrace (prefixWord ++ tailWord_260917) baseStart_260917 baseEnd_260917 := by
    simpa [prefixWord, tailWord_260917, baseEnd_260917] using wordTrace_append hprefix tailTrace_260917
  have hstable : (prefixWord ++ tailWord_260917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_260917).length < 2 ^ (prefixWord ++ tailWord_260917).sum := by decide
  have hdescent : baseEnd_260917 < baseStart_260917 := by decide
  rcases family_descends (prefixWord ++ tailWord_260917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_260940 : List Nat := [2, 2, 1, 3, 3, 1, 1, 2, 4, 2, 2]
def baseStart_260940 : Nat := 118140960795 + 260940 * 2 ^ 59
def prefixEnd_260940 : Nat := 4983230072969 + 3 ^ 40 * 260940 * 2
def baseEnd_260940 : Nat := 133987641984314304749965

theorem tailTrace_260940 : CollatzResearch.WordTrace tailWord_260940 prefixEnd_260940 133987641984314304749965 := by
  unfold tailWord_260940
  simp only [CollatzResearch.WordTrace]
  refine ⟨4758631837333209924554137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6344842449777613232738849 4758631837333209924554137)
  ·
    refine ⟨3568973877999907443415603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4758631837333209924554137 3568973877999907443415603)
    ·
      refine ⟨5353460816999861165123405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3568973877999907443415603 5353460816999861165123405)
      ·
        refine ⟨2007547806374947936921277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5353460816999861165123405 2007547806374947936921277)
        ·
          refine ⟨752830427390605476345479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2007547806374947936921277 752830427390605476345479)
          ·
            refine ⟨1129245641085908214518219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 752830427390605476345479 1129245641085908214518219)
            ·
              refine ⟨1693868461628862321777329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1129245641085908214518219 1693868461628862321777329)
              ·
                refine ⟨1270401346221646741332997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1693868461628862321777329 1270401346221646741332997)
                ·
                  refine ⟨238200252416558763999937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1270401346221646741332997 238200252416558763999937)
                  ·
                    refine ⟨178650189312419072999953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 238200252416558763999937 178650189312419072999953)
                    ·
                      refine ⟨133987641984314304749965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 178650189312419072999953 133987641984314304749965)
                      ·
                        rfl

theorem cell23_260940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 2, 4, 2, 2].length) (baseStart_260940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_260940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_260940 prefixEnd_260940 := by exact prefixLift 260940
  have htrace : WordTrace (prefixWord ++ tailWord_260940) baseStart_260940 baseEnd_260940 := by
    simpa [prefixWord, tailWord_260940, baseEnd_260940] using wordTrace_append hprefix tailTrace_260940
  have hstable : (prefixWord ++ tailWord_260940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_260940).length < 2 ^ (prefixWord ++ tailWord_260940).sum := by decide
  have hdescent : baseEnd_260940 < baseStart_260940 := by decide
  rcases family_descends (prefixWord ++ tailWord_260940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_260963 : List Nat := [1, 1, 1, 5, 3, 3, 1, 1, 7]
def baseStart_260963 : Nat := 118140960795 + 260963 * 2 ^ 59
def prefixEnd_260963 : Nat := 4983230072969 + 3 ^ 40 * 260963 * 2
def baseEnd_260963 : Nat := 14888828004374190529151

theorem tailTrace_260963 : CollatzResearch.WordTrace tailWord_260963 prefixEnd_260963 14888828004374190529151 := by
  unfold tailWord_260963
  simp only [CollatzResearch.WordTrace]
  refine ⟨9518102553583094777195543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6345401702388729851463695 9518102553583094777195543)
  ·
    refine ⟨14277153830374642165793315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9518102553583094777195543 14277153830374642165793315)
    ·
      refine ⟨21415730745561963248689973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14277153830374642165793315 21415730745561963248689973)
      ·
        refine ⟨2007724757396434054564685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 21415730745561963248689973 2007724757396434054564685)
        ·
          refine ⟨752896784023662770461757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2007724757396434054564685 752896784023662770461757)
          ·
            refine ⟨282336294008873538923159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 752896784023662770461757 282336294008873538923159)
            ·
              refine ⟨423504441013310308384739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 282336294008873538923159 423504441013310308384739)
              ·
                refine ⟨635256661519965462577109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 423504441013310308384739 635256661519965462577109)
                ·
                  refine ⟨14888828004374190529151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 635256661519965462577109 14888828004374190529151)
                  ·
                    rfl

theorem cell23_260963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 3, 1, 1, 7].length) (baseStart_260963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_260963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_260963 prefixEnd_260963 := by exact prefixLift 260963
  have htrace : WordTrace (prefixWord ++ tailWord_260963) baseStart_260963 baseEnd_260963 := by
    simpa [prefixWord, tailWord_260963, baseEnd_260963] using wordTrace_append hprefix tailTrace_260963
  have hstable : (prefixWord ++ tailWord_260963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_260963).length < 2 ^ (prefixWord ++ tailWord_260963).sum := by decide
  have hdescent : baseEnd_260963 < baseStart_260963 := by decide
  rcases family_descends (prefixWord ++ tailWord_260963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_260974 : List Nat := [4, 1, 2, 3, 2, 1, 1, 3, 2, 2, 2]
def baseStart_260974 : Nat := 118140960795 + 260974 * 2 ^ 59
def prefixEnd_260974 : Nat := 4983230072969 + 3 ^ 40 * 260974 * 2
def baseEnd_260974 : Nat := 134005100326567171724809

theorem tailTrace_260974 : CollatzResearch.WordTrace tailWord_260974 prefixEnd_260974 134005100326567171724809 := by
  unfold tailWord_260974
  simp only [CollatzResearch.WordTrace]
  refine ⟨1189812969567905456980747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6345669171028829103897317 1189812969567905456980747)
  ·
    refine ⟨1784719454351858185471121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1189812969567905456980747 1784719454351858185471121)
    ·
      refine ⟨1338539590763893639103341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1784719454351858185471121 1338539590763893639103341)
      ·
        refine ⟨501952346536460114663753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1338539590763893639103341 501952346536460114663753)
        ·
          refine ⟨376464259902345085997815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 501952346536460114663753 376464259902345085997815)
          ·
            refine ⟨564696389853517628996723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 376464259902345085997815 564696389853517628996723)
            ·
              refine ⟨847044584780276443495085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 564696389853517628996723 847044584780276443495085)
              ·
                refine ⟨317641719292603666310657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 847044584780276443495085 317641719292603666310657)
                ·
                  refine ⟨238231289469452749732993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 317641719292603666310657 238231289469452749732993)
                  ·
                    refine ⟨178673467102089562299745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 238231289469452749732993 178673467102089562299745)
                    ·
                      refine ⟨134005100326567171724809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 178673467102089562299745 134005100326567171724809)
                      ·
                        rfl

theorem cell23_260974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 1, 3, 2, 2, 2].length) (baseStart_260974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_260974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_260974 prefixEnd_260974 := by exact prefixLift 260974
  have htrace : WordTrace (prefixWord ++ tailWord_260974) baseStart_260974 baseEnd_260974 := by
    simpa [prefixWord, tailWord_260974, baseEnd_260974] using wordTrace_append hprefix tailTrace_260974
  have hstable : (prefixWord ++ tailWord_260974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_260974).length < 2 ^ (prefixWord ++ tailWord_260974).sum := by decide
  have hdescent : baseEnd_260974 < baseStart_260974 := by decide
  rcases family_descends (prefixWord ++ tailWord_260974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_261013 : List Nat := [1, 3, 2, 1, 1, 4, 2, 2, 2, 1, 4]
def baseStart_261013 : Nat := 118140960795 + 261013 * 2 ^ 59
def prefixEnd_261013 : Nat := 4983230072969 + 3 ^ 40 * 261013 * 2
def baseEnd_261013 : Nat := 134025126072092519137129

theorem tailTrace_261013 : CollatzResearch.WordTrace tailWord_261013 prefixEnd_261013 134025126072092519137129 := by
  unfold tailWord_261013
  simp only [CollatzResearch.WordTrace]
  refine ⟨9519926203401953316515693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6346617468934635544343795 9519926203401953316515693)
  ·
    refine ⟨3569972326275732493693385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9519926203401953316515693 3569972326275732493693385)
    ·
      refine ⟨2677479244706799370270039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3569972326275732493693385 2677479244706799370270039)
      ·
        refine ⟨4016218867060199055405059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2677479244706799370270039 4016218867060199055405059)
        ·
          refine ⟨6024328300590298583107589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4016218867060199055405059 6024328300590298583107589)
          ·
            refine ⟨1129561556360680984332673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6024328300590298583107589 1129561556360680984332673)
            ·
              refine ⟨847171167270510738249505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1129561556360680984332673 847171167270510738249505)
              ·
                refine ⟨635378375452883053687129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 847171167270510738249505 635378375452883053687129)
                ·
                  refine ⟨476533781589662290265347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 635378375452883053687129 476533781589662290265347)
                  ·
                    refine ⟨714800672384493435398021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 476533781589662290265347 714800672384493435398021)
                    ·
                      refine ⟨134025126072092519137129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 714800672384493435398021 134025126072092519137129)
                      ·
                        rfl

theorem cell23_261013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 2, 2, 2, 1, 4].length) (baseStart_261013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_261013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_261013 prefixEnd_261013 := by exact prefixLift 261013
  have htrace : WordTrace (prefixWord ++ tailWord_261013) baseStart_261013 baseEnd_261013 := by
    simpa [prefixWord, tailWord_261013, baseEnd_261013] using wordTrace_append hprefix tailTrace_261013
  have hstable : (prefixWord ++ tailWord_261013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_261013).length < 2 ^ (prefixWord ++ tailWord_261013).sum := by decide
  have hdescent : baseEnd_261013 < baseStart_261013 := by decide
  rcases family_descends (prefixWord ++ tailWord_261013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_261014 : List Nat := [5, 3, 1, 1, 1, 2, 1, 4, 5]
def baseStart_261014 : Nat := 118140960795 + 261014 * 2 ^ 59
def prefixEnd_261014 : Nat := 4983230072969 + 3 ^ 40 * 261014 * 2
def baseEnd_261014 : Nat := 14891737728083001691625

theorem tailTrace_261014 : CollatzResearch.WordTrace tailWord_261014 prefixEnd_261014 14891737728083001691625 := by
  unfold tailWord_261014
  simp only [CollatzResearch.WordTrace]
  refine ⟨594997667274895655456381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6346641784265553658201397 594997667274895655456381)
  ·
    refine ⟨223124125228085870796143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 594997667274895655456381 223124125228085870796143)
    ·
      refine ⟨334686187842128806194215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223124125228085870796143 334686187842128806194215)
      ·
        refine ⟨502029281763193209291323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 334686187842128806194215 502029281763193209291323)
        ·
          refine ⟨753043922644789813936985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 502029281763193209291323 753043922644789813936985)
          ·
            refine ⟨564782941983592360452739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 753043922644789813936985 564782941983592360452739)
            ·
              refine ⟨847174412975388540679109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 564782941983592360452739 847174412975388540679109)
              ·
                refine ⟨158845202432885351377333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 847174412975388540679109 158845202432885351377333)
                ·
                  refine ⟨14891737728083001691625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 158845202432885351377333 14891737728083001691625)
                  ·
                    rfl

theorem cell23_261014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 1, 4, 5].length) (baseStart_261014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_261014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_261014 prefixEnd_261014 := by exact prefixLift 261014
  have htrace : WordTrace (prefixWord ++ tailWord_261014) baseStart_261014 baseEnd_261014 := by
    simpa [prefixWord, tailWord_261014, baseEnd_261014] using wordTrace_append hprefix tailTrace_261014
  have hstable : (prefixWord ++ tailWord_261014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_261014).length < 2 ^ (prefixWord ++ tailWord_261014).sum := by decide
  have hdescent : baseEnd_261014 < baseStart_261014 := by decide
  rcases family_descends (prefixWord ++ tailWord_261014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_261070 : List Nat := [4, 1, 1, 1, 2, 5, 1, 2, 6]
def baseStart_261070 : Nat := 118140960795 + 261070 * 2 ^ 59
def prefixEnd_261070 : Nat := 4983230072969 + 3 ^ 40 * 261070 * 2
def baseEnd_261070 : Nat := 14894932718822088458263

theorem tailTrace_261070 : CollatzResearch.WordTrace tailWord_261070 prefixEnd_261070 14894932718822088458263 := by
  unfold tailWord_261070
  simp only [CollatzResearch.WordTrace]
  refine ⟨1190250645524431506417583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6348003442796968034227109 1190250645524431506417583)
  ·
    refine ⟨1785375968286647259626375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1190250645524431506417583 1785375968286647259626375)
    ·
      refine ⟨2678063952429970889439563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1785375968286647259626375 2678063952429970889439563)
      ·
        refine ⟨4017095928644956334159345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2678063952429970889439563 4017095928644956334159345)
        ·
          refine ⟨3012821946483717250619509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4017095928644956334159345 3012821946483717250619509)
          ·
            refine ⟨282452057482848492245579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3012821946483717250619509 282452057482848492245579)
            ·
              refine ⟨423678086224272738368369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 282452057482848492245579 423678086224272738368369)
              ·
                refine ⟨317758564668204553776277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 423678086224272738368369 317758564668204553776277)
                ·
                  refine ⟨14894932718822088458263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 317758564668204553776277 14894932718822088458263)
                  ·
                    rfl

theorem cell23_261070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 5, 1, 2, 6].length) (baseStart_261070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_261070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_261070 prefixEnd_261070 := by exact prefixLift 261070
  have htrace : WordTrace (prefixWord ++ tailWord_261070) baseStart_261070 baseEnd_261070 := by
    simpa [prefixWord, tailWord_261070, baseEnd_261070] using wordTrace_append hprefix tailTrace_261070
  have hstable : (prefixWord ++ tailWord_261070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_261070).length < 2 ^ (prefixWord ++ tailWord_261070).sum := by decide
  have hdescent : baseEnd_261070 < baseStart_261070 := by decide
  rcases family_descends (prefixWord ++ tailWord_261070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_261080 : List Nat := [2, 1, 2, 2, 2, 3, 1, 3, 3, 1, 3]
def baseStart_261080 : Nat := 118140960795 + 261080 * 2 ^ 59
def prefixEnd_261080 : Nat := 4983230072969 + 3 ^ 40 * 261080 * 2
def baseEnd_261080 : Nat := 134059529275943756999321

theorem tailTrace_261080 : CollatzResearch.WordTrace tailWord_261080 prefixEnd_261080 134059529275943756999321 := by
  unfold tailWord_261080
  simp only [CollatzResearch.WordTrace]
  refine ⟨4761184947079611879602347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6348246596106149172803129 4761184947079611879602347)
  ·
    refine ⟨7141777420619417819403521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4761184947079611879602347 7141777420619417819403521)
    ·
      refine ⟨5356333065464563364552641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7141777420619417819403521 5356333065464563364552641)
      ·
        refine ⟨4017249799098422523414481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5356333065464563364552641 4017249799098422523414481)
        ·
          refine ⟨3012937349323816892560861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4017249799098422523414481 3012937349323816892560861)
          ·
            refine ⟨1129851505996431334710323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3012937349323816892560861 1129851505996431334710323)
            ·
              refine ⟨1694777258994647002065485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1129851505996431334710323 1694777258994647002065485)
              ·
                refine ⟨635541472122992625774557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1694777258994647002065485 635541472122992625774557)
                ·
                  refine ⟨238328052046122234665459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 635541472122992625774557 238328052046122234665459)
                  ·
                    refine ⟨357492078069183351998189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 238328052046122234665459 357492078069183351998189)
                    ·
                      refine ⟨134059529275943756999321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 357492078069183351998189 134059529275943756999321)
                      ·
                        rfl

theorem cell23_261080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 3, 3, 1, 3].length) (baseStart_261080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_261080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_261080 prefixEnd_261080 := by exact prefixLift 261080
  have htrace : WordTrace (prefixWord ++ tailWord_261080) baseStart_261080 baseEnd_261080 := by
    simpa [prefixWord, tailWord_261080, baseEnd_261080] using wordTrace_append hprefix tailTrace_261080
  have hstable : (prefixWord ++ tailWord_261080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_261080).length < 2 ^ (prefixWord ++ tailWord_261080).sum := by decide
  have hdescent : baseEnd_261080 < baseStart_261080 := by decide
  rcases family_descends (prefixWord ++ tailWord_261080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
