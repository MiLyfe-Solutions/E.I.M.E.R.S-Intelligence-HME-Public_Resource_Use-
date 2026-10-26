import V185TrunkScan23Chunk0564

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_3340626 : List Nat := [3, 2, 2, 1, 1, 1, 4, 4, 1, 1, 3]
def baseStart_3340626 : Nat := 118140960795 + 3340626 * 2 ^ 59
def prefixEnd_3340626 : Nat := 4983230072969 + 3 ^ 40 * 3340626 * 2
def baseEnd_3340626 : Nat := 1715346824906752019111747

theorem tailTrace_3340626 : CollatzResearch.WordTrace tailWord_3340626 prefixEnd_3340626 1715346824906752019111747 := by
  unfold tailWord_3340626
  simp only [CollatzResearch.WordTrace]
  refine ⟨30460659998872502585854433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81228426663660006895611821 30460659998872502585854433)
  ·
    refine ⟨22845494999154376939390825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30460659998872502585854433 22845494999154376939390825)
    ·
      refine ⟨17134121249365782704543119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22845494999154376939390825 17134121249365782704543119)
      ·
        refine ⟨25701181874048674056814679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17134121249365782704543119 25701181874048674056814679)
        ·
          refine ⟨38551772811073011085222019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25701181874048674056814679 38551772811073011085222019)
          ·
            refine ⟨57827659216609516627833029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38551772811073011085222019 57827659216609516627833029)
            ·
              refine ⟨10842686103114284367718693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57827659216609516627833029 10842686103114284367718693)
              ·
                refine ⟨2033003644333928318947255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10842686103114284367718693 2033003644333928318947255)
                ·
                  refine ⟨3049505466500892478420883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2033003644333928318947255 3049505466500892478420883)
                  ·
                    refine ⟨4574258199751338717631325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3049505466500892478420883 4574258199751338717631325)
                    ·
                      refine ⟨1715346824906752019111747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4574258199751338717631325 1715346824906752019111747)
                      ·
                        rfl

theorem cell23_3340626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 4, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 4, 4, 1, 1, 3].length) (baseStart_3340626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3340626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3340626 prefixEnd_3340626 := by exact prefixLift 3340626
  have htrace : WordTrace (prefixWord ++ tailWord_3340626) baseStart_3340626 baseEnd_3340626 := by
    simpa [prefixWord, tailWord_3340626, baseEnd_3340626] using wordTrace_append hprefix tailTrace_3340626
  have hstable : (prefixWord ++ tailWord_3340626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3340626).length < 2 ^ (prefixWord ++ tailWord_3340626).sum := by decide
  have hdescent : baseEnd_3340626 < baseStart_3340626 := by decide
  rcases family_descends (prefixWord ++ tailWord_3340626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3340649 : List Nat := [1, 2, 1, 1, 1, 3, 3, 4, 3, 2, 2]
def baseStart_3340649 : Nat := 118140960795 + 3340649 * 2 ^ 59
def prefixEnd_3340649 : Nat := 4983230072969 + 3 ^ 40 * 3340649 * 2
def baseEnd_3340649 : Nat := 1715358634961805429124141

theorem tailTrace_3340649 : CollatzResearch.WordTrace tailWord_3340649 prefixEnd_3340649 1715358634961805429124141 := by
  unfold tailWord_3340649
  simp only [CollatzResearch.WordTrace]
  refine ⟨121843478874406685271505001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81228985916271123514336667 121843478874406685271505001)
  ·
    refine ⟨91382609155805013953628751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121843478874406685271505001 91382609155805013953628751)
    ·
      refine ⟨137073913733707520930443127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91382609155805013953628751 137073913733707520930443127)
      ·
        refine ⟨205610870600561281395664691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137073913733707520930443127 205610870600561281395664691)
        ·
          refine ⟨308416305900841922093497037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 205610870600561281395664691 308416305900841922093497037)
          ·
            refine ⟨115656114712815720785061389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 308416305900841922093497037 115656114712815720785061389)
            ·
              refine ⟨43371043017305895294398021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 115656114712815720785061389 43371043017305895294398021)
              ·
                refine ⟨8132070565744855367699629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43371043017305895294398021 8132070565744855367699629)
                ·
                  refine ⟨3049526462154320762887361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8132070565744855367699629 3049526462154320762887361)
                  ·
                    refine ⟨2287144846615740572165521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3049526462154320762887361 2287144846615740572165521)
                    ·
                      refine ⟨1715358634961805429124141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2287144846615740572165521 1715358634961805429124141)
                      ·
                        rfl

theorem cell23_3340649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 4, 3, 2, 2].length) (baseStart_3340649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3340649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3340649 prefixEnd_3340649 := by exact prefixLift 3340649
  have htrace : WordTrace (prefixWord ++ tailWord_3340649) baseStart_3340649 baseEnd_3340649 := by
    simpa [prefixWord, tailWord_3340649, baseEnd_3340649] using wordTrace_append hprefix tailTrace_3340649
  have hstable : (prefixWord ++ tailWord_3340649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3340649).length < 2 ^ (prefixWord ++ tailWord_3340649).sum := by decide
  have hdescent : baseEnd_3340649 < baseStart_3340649 := by decide
  rcases family_descends (prefixWord ++ tailWord_3340649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3340669 : List Nat := [1, 4, 1, 1, 2, 3, 2, 3, 1, 2, 3]
def baseStart_3340669 : Nat := 118140960795 + 3340669 * 2 ^ 59
def prefixEnd_3340669 : Nat := 4983230072969 + 3 ^ 40 * 3340669 * 2
def baseEnd_3340669 : Nat := 1715368904574895350874049

theorem tailTrace_3340669 : CollatzResearch.WordTrace tailWord_3340669 prefixEnd_3340669 1715368904574895350874049 := by
  unfold tailWord_3340669
  simp only [CollatzResearch.WordTrace]
  refine ⟨121844208334334228687233061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81229472222889485791488707 121844208334334228687233061)
  ·
    refine ⟨22845789062687667878856199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 121844208334334228687233061 22845789062687667878856199)
    ·
      refine ⟨34268683594031501818284299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22845789062687667878856199 34268683594031501818284299)
      ·
        refine ⟨51403025391047252727426449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34268683594031501818284299 51403025391047252727426449)
        ·
          refine ⟨38552269043285439545569837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51403025391047252727426449 38552269043285439545569837)
          ·
            refine ⟨14457100891232039829588689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38552269043285439545569837 14457100891232039829588689)
            ·
              refine ⟨10842825668424029872191517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14457100891232039829588689 10842825668424029872191517)
              ·
                refine ⟨4066059625659011202071819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10842825668424029872191517 4066059625659011202071819)
                ·
                  refine ⟨6099089438488516803107729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4066059625659011202071819 6099089438488516803107729)
                  ·
                    refine ⟨4574317078866387602330797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6099089438488516803107729 4574317078866387602330797)
                    ·
                      refine ⟨1715368904574895350874049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4574317078866387602330797 1715368904574895350874049)
                      ·
                        rfl

theorem cell23_3340669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 2, 3, 1, 2, 3].length) (baseStart_3340669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3340669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3340669 prefixEnd_3340669 := by exact prefixLift 3340669
  have htrace : WordTrace (prefixWord ++ tailWord_3340669) baseStart_3340669 baseEnd_3340669 := by
    simpa [prefixWord, tailWord_3340669, baseEnd_3340669] using wordTrace_append hprefix tailTrace_3340669
  have hstable : (prefixWord ++ tailWord_3340669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3340669).length < 2 ^ (prefixWord ++ tailWord_3340669).sum := by decide
  have hdescent : baseEnd_3340669 < baseStart_3340669 := by decide
  rcases family_descends (prefixWord ++ tailWord_3340669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3340709 : List Nat := [1, 3, 1, 2, 1, 1, 5, 1, 3, 3, 2]
def baseStart_3340709 : Nat := 118140960795 + 3340709 * 2 ^ 59
def prefixEnd_3340709 : Nat := 4983230072969 + 3 ^ 40 * 3340709 * 2
def baseEnd_3340709 : Nat := 1715389443801075194373865

theorem tailTrace_3340709 : CollatzResearch.WordTrace tailWord_3340709 prefixEnd_3340709 1715389443801075194373865 := by
  unfold tailWord_3340709
  simp only [CollatzResearch.WordTrace]
  refine ⟨121845667254189315518689181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81230444836126210345792787 121845667254189315518689181)
  ·
    refine ⟨45692125220320993319508443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121845667254189315518689181 45692125220320993319508443)
    ·
      refine ⟨68538187830481489979262665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45692125220320993319508443 68538187830481489979262665)
      ·
        refine ⟨51403640872861117484446999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68538187830481489979262665 51403640872861117484446999)
        ·
          refine ⟨77105461309291676226670499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51403640872861117484446999 77105461309291676226670499)
          ·
            refine ⟨115658191963937514340005749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77105461309291676226670499 115658191963937514340005749)
            ·
              refine ⟨10842955496619141969375539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 115658191963937514340005749 10842955496619141969375539)
              ·
                refine ⟨16264433244928712954063309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10842955496619141969375539 16264433244928712954063309)
                ·
                  refine ⟨6099162466848267357773741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16264433244928712954063309 6099162466848267357773741)
                  ·
                    refine ⟨2287185925068100259165153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6099162466848267357773741 2287185925068100259165153)
                    ·
                      refine ⟨1715389443801075194373865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2287185925068100259165153 1715389443801075194373865)
                      ·
                        rfl

theorem cell23_3340709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 5, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 5, 1, 3, 3, 2].length) (baseStart_3340709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3340709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3340709 prefixEnd_3340709 := by exact prefixLift 3340709
  have htrace : WordTrace (prefixWord ++ tailWord_3340709) baseStart_3340709 baseEnd_3340709 := by
    simpa [prefixWord, tailWord_3340709, baseEnd_3340709] using wordTrace_append hprefix tailTrace_3340709
  have hstable : (prefixWord ++ tailWord_3340709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3340709).length < 2 ^ (prefixWord ++ tailWord_3340709).sum := by decide
  have hdescent : baseEnd_3340709 < baseStart_3340709 := by decide
  rcases family_descends (prefixWord ++ tailWord_3340709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3340735 : List Nat := [1, 1, 2, 2, 2, 1, 1, 1, 1, 5, 6]
def baseStart_3340735 : Nat := 118140960795 + 3340735 * 2 ^ 59
def prefixEnd_3340735 : Nat := 4983230072969 + 3 ^ 40 * 3340735 * 2
def baseEnd_3340735 : Nat := 1715402794298092092648745

theorem tailTrace_3340735 : CollatzResearch.WordTrace tailWord_3340735 prefixEnd_3340735 1715402794298092092648745 := by
  unfold tailWord_3340735
  simp only [CollatzResearch.WordTrace]
  refine ⟨121846615552095121959135659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81231077034730081306090439 121846615552095121959135659)
  ·
    refine ⟨182769923328142682938703489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121846615552095121959135659 182769923328142682938703489)
    ·
      refine ⟨137077442496107012204027617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182769923328142682938703489 137077442496107012204027617)
      ·
        refine ⟨102808081872080259153020713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137077442496107012204027617 102808081872080259153020713)
        ·
          refine ⟨77106061404060194364765535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102808081872080259153020713 77106061404060194364765535)
          ·
            refine ⟨115659092106090291547148303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77106061404060194364765535 115659092106090291547148303)
            ·
              refine ⟨173488638159135437320722455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115659092106090291547148303 173488638159135437320722455)
              ·
                refine ⟨260232957238703155981083683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 173488638159135437320722455 260232957238703155981083683)
                ·
                  refine ⟨390349435858054733971625525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 260232957238703155981083683 390349435858054733971625525)
                  ·
                    refine ⟨36595259611692631309839893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 390349435858054733971625525 36595259611692631309839893)
                    ·
                      refine ⟨1715402794298092092648745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 36595259611692631309839893 1715402794298092092648745)
                      ·
                        rfl

theorem cell23_3340735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 5, 6].length) (baseStart_3340735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3340735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3340735 prefixEnd_3340735 := by exact prefixLift 3340735
  have htrace : WordTrace (prefixWord ++ tailWord_3340735) baseStart_3340735 baseEnd_3340735 := by
    simpa [prefixWord, tailWord_3340735, baseEnd_3340735] using wordTrace_append hprefix tailTrace_3340735
  have hstable : (prefixWord ++ tailWord_3340735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3340735).length < 2 ^ (prefixWord ++ tailWord_3340735).sum := by decide
  have hdescent : baseEnd_3340735 < baseStart_3340735 := by decide
  rcases family_descends (prefixWord ++ tailWord_3340735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3340755 : List Nat := [1, 1, 1, 2, 1, 1, 1, 1, 5, 2, 7]
def baseStart_3340755 : Nat := 118140960795 + 3340755 * 2 ^ 59
def prefixEnd_3340755 : Nat := 4983230072969 + 3 ^ 40 * 3340755 * 2
def baseEnd_3340755 : Nat := 1715413063911182014398653

theorem tailTrace_3340755 : CollatzResearch.WordTrace tailWord_3340755 prefixEnd_3340755 1715413063911182014398653 := by
  unfold tailWord_3340755
  simp only [CollatzResearch.WordTrace]
  refine ⟨121847345012022665374863719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81231563341348443583242479 121847345012022665374863719)
  ·
    refine ⟨182771017518033998062295579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121847345012022665374863719 182771017518033998062295579)
    ·
      refine ⟨274156526277050997093443369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182771017518033998062295579 274156526277050997093443369)
      ·
        refine ⟨205617394707788247820082527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 274156526277050997093443369 205617394707788247820082527)
        ·
          refine ⟨308426092061682371730123791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 205617394707788247820082527 308426092061682371730123791)
          ·
            refine ⟨462639138092523557595185687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 308426092061682371730123791 462639138092523557595185687)
            ·
              refine ⟨693958707138785336392778531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 462639138092523557595185687 693958707138785336392778531)
              ·
                refine ⟨1040938060708178004589167797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 693958707138785336392778531 1040938060708178004589167797)
                ·
                  refine ⟨97587943191391687930234481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1040938060708178004589167797 97587943191391687930234481)
                  ·
                    refine ⟨73190957393543765947675861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 97587943191391687930234481 73190957393543765947675861)
                    ·
                      refine ⟨1715413063911182014398653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 73190957393543765947675861 1715413063911182014398653)
                      ·
                        rfl

theorem cell23_3340755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 5, 2, 7].length) (baseStart_3340755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3340755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3340755 prefixEnd_3340755 := by exact prefixLift 3340755
  have htrace : WordTrace (prefixWord ++ tailWord_3340755) baseStart_3340755 baseEnd_3340755 := by
    simpa [prefixWord, tailWord_3340755, baseEnd_3340755] using wordTrace_append hprefix tailTrace_3340755
  have hstable : (prefixWord ++ tailWord_3340755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3340755).length < 2 ^ (prefixWord ++ tailWord_3340755).sum := by decide
  have hdescent : baseEnd_3340755 < baseStart_3340755 := by decide
  rcases family_descends (prefixWord ++ tailWord_3340755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3340756 : List Nat := [2, 4, 1, 2, 2, 1, 1, 3, 1, 4, 2]
def baseStart_3340756 : Nat := 118140960795 + 3340756 * 2 ^ 59
def prefixEnd_3340756 : Nat := 4983230072969 + 3 ^ 40 * 3340756 * 2
def baseEnd_3340756 : Nat := 1715413577391836510486149

theorem tailTrace_3340756 : CollatzResearch.WordTrace tailWord_3340756 prefixEnd_3340756 1715413577391836510486149 := by
  unfold tailWord_3340756
  simp only [CollatzResearch.WordTrace]
  refine ⟨60923690742509521272825061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81231587656679361697100081 60923690742509521272825061)
  ·
    refine ⟨11423192014220535238654699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60923690742509521272825061 11423192014220535238654699)
    ·
      refine ⟨17134788021330802857982049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11423192014220535238654699 17134788021330802857982049)
      ·
        refine ⟨12851091015998102143486537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17134788021330802857982049 12851091015998102143486537)
        ·
          refine ⟨9638318261998576607614903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12851091015998102143486537 9638318261998576607614903)
          ·
            refine ⟨14457477392997864911422355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9638318261998576607614903 14457477392997864911422355)
            ·
              refine ⟨21686216089496797367133533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14457477392997864911422355 21686216089496797367133533)
              ·
                refine ⟨8132331033561299012675075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21686216089496797367133533 8132331033561299012675075)
                ·
                  refine ⟨12198496550341948519012613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8132331033561299012675075 12198496550341948519012613)
                  ·
                    refine ⟨2287218103189115347314865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12198496550341948519012613 2287218103189115347314865)
                    ·
                      refine ⟨1715413577391836510486149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2287218103189115347314865 1715413577391836510486149)
                      ·
                        rfl

theorem cell23_3340756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 3, 1, 4, 2].length) (baseStart_3340756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3340756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3340756 prefixEnd_3340756 := by exact prefixLift 3340756
  have htrace : WordTrace (prefixWord ++ tailWord_3340756) baseStart_3340756 baseEnd_3340756 := by
    simpa [prefixWord, tailWord_3340756, baseEnd_3340756] using wordTrace_append hprefix tailTrace_3340756
  have hstable : (prefixWord ++ tailWord_3340756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3340756).length < 2 ^ (prefixWord ++ tailWord_3340756).sum := by decide
  have hdescent : baseEnd_3340756 < baseStart_3340756 := by decide
  rcases family_descends (prefixWord ++ tailWord_3340756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3340762 : List Nat := [3, 1, 1, 2, 3, 1, 3, 2, 7]
def baseStart_3340762 : Nat := 118140960795 + 3340762 * 2 ^ 59
def prefixEnd_3340762 : Nat := 4983230072969 + 3 ^ 40 * 3340762 * 2
def baseEnd_3340762 : Nat := 190601850919529276334569

theorem tailTrace_3340762 : CollatzResearch.WordTrace tailWord_3340762 prefixEnd_3340762 190601850919529276334569 := by
  unfold tailWord_3340762
  simp only [CollatzResearch.WordTrace]
  refine ⟨30461900080749326392592135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81231733548664870380245693 30461900080749326392592135)
  ·
    refine ⟨45692850121123989588888203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30461900080749326392592135 45692850121123989588888203)
    ·
      refine ⟨68539275181685984383332305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45692850121123989588888203 68539275181685984383332305)
      ·
        refine ⟨51404456386264488287499229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68539275181685984383332305 51404456386264488287499229)
        ·
          refine ⟨19276671144849183107812211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51404456386264488287499229 19276671144849183107812211)
          ·
            refine ⟨28915006717273774661718317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19276671144849183107812211 28915006717273774661718317)
            ·
              refine ⟨10843127518977665498144369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28915006717273774661718317 10843127518977665498144369)
              ·
                refine ⟨8132345639233249123608277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10843127518977665498144369 8132345639233249123608277)
                ·
                  refine ⟨190601850919529276334569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8132345639233249123608277 190601850919529276334569)
                  ·
                    rfl

theorem cell23_3340762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 3, 2, 7].length) (baseStart_3340762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3340762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3340762 prefixEnd_3340762 := by exact prefixLift 3340762
  have htrace : WordTrace (prefixWord ++ tailWord_3340762) baseStart_3340762 baseEnd_3340762 := by
    simpa [prefixWord, tailWord_3340762, baseEnd_3340762] using wordTrace_append hprefix tailTrace_3340762
  have hstable : (prefixWord ++ tailWord_3340762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3340762).length < 2 ^ (prefixWord ++ tailWord_3340762).sum := by decide
  have hdescent : baseEnd_3340762 < baseStart_3340762 := by decide
  rcases family_descends (prefixWord ++ tailWord_3340762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3340779 : List Nat := [1, 1, 1, 1, 2, 3, 6, 3, 5]
def baseStart_3340779 : Nat := 118140960795 + 3340779 * 2 ^ 59
def prefixEnd_3340779 : Nat := 4983230072969 + 3 ^ 40 * 3340779 * 2
def baseEnd_3340779 : Nat := 190602820827432213388727

theorem tailTrace_3340779 : CollatzResearch.WordTrace tailWord_3340779 prefixEnd_3340779 190602820827432213388727 := by
  unfold tailWord_3340779
  simp only [CollatzResearch.WordTrace]
  refine ⟨121848220363935717473737391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81232146909290478315824927 121848220363935717473737391)
  ·
    refine ⟨182772330545903576210606087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121848220363935717473737391 182772330545903576210606087)
    ·
      refine ⟨274158495818855364315909131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182772330545903576210606087 274158495818855364315909131)
      ·
        refine ⟨411237743728283046473863697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 274158495818855364315909131 411237743728283046473863697)
        ·
          refine ⟨308428307796212284855397773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 411237743728283046473863697 308428307796212284855397773)
          ·
            refine ⟨115660615423579606820774165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 308428307796212284855397773 115660615423579606820774165)
            ·
              refine ⟨5421591347980294069723789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 115660615423579606820774165 5421591347980294069723789)
              ·
                refine ⟨2033096755492610276146421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5421591347980294069723789 2033096755492610276146421)
                ·
                  refine ⟨190602820827432213388727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2033096755492610276146421 190602820827432213388727)
                  ·
                    rfl

theorem cell23_3340779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 6, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 6, 3, 5].length) (baseStart_3340779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3340779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3340779 prefixEnd_3340779 := by exact prefixLift 3340779
  have htrace : WordTrace (prefixWord ++ tailWord_3340779) baseStart_3340779 baseEnd_3340779 := by
    simpa [prefixWord, tailWord_3340779, baseEnd_3340779] using wordTrace_append hprefix tailTrace_3340779
  have hstable : (prefixWord ++ tailWord_3340779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3340779).length < 2 ^ (prefixWord ++ tailWord_3340779).sum := by decide
  have hdescent : baseEnd_3340779 < baseStart_3340779 := by decide
  rcases family_descends (prefixWord ++ tailWord_3340779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3340792 : List Nat := [2, 1, 2, 1, 1, 4, 2, 1, 4, 5]
def baseStart_3340792 : Nat := 118140960795 + 3340792 * 2 ^ 59
def prefixEnd_3340792 : Nat := 4983230072969 + 3 ^ 40 * 3340792 * 2
def baseEnd_3340792 : Nat := 571810687565132789878661

theorem tailTrace_3340792 : CollatzResearch.WordTrace tailWord_3340792 prefixEnd_3340792 571810687565132789878661 := by
  unfold tailWord_3340792
  simp only [CollatzResearch.WordTrace]
  refine ⟨60924347256444310346980315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81232463008592413795973753 60924347256444310346980315)
  ·
    refine ⟨91386520884666465520470473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60924347256444310346980315 91386520884666465520470473)
    ·
      refine ⟨68539890663499849140352855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91386520884666465520470473 68539890663499849140352855)
      ·
        refine ⟨102809835995249773710529283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68539890663499849140352855 102809835995249773710529283)
        ·
          refine ⟨154214753992874660565793925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102809835995249773710529283 154214753992874660565793925)
          ·
            refine ⟨28915266373663998856086361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 154214753992874660565793925 28915266373663998856086361)
            ·
              refine ⟨21686449780247999142064771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28915266373663998856086361 21686449780247999142064771)
              ·
                refine ⟨32529674670371998713097157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21686449780247999142064771 32529674670371998713097157)
                ·
                  refine ⟨6099314000694749758705717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32529674670371998713097157 6099314000694749758705717)
                  ·
                    refine ⟨571810687565132789878661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6099314000694749758705717 571810687565132789878661)
                    ·
                      rfl

theorem cell23_3340792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 1, 4, 5].length) (baseStart_3340792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3340792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3340792 prefixEnd_3340792 := by exact prefixLift 3340792
  have htrace : WordTrace (prefixWord ++ tailWord_3340792) baseStart_3340792 baseEnd_3340792 := by
    simpa [prefixWord, tailWord_3340792, baseEnd_3340792] using wordTrace_append hprefix tailTrace_3340792
  have hstable : (prefixWord ++ tailWord_3340792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3340792).length < 2 ^ (prefixWord ++ tailWord_3340792).sum := by decide
  have hdescent : baseEnd_3340792 < baseStart_3340792 := by decide
  rcases family_descends (prefixWord ++ tailWord_3340792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3340829 : List Nat := [1, 4, 2, 2, 1, 2, 2, 1, 1, 3, 4]
def baseStart_3340829 : Nat := 118140960795 + 3340829 * 2 ^ 59
def prefixEnd_3340829 : Nat := 4983230072969 + 3 ^ 40 * 3340829 * 2
def baseEnd_3340829 : Nat := 1715451061479614724873313

theorem tailTrace_3340829 : CollatzResearch.WordTrace tailWord_3340829 prefixEnd_3340829 1715451061479614724873313 := by
  unfold tailWord_3340829
  simp only [CollatzResearch.WordTrace]
  refine ⟨121850044013754576013057541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81233362675836384008705027 121850044013754576013057541)
  ·
    refine ⟨22846883252578983002448289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 121850044013754576013057541 22846883252578983002448289)
    ·
      refine ⟨17135162439434237251836217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22846883252578983002448289 17135162439434237251836217)
      ·
        refine ⟨12851371829575677938877163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17135162439434237251836217 12851371829575677938877163)
        ·
          refine ⟨19277057744363516908315745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12851371829575677938877163 19277057744363516908315745)
          ·
            refine ⟨14457793308272637681236809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19277057744363516908315745 14457793308272637681236809)
            ·
              refine ⟨10843344981204478260927607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14457793308272637681236809 10843344981204478260927607)
              ·
                refine ⟨16265017471806717391391411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10843344981204478260927607 16265017471806717391391411)
                ·
                  refine ⟨24397526207710076087087117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16265017471806717391391411 24397526207710076087087117)
                  ·
                    refine ⟨9149072327891278532657669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24397526207710076087087117 9149072327891278532657669)
                    ·
                      refine ⟨1715451061479614724873313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9149072327891278532657669 1715451061479614724873313)
                      ·
                        rfl

theorem cell23_3340829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 2, 1, 1, 3, 4].length) (baseStart_3340829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3340829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3340829 prefixEnd_3340829 := by exact prefixLift 3340829
  have htrace : WordTrace (prefixWord ++ tailWord_3340829) baseStart_3340829 baseEnd_3340829 := by
    simpa [prefixWord, tailWord_3340829, baseEnd_3340829] using wordTrace_append hprefix tailTrace_3340829
  have hstable : (prefixWord ++ tailWord_3340829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3340829).length < 2 ^ (prefixWord ++ tailWord_3340829).sum := by decide
  have hdescent : baseEnd_3340829 < baseStart_3340829 := by decide
  rcases family_descends (prefixWord ++ tailWord_3340829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3340849 : List Nat := [1, 2, 2, 3, 1, 1, 3, 1, 4, 2, 3]
def baseStart_3340849 : Nat := 118140960795 + 3340849 * 2 ^ 59
def prefixEnd_3340849 : Nat := 4983230072969 + 3 ^ 40 * 3340849 * 2
def baseEnd_3340849 : Nat := 1715461331092704646623221

theorem tailTrace_3340849 : CollatzResearch.WordTrace tailWord_3340849 prefixEnd_3340849 1715461331092704646623221 := by
  unfold tailWord_3340849
  simp only [CollatzResearch.WordTrace]
  refine ⟨121850773473682119428785601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81233848982454746285857067 121850773473682119428785601)
  ·
    refine ⟨91388080105261589571589201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121850773473682119428785601 91388080105261589571589201)
    ·
      refine ⟨68541060078946192178691901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91388080105261589571589201 68541060078946192178691901)
      ·
        refine ⟨25702897529604822067009463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68541060078946192178691901 25702897529604822067009463)
        ·
          refine ⟨38554346294407233100514195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25702897529604822067009463 38554346294407233100514195)
          ·
            refine ⟨57831519441610849650771293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38554346294407233100514195 57831519441610849650771293)
            ·
              refine ⟨21686819790604068619039235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57831519441610849650771293 21686819790604068619039235)
              ·
                refine ⟨32530229685906102928558853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21686819790604068619039235 32530229685906102928558853)
                ·
                  refine ⟨6099418066107394299104785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32530229685906102928558853 6099418066107394299104785)
                  ·
                    refine ⟨4574563549580545724328589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6099418066107394299104785 4574563549580545724328589)
                    ·
                      refine ⟨1715461331092704646623221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4574563549580545724328589 1715461331092704646623221)
                      ·
                        rfl

theorem cell23_3340849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 1, 4, 2, 3].length) (baseStart_3340849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3340849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3340849 prefixEnd_3340849 := by exact prefixLift 3340849
  have htrace : WordTrace (prefixWord ++ tailWord_3340849) baseStart_3340849 baseEnd_3340849 := by
    simpa [prefixWord, tailWord_3340849, baseEnd_3340849] using wordTrace_append hprefix tailTrace_3340849
  have hstable : (prefixWord ++ tailWord_3340849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3340849).length < 2 ^ (prefixWord ++ tailWord_3340849).sum := by decide
  have hdescent : baseEnd_3340849 < baseStart_3340849 := by decide
  rcases family_descends (prefixWord ++ tailWord_3340849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3340869 : List Nat := [1, 3, 1, 1, 1, 6, 1, 3, 6]
def baseStart_3340869 : Nat := 118140960795 + 3340869 * 2 ^ 59
def prefixEnd_3340869 : Nat := 4983230072969 + 3 ^ 40 * 3340869 * 2
def baseEnd_3340869 : Nat := 190607955633977174263681

theorem tailTrace_3340869 : CollatzResearch.WordTrace tailWord_3340869 prefixEnd_3340869 190607955633977174263681 := by
  unfold tailWord_3340869
  simp only [CollatzResearch.WordTrace]
  refine ⟨121851502933609662844513661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81234335289073108563009107 121851502933609662844513661)
  ·
    refine ⟨45694313600103623566692623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121851502933609662844513661 45694313600103623566692623)
    ·
      refine ⟨68541470400155435350038935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45694313600103623566692623 68541470400155435350038935)
      ·
        refine ⟨102812205600233153025058403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68541470400155435350038935 102812205600233153025058403)
        ·
          refine ⟨154218308400349729537587605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102812205600233153025058403 154218308400349729537587605)
          ·
            refine ⟨7228983206266393572074419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 154218308400349729537587605 7228983206266393572074419)
            ·
              refine ⟨10843474809399590358111629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7228983206266393572074419 10843474809399590358111629)
              ·
                refine ⟨4066303053524846384291861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10843474809399590358111629 4066303053524846384291861)
                ·
                  refine ⟨190607955633977174263681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4066303053524846384291861 190607955633977174263681)
                  ·
                    rfl

theorem cell23_3340869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 1, 3, 6].length) (baseStart_3340869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3340869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3340869 prefixEnd_3340869 := by exact prefixLift 3340869
  have htrace : WordTrace (prefixWord ++ tailWord_3340869) baseStart_3340869 baseEnd_3340869 := by
    simpa [prefixWord, tailWord_3340869, baseEnd_3340869] using wordTrace_append hprefix tailTrace_3340869
  have hstable : (prefixWord ++ tailWord_3340869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3340869).length < 2 ^ (prefixWord ++ tailWord_3340869).sum := by decide
  have hdescent : baseEnd_3340869 < baseStart_3340869 := by decide
  rcases family_descends (prefixWord ++ tailWord_3340869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3340872 : List Nat := [2, 1, 3, 1, 1, 1, 1, 4, 1, 2, 6]
def baseStart_3340872 : Nat := 118140960795 + 3340872 * 2 ^ 59
def prefixEnd_3340872 : Nat := 4983230072969 + 3 ^ 40 * 3340872 * 2
def baseEnd_3340872 : Nat := 1715473141147758056635615

theorem tailTrace_3340872 : CollatzResearch.WordTrace tailWord_3340872 prefixEnd_3340872 1715473141147758056635615 := by
  unfold tailWord_3340872
  simp only [CollatzResearch.WordTrace]
  refine ⟨60925806176299397178436435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81234408235065862904581913 60925806176299397178436435)
  ·
    refine ⟨91388709264449095767654653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60925806176299397178436435 91388709264449095767654653)
    ·
      refine ⟨34270765974168410912870495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91388709264449095767654653 34270765974168410912870495)
      ·
        refine ⟨51406148961252616369305743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34270765974168410912870495 51406148961252616369305743)
        ·
          refine ⟨77109223441878924553958615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51406148961252616369305743 77109223441878924553958615)
          ·
            refine ⟨115663835162818386830937923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77109223441878924553958615 115663835162818386830937923)
            ·
              refine ⟨173495752744227580246406885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115663835162818386830937923 173495752744227580246406885)
              ·
                refine ⟨32530453639542671296201291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 173495752744227580246406885 32530453639542671296201291)
                ·
                  refine ⟨48795680459314006944301937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32530453639542671296201291 48795680459314006944301937)
                  ·
                    refine ⟨36596760344485505208226453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 48795680459314006944301937 36596760344485505208226453)
                    ·
                      refine ⟨1715473141147758056635615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 36596760344485505208226453 1715473141147758056635615)
                      ·
                        rfl

theorem cell23_3340872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 4, 1, 2, 6].length) (baseStart_3340872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3340872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3340872 prefixEnd_3340872 := by exact prefixLift 3340872
  have htrace : WordTrace (prefixWord ++ tailWord_3340872) baseStart_3340872 baseEnd_3340872 := by
    simpa [prefixWord, tailWord_3340872, baseEnd_3340872] using wordTrace_append hprefix tailTrace_3340872
  have hstable : (prefixWord ++ tailWord_3340872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3340872).length < 2 ^ (prefixWord ++ tailWord_3340872).sum := by decide
  have hdescent : baseEnd_3340872 < baseStart_3340872 := by decide
  rcases family_descends (prefixWord ++ tailWord_3340872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3340919 : List Nat := [1, 1, 3, 1, 1, 3, 3, 2, 3, 1, 4]
def baseStart_3340919 : Nat := 118140960795 + 3340919 * 2 ^ 59
def prefixEnd_3340919 : Nat := 4983230072969 + 3 ^ 40 * 3340919 * 2
def baseEnd_3340919 : Nat := 1715497274738519372747899

theorem tailTrace_3340919 : CollatzResearch.WordTrace tailWord_3340919 prefixEnd_3340919 1715497274738519372747899 := by
  unfold tailWord_3340919
  simp only [CollatzResearch.WordTrace]
  refine ⟨121853326583428521383833811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81235551055619014255889207 121853326583428521383833811)
  ·
    refine ⟨182779989875142782075750717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121853326583428521383833811 182779989875142782075750717)
    ·
      refine ⟨68542496203178543278406519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 182779989875142782075750717 68542496203178543278406519)
      ·
        refine ⟨102813744304767814917609779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68542496203178543278406519 102813744304767814917609779)
        ·
          refine ⟨154220616457151722376414669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102813744304767814917609779 154220616457151722376414669)
          ·
            refine ⟨57832731171431895891155501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 154220616457151722376414669 57832731171431895891155501)
            ·
              refine ⟨21687274189286960959183313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57832731171431895891155501 21687274189286960959183313)
              ·
                refine ⟨16265455641965220719387485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21687274189286960959183313 16265455641965220719387485)
                ·
                  refine ⟨6099545865736957769770307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16265455641965220719387485 6099545865736957769770307)
                  ·
                    refine ⟨9149318798605436654655461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6099545865736957769770307 9149318798605436654655461)
                    ·
                      refine ⟨1715497274738519372747899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9149318798605436654655461 1715497274738519372747899)
                      ·
                        rfl

theorem cell23_3340919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 2, 3, 1, 4].length) (baseStart_3340919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3340919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3340919 prefixEnd_3340919 := by exact prefixLift 3340919
  have htrace : WordTrace (prefixWord ++ tailWord_3340919) baseStart_3340919 baseEnd_3340919 := by
    simpa [prefixWord, tailWord_3340919, baseEnd_3340919] using wordTrace_append hprefix tailTrace_3340919
  have hstable : (prefixWord ++ tailWord_3340919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3340919).length < 2 ^ (prefixWord ++ tailWord_3340919).sum := by decide
  have hdescent : baseEnd_3340919 < baseStart_3340919 := by decide
  rcases family_descends (prefixWord ++ tailWord_3340919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3340946 : List Nat := [3, 2, 3, 1, 2, 1, 2, 2, 1, 6]
def baseStart_3340946 : Nat := 118140960795 + 3340946 * 2 ^ 59
def prefixEnd_3340946 : Nat := 4983230072969 + 3 ^ 40 * 3340946 * 2
def baseEnd_3340946 : Nat := 571837046238730255703425

theorem tailTrace_3340946 : CollatzResearch.WordTrace tailWord_3340946 prefixEnd_3340946 571837046238730255703425 := by
  unfold tailWord_3340946
  simp only [CollatzResearch.WordTrace]
  refine ⟨30463577838582676248766673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81236207569553803330044461 30463577838582676248766673)
  ·
    refine ⟨22847683378937007186575005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30463577838582676248766673 22847683378937007186575005)
    ·
      refine ⟨8567881267101377694965627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22847683378937007186575005 8567881267101377694965627)
      ·
        refine ⟨12851821900652066542448441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8567881267101377694965627 12851821900652066542448441)
        ·
          refine ⟨9638866425489049906836331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12851821900652066542448441 9638866425489049906836331)
          ·
            refine ⟨14458299638233574860254497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9638866425489049906836331 14458299638233574860254497)
            ·
              refine ⟨10843724728675181145190873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14458299638233574860254497 10843724728675181145190873)
              ·
                refine ⟨8132793546506385858893155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10843724728675181145190873 8132793546506385858893155)
                ·
                  refine ⟨12199190319759578788339733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8132793546506385858893155 12199190319759578788339733)
                  ·
                    refine ⟨571837046238730255703425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12199190319759578788339733 571837046238730255703425)
                    ·
                      rfl

theorem cell23_3340946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 2, 2, 1, 6].length) (baseStart_3340946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3340946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3340946 prefixEnd_3340946 := by exact prefixLift 3340946
  have htrace : WordTrace (prefixWord ++ tailWord_3340946) baseStart_3340946 baseEnd_3340946 := by
    simpa [prefixWord, tailWord_3340946, baseEnd_3340946] using wordTrace_append hprefix tailTrace_3340946
  have hstable : (prefixWord ++ tailWord_3340946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3340946).length < 2 ^ (prefixWord ++ tailWord_3340946).sum := by decide
  have hdescent : baseEnd_3340946 < baseStart_3340946 := by decide
  rcases family_descends (prefixWord ++ tailWord_3340946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3340969 : List Nat := [1, 2, 1, 1, 1, 1, 2, 3, 5, 3, 3]
def baseStart_3340969 : Nat := 118140960795 + 3340969 * 2 ^ 59
def prefixEnd_3340969 : Nat := 4983230072969 + 3 ^ 40 * 3340969 * 2
def baseEnd_3340969 : Nat := 1715522948771244177122669

theorem tailTrace_3340969 : CollatzResearch.WordTrace tailWord_3340969 prefixEnd_3340969 1715522948771244177122669 := by
  unfold tailWord_3340969
  simp only [CollatzResearch.WordTrace]
  refine ⟨121855150233247379923153961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81236766822164919948769307 121855150233247379923153961)
  ·
    refine ⟨91391362674935534942365471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121855150233247379923153961 91391362674935534942365471)
    ·
      refine ⟨137087044012403302413548207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91391362674935534942365471 137087044012403302413548207)
      ·
        refine ⟨205630566018604953620322311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137087044012403302413548207 205630566018604953620322311)
        ·
          refine ⟨308445849027907430430483467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 205630566018604953620322311 308445849027907430430483467)
          ·
            refine ⟨462668773541861145645725201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 308445849027907430430483467 462668773541861145645725201)
            ·
              refine ⟨347001580156395859234293901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 462668773541861145645725201 347001580156395859234293901)
              ·
                refine ⟨130125592558648447212860213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 347001580156395859234293901 130125592558648447212860213)
                ·
                  refine ⟨12199274302373291926205645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 130125592558648447212860213 12199274302373291926205645)
                  ·
                    refine ⟨4574727863389984472327117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12199274302373291926205645 4574727863389984472327117)
                    ·
                      refine ⟨1715522948771244177122669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4574727863389984472327117 1715522948771244177122669)
                      ·
                        rfl

theorem cell23_3340969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 3, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 3, 5, 3, 3].length) (baseStart_3340969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3340969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3340969 prefixEnd_3340969 := by exact prefixLift 3340969
  have htrace : WordTrace (prefixWord ++ tailWord_3340969) baseStart_3340969 baseEnd_3340969 := by
    simpa [prefixWord, tailWord_3340969, baseEnd_3340969] using wordTrace_append hprefix tailTrace_3340969
  have hstable : (prefixWord ++ tailWord_3340969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3340969).length < 2 ^ (prefixWord ++ tailWord_3340969).sum := by decide
  have hdescent : baseEnd_3340969 < baseStart_3340969 := by decide
  rcases family_descends (prefixWord ++ tailWord_3340969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3340983 : List Nat := [1, 1, 3, 1, 6, 2, 1, 1, 1, 2, 4]
def baseStart_3340983 : Nat := 118140960795 + 3340983 * 2 ^ 59
def prefixEnd_3340983 : Nat := 4983230072969 + 3 ^ 40 * 3340983 * 2
def baseEnd_3340983 : Nat := 1715530137500407122347605

theorem tailTrace_3340983 : CollatzResearch.WordTrace tailWord_3340983 prefixEnd_3340983 1715530137500407122347605 := by
  unfold tailWord_3340983
  simp only [CollatzResearch.WordTrace]
  refine ⟨121855660855196660314163603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81237107236797773542775735 121855660855196660314163603)
  ·
    refine ⟨182783491282794990471245405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121855660855196660314163603 182783491282794990471245405)
    ·
      refine ⟨68543809231048121426717027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 182783491282794990471245405 68543809231048121426717027)
      ·
        refine ⟨102815713846572182140075541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68543809231048121426717027 102815713846572182140075541)
        ·
          refine ⟨4819486586558071037816041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 102815713846572182140075541 4819486586558071037816041)
          ·
            refine ⟨3614614939918553278362031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4819486586558071037816041 3614614939918553278362031)
            ·
              refine ⟨5421922409877829917543047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3614614939918553278362031 5421922409877829917543047)
              ·
                refine ⟨8132883614816744876314571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5421922409877829917543047 8132883614816744876314571)
                ·
                  refine ⟨12199325422225117314471857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8132883614816744876314571 12199325422225117314471857)
                  ·
                    refine ⟨9149494066668837985853893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12199325422225117314471857 9149494066668837985853893)
                    ·
                      refine ⟨1715530137500407122347605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9149494066668837985853893 1715530137500407122347605)
                      ·
                        rfl

theorem cell23_3340983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 2, 1, 1, 1, 2, 4].length) (baseStart_3340983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3340983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3340983 prefixEnd_3340983 := by exact prefixLift 3340983
  have htrace : WordTrace (prefixWord ++ tailWord_3340983) baseStart_3340983 baseEnd_3340983 := by
    simpa [prefixWord, tailWord_3340983, baseEnd_3340983] using wordTrace_append hprefix tailTrace_3340983
  have hstable : (prefixWord ++ tailWord_3340983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3340983).length < 2 ^ (prefixWord ++ tailWord_3340983).sum := by decide
  have hdescent : baseEnd_3340983 < baseStart_3340983 := by decide
  rcases family_descends (prefixWord ++ tailWord_3340983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3340993 : List Nat := [1, 2, 6, 2, 1, 1, 1, 9]
def baseStart_3340993 : Nat := 118140960795 + 3340993 * 2 ^ 59
def prefixEnd_3340993 : Nat := 4983230072969 + 3 ^ 40 * 3340993 * 2
def baseEnd_3340993 : Nat := 63538343418776003082317

theorem tailTrace_3340993 : CollatzResearch.WordTrace tailWord_3340993 prefixEnd_3340993 63538343418776003082317 := by
  unfold tailWord_3340993
  simp only [CollatzResearch.WordTrace]
  refine ⟨121856025585160432022027633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81237350390106954681351755 121856025585160432022027633)
  ·
    refine ⟨91392019188870324016520725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121856025585160432022027633 91392019188870324016520725)
    ·
      refine ⟨4284000899478296438274409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 91392019188870324016520725 4284000899478296438274409)
      ·
        refine ⟨3213000674608722328705807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4284000899478296438274409 3213000674608722328705807)
        ·
          refine ⟨4819501011913083493058711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3213000674608722328705807 4819501011913083493058711)
          ·
            refine ⟨7229251517869625239588067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4819501011913083493058711 7229251517869625239588067)
            ·
              refine ⟨10843877276804437859382101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7229251517869625239588067 10843877276804437859382101)
              ·
                refine ⟨63538343418776003082317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 10843877276804437859382101 63538343418776003082317)
                ·
                  rfl

theorem cell23_3340993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 1, 9].length) (baseStart_3340993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3340993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3340993 prefixEnd_3340993 := by exact prefixLift 3340993
  have htrace : WordTrace (prefixWord ++ tailWord_3340993) baseStart_3340993 baseEnd_3340993 := by
    simpa [prefixWord, tailWord_3340993, baseEnd_3340993] using wordTrace_append hprefix tailTrace_3340993
  have hstable : (prefixWord ++ tailWord_3340993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3340993).length < 2 ^ (prefixWord ++ tailWord_3340993).sum := by decide
  have hdescent : baseEnd_3340993 < baseStart_3340993 := by decide
  rcases family_descends (prefixWord ++ tailWord_3340993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3340998 : List Nat := [6, 1, 2, 1, 3, 1, 1, 3, 1, 1, 3]
def baseStart_3340998 : Nat := 118140960795 + 3340998 * 2 ^ 59
def prefixEnd_3340998 : Nat := 4983230072969 + 3 ^ 40 * 3340998 * 2
def baseEnd_3340998 : Nat := 1715537839710224563660037

theorem tailTrace_3340998 : CollatzResearch.WordTrace tailWord_3340998 prefixEnd_3340998 1715537839710224563660037 := by
  unfold tailWord_3340998
  simp only [CollatzResearch.WordTrace]
  refine ⟨3808006498441947433623739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 81237471966761545250639765 3808006498441947433623739)
  ·
    refine ⟨5712009747662921150435609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3808006498441947433623739 5712009747662921150435609)
    ·
      refine ⟨4284007310747190862826707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5712009747662921150435609 4284007310747190862826707)
      ·
        refine ⟨6426010966120786294240061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4284007310747190862826707 6426010966120786294240061)
        ·
          refine ⟨2409754112295294860340023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6426010966120786294240061 2409754112295294860340023)
          ·
            refine ⟨3614631168442942290510035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2409754112295294860340023 3614631168442942290510035)
            ·
              refine ⟨5421946752664413435765053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3614631168442942290510035 5421946752664413435765053)
              ·
                refine ⟨2033230032249155038411895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5421946752664413435765053 2033230032249155038411895)
                ·
                  refine ⟨3049845048373732557617843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2033230032249155038411895 3049845048373732557617843)
                  ·
                    refine ⟨4574767572560598836426765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3049845048373732557617843 4574767572560598836426765)
                    ·
                      refine ⟨1715537839710224563660037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4574767572560598836426765 1715537839710224563660037)
                      ·
                        rfl

theorem cell23_3340998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 1, 1, 3, 1, 1, 3].length) (baseStart_3340998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3340998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3340998 prefixEnd_3340998 := by exact prefixLift 3340998
  have htrace : WordTrace (prefixWord ++ tailWord_3340998) baseStart_3340998 baseEnd_3340998 := by
    simpa [prefixWord, tailWord_3340998, baseEnd_3340998] using wordTrace_append hprefix tailTrace_3340998
  have hstable : (prefixWord ++ tailWord_3340998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3340998).length < 2 ^ (prefixWord ++ tailWord_3340998).sum := by decide
  have hdescent : baseEnd_3340998 < baseStart_3340998 := by decide
  rcases family_descends (prefixWord ++ tailWord_3340998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3341004 : List Nat := [2, 2, 1, 5, 1, 3, 1, 3, 1, 2, 2]
def baseStart_3341004 : Nat := 118140960795 + 3341004 * 2 ^ 59
def prefixEnd_3341004 : Nat := 4983230072969 + 3 ^ 40 * 3341004 * 2
def baseEnd_3341004 : Nat := 1715540920594151540185009

theorem tailTrace_3341004 : CollatzResearch.WordTrace tailWord_3341004 prefixEnd_3341004 1715540920594151540185009 := by
  unfold tailWord_3341004
  simp only [CollatzResearch.WordTrace]
  refine ⟨60928213394060290450339033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81237617858747053933785377 60928213394060290450339033)
  ·
    refine ⟨45696160045545217837754275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60928213394060290450339033 45696160045545217837754275)
    ·
      refine ⟨68544240068317826756631413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45696160045545217837754275 68544240068317826756631413)
      ·
        refine ⟨6426022506404796258434195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 68544240068317826756631413 6426022506404796258434195)
        ·
          refine ⟨9639033759607194387651293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6426022506404796258434195 9639033759607194387651293)
          ·
            refine ⟨3614637659852697895369235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9639033759607194387651293 3614637659852697895369235)
            ·
              refine ⟨5421956489779046843053853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3614637659852697895369235 5421956489779046843053853)
              ·
                refine ⟨2033233683667142566145195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5421956489779046843053853 2033233683667142566145195)
                ·
                  refine ⟨3049850525500713849217793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2033233683667142566145195 3049850525500713849217793)
                  ·
                    refine ⟨2287387894125535386913345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3049850525500713849217793 2287387894125535386913345)
                    ·
                      refine ⟨1715540920594151540185009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2287387894125535386913345 1715540920594151540185009)
                      ·
                        rfl

theorem cell23_3341004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 3, 1, 3, 1, 2, 2].length) (baseStart_3341004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3341004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3341004 prefixEnd_3341004 := by exact prefixLift 3341004
  have htrace : WordTrace (prefixWord ++ tailWord_3341004) baseStart_3341004 baseEnd_3341004 := by
    simpa [prefixWord, tailWord_3341004, baseEnd_3341004] using wordTrace_append hprefix tailTrace_3341004
  have hstable : (prefixWord ++ tailWord_3341004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3341004).length < 2 ^ (prefixWord ++ tailWord_3341004).sum := by decide
  have hdescent : baseEnd_3341004 < baseStart_3341004 := by decide
  rcases family_descends (prefixWord ++ tailWord_3341004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3341020 : List Nat := [2, 2, 5, 1, 1, 1, 2, 1, 4, 1, 3]
def baseStart_3341020 : Nat := 118140960795 + 3341020 * 2 ^ 59
def prefixEnd_3341020 : Nat := 4983230072969 + 3 ^ 40 * 3341020 * 2
def baseEnd_3341020 : Nat := 1715549136284623477584935

theorem tailTrace_3341020 : CollatzResearch.WordTrace tailWord_3341020 prefixEnd_3341020 1715549136284623477584935 := by
  unfold tailWord_3341020
  simp only [CollatzResearch.WordTrace]
  refine ⟨60928505178031307816630257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81238006904041743755507009 60928505178031307816630257)
  ·
    refine ⟨45696378883523480862472693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60928505178031307816630257 45696378883523480862472693)
    ·
      refine ⟨4284035520330326330856815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 45696378883523480862472693 4284035520330326330856815)
      ·
        refine ⟨6426053280495489496285223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4284035520330326330856815 6426053280495489496285223)
        ·
          refine ⟨9639079920743234244427835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6426053280495489496285223 9639079920743234244427835)
          ·
            refine ⟨14458619881114851366641753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9639079920743234244427835 14458619881114851366641753)
            ·
              refine ⟨10843964910836138524981315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14458619881114851366641753 10843964910836138524981315)
              ·
                refine ⟨16265947366254207787471973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10843964910836138524981315 16265947366254207787471973)
                ·
                  refine ⟨3049865131172663960150995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16265947366254207787471973 3049865131172663960150995)
                  ·
                    refine ⟨4574797696758995940226493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3049865131172663960150995 4574797696758995940226493)
                    ·
                      refine ⟨1715549136284623477584935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4574797696758995940226493 1715549136284623477584935)
                      ·
                        rfl

theorem cell23_3341020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 2, 1, 4, 1, 3].length) (baseStart_3341020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3341020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3341020 prefixEnd_3341020 := by exact prefixLift 3341020
  have htrace : WordTrace (prefixWord ++ tailWord_3341020) baseStart_3341020 baseEnd_3341020 := by
    simpa [prefixWord, tailWord_3341020, baseEnd_3341020] using wordTrace_append hprefix tailTrace_3341020
  have hstable : (prefixWord ++ tailWord_3341020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3341020).length < 2 ^ (prefixWord ++ tailWord_3341020).sum := by decide
  have hdescent : baseEnd_3341020 < baseStart_3341020 := by decide
  rcases family_descends (prefixWord ++ tailWord_3341020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3341046 : List Nat := [5, 1, 1, 1, 1, 2, 1, 1, 4, 1, 5]
def baseStart_3341046 : Nat := 118140960795 + 3341046 * 2 ^ 59
def prefixEnd_3341046 : Nat := 4983230072969 + 3 ^ 40 * 3341046 * 2
def baseEnd_3341046 : Nat := 1715562486781640375859815

theorem tailTrace_3341046 : CollatzResearch.WordTrace tailWord_3341046 prefixEnd_3341046 1715562486781640375859815 := by
  unfold tailWord_3341046
  simp only [CollatzResearch.WordTrace]
  refine ⟨7616122415873026379606687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 81238639102645614715804661 7616122415873026379606687)
  ·
    refine ⟨11424183623809539569410031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7616122415873026379606687 11424183623809539569410031)
    ·
      refine ⟨17136275435714309354115047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11424183623809539569410031 17136275435714309354115047)
      ·
        refine ⟨25704413153571464031172571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17136275435714309354115047 25704413153571464031172571)
        ·
          refine ⟨38556619730357196046758857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25704413153571464031172571 38556619730357196046758857)
          ·
            refine ⟨28917464797767897035069143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38556619730357196046758857 28917464797767897035069143)
            ·
              refine ⟨43376197196651845552603715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28917464797767897035069143 43376197196651845552603715)
              ·
                refine ⟨65064295794977768328905573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43376197196651845552603715 65064295794977768328905573)
                ·
                  refine ⟨12199555461558331561669795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 65064295794977768328905573 12199555461558331561669795)
                  ·
                    refine ⟨18299333192337497342504693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12199555461558331561669795 18299333192337497342504693)
                    ·
                      refine ⟨1715562486781640375859815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18299333192337497342504693 1715562486781640375859815)
                      ·
                        rfl

theorem cell23_3341046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 1, 4, 1, 5].length) (baseStart_3341046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3341046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3341046 prefixEnd_3341046 := by exact prefixLift 3341046
  have htrace : WordTrace (prefixWord ++ tailWord_3341046) baseStart_3341046 baseEnd_3341046 := by
    simpa [prefixWord, tailWord_3341046, baseEnd_3341046] using wordTrace_append hprefix tailTrace_3341046
  have hstable : (prefixWord ++ tailWord_3341046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3341046).length < 2 ^ (prefixWord ++ tailWord_3341046).sum := by decide
  have hdescent : baseEnd_3341046 < baseStart_3341046 := by decide
  rcases family_descends (prefixWord ++ tailWord_3341046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3341049 : List Nat := [1, 2, 1, 3, 1, 1, 1, 6, 7]
def baseStart_3341049 : Nat := 118140960795 + 3341049 * 2 ^ 59
def prefixEnd_3341049 : Nat := 4983230072969 + 3 ^ 40 * 3341049 * 2
def baseEnd_3341049 : Nat := 190618225247067096013589

theorem tailTrace_3341049 : CollatzResearch.WordTrace tailWord_3341049 prefixEnd_3341049 190618225247067096013589 := by
  unfold tailWord_3341049
  simp only [CollatzResearch.WordTrace]
  refine ⟨121858068072957553586066201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81238712048638369057377467 121858068072957553586066201)
  ·
    refine ⟨91393551054718165189549651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121858068072957553586066201 91393551054718165189549651)
    ·
      refine ⟨137090326582077247784324477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91393551054718165189549651 137090326582077247784324477)
      ·
        refine ⟨51408872468278967919121679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 137090326582077247784324477 51408872468278967919121679)
        ·
          refine ⟨77113308702418451878682519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51408872468278967919121679 77113308702418451878682519)
          ·
            refine ⟨115669963053627677818023779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77113308702418451878682519 115669963053627677818023779)
            ·
              refine ⟨173504944580441516727035669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115669963053627677818023779 173504944580441516727035669)
              ·
                refine ⟨8133044277208196096579797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 173504944580441516727035669 8133044277208196096579797)
                ·
                  refine ⟨190618225247067096013589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8133044277208196096579797 190618225247067096013589)
                  ·
                    rfl

theorem cell23_3341049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 6, 7].length) (baseStart_3341049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3341049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3341049 prefixEnd_3341049 := by exact prefixLift 3341049
  have htrace : WordTrace (prefixWord ++ tailWord_3341049) baseStart_3341049 baseEnd_3341049 := by
    simpa [prefixWord, tailWord_3341049, baseEnd_3341049] using wordTrace_append hprefix tailTrace_3341049
  have hstable : (prefixWord ++ tailWord_3341049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3341049).length < 2 ^ (prefixWord ++ tailWord_3341049).sum := by decide
  have hdescent : baseEnd_3341049 < baseStart_3341049 := by decide
  rcases family_descends (prefixWord ++ tailWord_3341049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3341096 : List Nat := [2, 1, 5, 1, 1, 1, 2, 2, 1, 7]
def baseStart_3341096 : Nat := 118140960795 + 3341096 * 2 ^ 59
def prefixEnd_3341096 : Nat := 4983230072969 + 3 ^ 40 * 3341096 * 2
def baseEnd_3341096 : Nat := 571862720271455060078195

theorem tailTrace_3341096 : CollatzResearch.WordTrace tailWord_3341096 prefixEnd_3341096 571862720271455060078195 := by
  unfold tailWord_3341096
  simp only [CollatzResearch.WordTrace]
  refine ⟨60929891151893640306513571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81239854869191520408684761 60929891151893640306513571)
  ·
    refine ⟨91394836727840460459770357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60929891151893640306513571 91394836727840460459770357)
    ·
      refine ⟨8568265943235043168103471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 91394836727840460459770357 8568265943235043168103471)
      ·
        refine ⟨12852398914852564752155207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8568265943235043168103471 12852398914852564752155207)
        ·
          refine ⟨19278598372278847128232811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12852398914852564752155207 19278598372278847128232811)
          ·
            refine ⟨28917897558418270692349217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19278598372278847128232811 28917897558418270692349217)
            ·
              refine ⟨21688423168813703019261913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28917897558418270692349217 21688423168813703019261913)
              ·
                refine ⟨16266317376610277264446435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21688423168813703019261913 16266317376610277264446435)
                ·
                  refine ⟨24399476064915415896669653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16266317376610277264446435 24399476064915415896669653)
                  ·
                    refine ⟨571862720271455060078195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24399476064915415896669653 571862720271455060078195)
                    ·
                      rfl

theorem cell23_3341096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 2, 1, 7].length) (baseStart_3341096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3341096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3341096 prefixEnd_3341096 := by exact prefixLift 3341096
  have htrace : WordTrace (prefixWord ++ tailWord_3341096) baseStart_3341096 baseEnd_3341096 := by
    simpa [prefixWord, tailWord_3341096, baseEnd_3341096] using wordTrace_append hprefix tailTrace_3341096
  have hstable : (prefixWord ++ tailWord_3341096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3341096).length < 2 ^ (prefixWord ++ tailWord_3341096).sum := by decide
  have hdescent : baseEnd_3341096 < baseStart_3341096 := by decide
  rcases family_descends (prefixWord ++ tailWord_3341096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3341143 : List Nat := [1, 1, 3, 2, 4, 1, 1, 3, 3, 4]
def baseStart_3341143 : Nat := 118140960795 + 3341143 * 2 ^ 59
def prefixEnd_3341143 : Nat := 4983230072969 + 3 ^ 40 * 3341143 * 2
def baseEnd_3341143 : Nat := 571870764801708832115623

theorem tailTrace_3341143 : CollatzResearch.WordTrace tailWord_3341143 prefixEnd_3341143 571870764801708832115623 := by
  unfold tailWord_3341143
  simp only [CollatzResearch.WordTrace]
  refine ⟨121861496534617007639988083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81240997689744671759992055 121861496534617007639988083)
  ·
    refine ⟨182792244801925511459982125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121861496534617007639988083 182792244801925511459982125)
    ·
      refine ⟨68547091800722066797493297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 182792244801925511459982125 68547091800722066797493297)
      ·
        refine ⟨51410318850541550098119973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68547091800722066797493297 51410318850541550098119973)
        ·
          refine ⟨9639434784476540643397495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51410318850541550098119973 9639434784476540643397495)
          ·
            refine ⟨14459152176714810965096243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9639434784476540643397495 14459152176714810965096243)
            ·
              refine ⟨21688728265072216447644365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14459152176714810965096243 21688728265072216447644365)
              ·
                refine ⟨8133273099402081167866637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21688728265072216447644365 8133273099402081167866637)
                ·
                  refine ⟨3049977412275780437949989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8133273099402081167866637 3049977412275780437949989)
                  ·
                    refine ⟨571870764801708832115623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3049977412275780437949989 571870764801708832115623)
                    ·
                      rfl

theorem cell23_3341143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 3, 3, 4].length) (baseStart_3341143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3341143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3341143 prefixEnd_3341143 := by exact prefixLift 3341143
  have htrace : WordTrace (prefixWord ++ tailWord_3341143) baseStart_3341143 baseEnd_3341143 := by
    simpa [prefixWord, tailWord_3341143, baseEnd_3341143] using wordTrace_append hprefix tailTrace_3341143
  have hstable : (prefixWord ++ tailWord_3341143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3341143).length < 2 ^ (prefixWord ++ tailWord_3341143).sum := by decide
  have hdescent : baseEnd_3341143 < baseStart_3341143 := by decide
  rcases family_descends (prefixWord ++ tailWord_3341143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3341177 : List Nat := [1, 2, 1, 3, 2, 5, 1, 3, 1, 4]
def baseStart_3341177 : Nat := 118140960795 + 3341177 * 2 ^ 59
def prefixEnd_3341177 : Nat := 4983230072969 + 3 ^ 40 * 3341177 * 2
def baseEnd_3341177 : Nat := 571876584249126454440571

theorem tailTrace_3341177 : CollatzResearch.WordTrace tailWord_3341177 prefixEnd_3341177 571876584249126454440571 := by
  unfold tailWord_3341177
  simp only [CollatzResearch.WordTrace]
  refine ⟨121862736616493831446725785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81241824410995887631150523 121862736616493831446725785)
  ·
    refine ⟨91397052462370373585044339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121862736616493831446725785 91397052462370373585044339)
    ·
      refine ⟨137095578693555560377566509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91397052462370373585044339 137095578693555560377566509)
      ·
        refine ⟨51410842010083335141587441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 137095578693555560377566509 51410842010083335141587441)
        ·
          refine ⟨38558131507562501356190581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51410842010083335141587441 38558131507562501356190581)
          ·
            refine ⟨3614824828833984502142867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 38558131507562501356190581 3614824828833984502142867)
            ·
              refine ⟨5422237243250976753214301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3614824828833984502142867 5422237243250976753214301)
              ·
                refine ⟨2033338966219116282455363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5422237243250976753214301 2033338966219116282455363)
                ·
                  refine ⟨3050008449328674423683045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2033338966219116282455363 3050008449328674423683045)
                  ·
                    refine ⟨571876584249126454440571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3050008449328674423683045 571876584249126454440571)
                    ·
                      rfl

theorem cell23_3341177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 5, 1, 3, 1, 4].length) (baseStart_3341177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3341177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3341177 prefixEnd_3341177 := by exact prefixLift 3341177
  have htrace : WordTrace (prefixWord ++ tailWord_3341177) baseStart_3341177 baseEnd_3341177 := by
    simpa [prefixWord, tailWord_3341177, baseEnd_3341177] using wordTrace_append hprefix tailTrace_3341177
  have hstable : (prefixWord ++ tailWord_3341177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3341177).length < 2 ^ (prefixWord ++ tailWord_3341177).sum := by decide
  have hdescent : baseEnd_3341177 < baseStart_3341177 := by decide
  rcases family_descends (prefixWord ++ tailWord_3341177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3341183 : List Nat := [1, 1, 2, 2, 1, 1, 4, 2, 5, 1, 3]
def baseStart_3341183 : Nat := 118140960795 + 3341183 * 2 ^ 59
def prefixEnd_3341183 : Nat := 4983230072969 + 3 ^ 40 * 3341183 * 2
def baseEnd_3341183 : Nat := 1715632833631306339846685

theorem tailTrace_3341183 : CollatzResearch.WordTrace tailWord_3341183 prefixEnd_3341183 1715632833631306339846685 := by
  unfold tailWord_3341183
  simp only [CollatzResearch.WordTrace]
  refine ⟨121862955454472094471444203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81241970302981396314296135 121862955454472094471444203)
  ·
    refine ⟨182794433181708141707166305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121862955454472094471444203 182794433181708141707166305)
    ·
      refine ⟨137095824886281106280374729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182794433181708141707166305 137095824886281106280374729)
      ·
        refine ⟨102821868664710829710281047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137095824886281106280374729 102821868664710829710281047)
        ·
          refine ⟨154232802997066244565421571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102821868664710829710281047 154232802997066244565421571)
          ·
            refine ⟨231349204495599366848132357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154232802997066244565421571 231349204495599366848132357)
            ·
              refine ⟨43377975842924881284024817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 231349204495599366848132357 43377975842924881284024817)
              ·
                refine ⟨32533481882193660963018613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43377975842924881284024817 32533481882193660963018613)
                ·
                  refine ⟨3050013926455655715282995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 32533481882193660963018613 3050013926455655715282995)
                  ·
                    refine ⟨4575020889683483572924493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3050013926455655715282995 4575020889683483572924493)
                    ·
                      refine ⟨1715632833631306339846685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4575020889683483572924493 1715632833631306339846685)
                      ·
                        rfl

theorem cell23_3341183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 2, 5, 1, 3].length) (baseStart_3341183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3341183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3341183 prefixEnd_3341183 := by exact prefixLift 3341183
  have htrace : WordTrace (prefixWord ++ tailWord_3341183) baseStart_3341183 baseEnd_3341183 := by
    simpa [prefixWord, tailWord_3341183, baseEnd_3341183] using wordTrace_append hprefix tailTrace_3341183
  have hstable : (prefixWord ++ tailWord_3341183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3341183).length < 2 ^ (prefixWord ++ tailWord_3341183).sum := by decide
  have hdescent : baseEnd_3341183 < baseStart_3341183 := by decide
  rcases family_descends (prefixWord ++ tailWord_3341183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3341194 : List Nat := [3, 1, 2, 4, 1, 2, 3, 2, 1, 4]
def baseStart_3341194 : Nat := 118140960795 + 3341194 * 2 ^ 59
def prefixEnd_3341194 : Nat := 4983230072969 + 3 ^ 40 * 3341194 * 2
def baseEnd_3341194 : Nat := 571879493972835265603045

theorem tailTrace_3341194 : CollatzResearch.WordTrace tailWord_3341194 prefixEnd_3341194 571879493972835265603045 := by
  unfold tailWord_3341194
  simp only [CollatzResearch.WordTrace]
  refine ⟨30465839164358060837523659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81242237771621495566729757 30465839164358060837523659)
  ·
    refine ⟨45698758746537091256285489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30465839164358060837523659 45698758746537091256285489)
    ·
      refine ⟨34274069059902818442214117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45698758746537091256285489 34274069059902818442214117)
      ·
        refine ⟨6426387948731778457915147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34274069059902818442214117 6426387948731778457915147)
        ·
          refine ⟨9639581923097667686872721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6426387948731778457915147 9639581923097667686872721)
          ·
            refine ⟨7229686442323250765154541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9639581923097667686872721 7229686442323250765154541)
            ·
              refine ⟨2711132415871219036932953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7229686442323250765154541 2711132415871219036932953)
              ·
                refine ⟨2033349311903414277699715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2711132415871219036932953 2033349311903414277699715)
                ·
                  refine ⟨3050023967855121416549573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2033349311903414277699715 3050023967855121416549573)
                  ·
                    refine ⟨571879493972835265603045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3050023967855121416549573 571879493972835265603045)
                    ·
                      rfl

theorem cell23_3341194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 3, 2, 1, 4].length) (baseStart_3341194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3341194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3341194 prefixEnd_3341194 := by exact prefixLift 3341194
  have htrace : WordTrace (prefixWord ++ tailWord_3341194) baseStart_3341194 baseEnd_3341194 := by
    simpa [prefixWord, tailWord_3341194, baseEnd_3341194] using wordTrace_append hprefix tailTrace_3341194
  have hstable : (prefixWord ++ tailWord_3341194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3341194).length < 2 ^ (prefixWord ++ tailWord_3341194).sum := by decide
  have hdescent : baseEnd_3341194 < baseStart_3341194 := by decide
  rcases family_descends (prefixWord ++ tailWord_3341194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3341263 : List Nat := [1, 1, 2, 1, 1, 8, 1, 8]
def baseStart_3341263 : Nat := 118140960795 + 3341263 * 2 ^ 59
def prefixEnd_3341263 : Nat := 4983230072969 + 3 ^ 40 * 3341263 * 2
def baseEnd_3341263 : Nat := 63543478225320963957271

theorem tailTrace_3341263 : CollatzResearch.WordTrace tailWord_3341263 prefixEnd_3341263 63543478225320963957271 := by
  unfold tailWord_3341263
  simp only [CollatzResearch.WordTrace]
  refine ⟨121865873294182268134356443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81243915529454845422904295 121865873294182268134356443)
  ·
    refine ⟨182798809941273402201534665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121865873294182268134356443 182798809941273402201534665)
    ·
      refine ⟨137099107455955051651150999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182798809941273402201534665 137099107455955051651150999)
      ·
        refine ⟨205648661183932577476726499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137099107455955051651150999 205648661183932577476726499)
        ·
          refine ⟨308472991775898866215089749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 205648661183932577476726499 308472991775898866215089749)
          ·
            refine ⟨3614917872373814838458083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 308472991775898866215089749 3614917872373814838458083)
            ·
              refine ⟨5422376808560722257687125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3614917872373814838458083 5422376808560722257687125)
              ·
                refine ⟨63543478225320963957271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5422376808560722257687125 63543478225320963957271)
                ·
                  rfl

theorem cell23_3341263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 8, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 8, 1, 8].length) (baseStart_3341263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3341263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3341263 prefixEnd_3341263 := by exact prefixLift 3341263
  have htrace : WordTrace (prefixWord ++ tailWord_3341263) baseStart_3341263 baseEnd_3341263 := by
    simpa [prefixWord, tailWord_3341263, baseEnd_3341263] using wordTrace_append hprefix tailTrace_3341263
  have hstable : (prefixWord ++ tailWord_3341263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3341263).length < 2 ^ (prefixWord ++ tailWord_3341263).sum := by decide
  have hdescent : baseEnd_3341263 < baseStart_3341263 := by decide
  rcases family_descends (prefixWord ++ tailWord_3341263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3341290 : List Nat := [3, 1, 3, 1, 2, 2, 2, 2, 1, 3, 3]
def baseStart_3341290 : Nat := 118140960795 + 3341290 * 2 ^ 59
def prefixEnd_3341290 : Nat := 4983230072969 + 3 ^ 40 * 3341290 * 2
def baseEnd_3341290 : Nat := 1715687776061337421208693

theorem tailTrace_3341290 : CollatzResearch.WordTrace tailWord_3341290 prefixEnd_3341290 1715687776061337421208693 := by
  unfold tailWord_3341290
  simp only [CollatzResearch.WordTrace]
  refine ⟨30466714516271112936397331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81244572043389634497059549 30466714516271112936397331)
  ·
    refine ⟨45700071774406669404595997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30466714516271112936397331 45700071774406669404595997)
    ·
      refine ⟨17137526915402501026723499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45700071774406669404595997 17137526915402501026723499)
      ·
        refine ⟨25706290373103751540085249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17137526915402501026723499 25706290373103751540085249)
        ·
          refine ⟨19279717779827813655063937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25706290373103751540085249 19279717779827813655063937)
          ·
            refine ⟨14459788334870860241297953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19279717779827813655063937 14459788334870860241297953)
            ·
              refine ⟨10844841251153145180973465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14459788334870860241297953 10844841251153145180973465)
              ·
                refine ⟨8133630938364858885730099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10844841251153145180973465 8133630938364858885730099)
                ·
                  refine ⟨12200446407547288328595149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8133630938364858885730099 12200446407547288328595149)
                  ·
                    refine ⟨4575167402830233123223181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12200446407547288328595149 4575167402830233123223181)
                    ·
                      refine ⟨1715687776061337421208693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4575167402830233123223181 1715687776061337421208693)
                      ·
                        rfl

theorem cell23_3341290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 2, 2, 1, 3, 3].length) (baseStart_3341290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3341290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3341290 prefixEnd_3341290 := by exact prefixLift 3341290
  have htrace : WordTrace (prefixWord ++ tailWord_3341290) baseStart_3341290 baseEnd_3341290 := by
    simpa [prefixWord, tailWord_3341290, baseEnd_3341290] using wordTrace_append hprefix tailTrace_3341290
  have hstable : (prefixWord ++ tailWord_3341290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3341290).length < 2 ^ (prefixWord ++ tailWord_3341290).sum := by decide
  have hdescent : baseEnd_3341290 < baseStart_3341290 := by decide
  rcases family_descends (prefixWord ++ tailWord_3341290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3341301 : List Nat := [1, 3, 5, 2, 1, 2, 1, 2, 2, 4]
def baseStart_3341301 : Nat := 118140960795 + 3341301 * 2 ^ 59
def prefixEnd_3341301 : Nat := 4983230072969 + 3 ^ 40 * 3341301 * 2
def baseEnd_3341301 : Nat := 571897808116178959390381

theorem tailTrace_3341301 : CollatzResearch.WordTrace tailWord_3341301 prefixEnd_3341301 571897808116178959390381 := by
  unfold tailWord_3341301
  simp only [CollatzResearch.WordTrace]
  refine ⟨121867259268044600624239757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81244839512029733749493171 121867259268044600624239757)
  ·
    refine ⟨45700222225516725234089909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121867259268044600624239757 45700222225516725234089909)
    ·
      refine ⟨4284395833642192990695929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 45700222225516725234089909 4284395833642192990695929)
      ·
        refine ⟨3213296875231644743021947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4284395833642192990695929 3213296875231644743021947)
        ·
          refine ⟨4819945312847467114532921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3213296875231644743021947 4819945312847467114532921)
          ·
            refine ⟨3614958984635600335899691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4819945312847467114532921 3614958984635600335899691)
            ·
              refine ⟨5422438476953400503849537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3614958984635600335899691 5422438476953400503849537)
              ·
                refine ⟨4066828857715050377887153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5422438476953400503849537 4066828857715050377887153)
                ·
                  refine ⟨3050121643286287783415365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4066828857715050377887153 3050121643286287783415365)
                  ·
                    refine ⟨571897808116178959390381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3050121643286287783415365 571897808116178959390381)
                    ·
                      rfl

theorem cell23_3341301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 2, 1, 2, 2, 4].length) (baseStart_3341301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3341301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3341301 prefixEnd_3341301 := by exact prefixLift 3341301
  have htrace : WordTrace (prefixWord ++ tailWord_3341301) baseStart_3341301 baseEnd_3341301 := by
    simpa [prefixWord, tailWord_3341301, baseEnd_3341301] using wordTrace_append hprefix tailTrace_3341301
  have hstable : (prefixWord ++ tailWord_3341301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3341301).length < 2 ^ (prefixWord ++ tailWord_3341301).sum := by decide
  have hdescent : baseEnd_3341301 < baseStart_3341301 := by decide
  rcases family_descends (prefixWord ++ tailWord_3341301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3341323 : List Nat := [1, 1, 1, 1, 6, 2, 2, 1, 2, 6]
def baseStart_3341323 : Nat := 118140960795 + 3341323 * 2 ^ 59
def prefixEnd_3341323 : Nat := 4983230072969 + 3 ^ 40 * 3341323 * 2
def baseEnd_3341323 : Nat := 571901573640978597365347

theorem tailTrace_3341323 : CollatzResearch.WordTrace tailWord_3341323 prefixEnd_3341323 571901573640978597365347 := by
  unfold tailWord_3341323
  simp only [CollatzResearch.WordTrace]
  refine ⟨121868061673964898381540623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81245374449309932254360415 121868061673964898381540623)
  ·
    refine ⟨182802092510947347572310935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121868061673964898381540623 182802092510947347572310935)
    ·
      refine ⟨274203138766421021358466403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182802092510947347572310935 274203138766421021358466403)
      ·
        refine ⟨411304708149631532037699605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 274203138766421021358466403 411304708149631532037699605)
        ·
          refine ⟨19279908194513978064267169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 411304708149631532037699605 19279908194513978064267169)
          ·
            refine ⟨14459931145885483548200377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19279908194513978064267169 14459931145885483548200377)
            ·
              refine ⟨10844948359414112661150283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14459931145885483548200377 10844948359414112661150283)
              ·
                refine ⟨16267422539121168991725425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10844948359414112661150283 16267422539121168991725425)
                ·
                  refine ⟨12200566904340876743794069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16267422539121168991725425 12200566904340876743794069)
                  ·
                    refine ⟨571901573640978597365347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12200566904340876743794069 571901573640978597365347)
                    ·
                      rfl

theorem cell23_3341323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 2, 1, 2, 6].length) (baseStart_3341323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3341323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3341323 prefixEnd_3341323 := by exact prefixLift 3341323
  have htrace : WordTrace (prefixWord ++ tailWord_3341323) baseStart_3341323 baseEnd_3341323 := by
    simpa [prefixWord, tailWord_3341323, baseEnd_3341323] using wordTrace_append hprefix tailTrace_3341323
  have hstable : (prefixWord ++ tailWord_3341323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3341323).length < 2 ^ (prefixWord ++ tailWord_3341323).sum := by decide
  have hdescent : baseEnd_3341323 < baseStart_3341323 := by decide
  rcases family_descends (prefixWord ++ tailWord_3341323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3341324 : List Nat := [2, 2, 1, 2, 3, 3, 3, 1, 2, 1, 3]
def baseStart_3341324 : Nat := 118140960795 + 3341324 * 2 ^ 59
def prefixEnd_3341324 : Nat := 4983230072969 + 3 ^ 40 * 3341324 * 2
def baseEnd_3341324 : Nat := 1715705234403590288183537

theorem tailTrace_3341324 : CollatzResearch.WordTrace tailWord_3341324 prefixEnd_3341324 1715705234403590288183537 := by
  unfold tailWord_3341324
  simp only [CollatzResearch.WordTrace]
  refine ⟨60934049073480637776163513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81245398764640850368218017 60934049073480637776163513)
  ·
    refine ⟨45700536805110478332122635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60934049073480637776163513 45700536805110478332122635)
    ·
      refine ⟨68550805207665717498183953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45700536805110478332122635 68550805207665717498183953)
      ·
        refine ⟨51413103905749288123637965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68550805207665717498183953 51413103905749288123637965)
        ·
          refine ⟨19279913964655983046364237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51413103905749288123637965 19279913964655983046364237)
          ·
            refine ⟨7229967736745993642386589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19279913964655983046364237 7229967736745993642386589)
            ·
              refine ⟨2711237901279747615894971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7229967736745993642386589 2711237901279747615894971)
              ·
                refine ⟨4066856851919621423842457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2711237901279747615894971 4066856851919621423842457)
                ·
                  refine ⟨3050142638939716067881843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4066856851919621423842457 3050142638939716067881843)
                  ·
                    refine ⟨4575213958409574101822765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3050142638939716067881843 4575213958409574101822765)
                    ·
                      refine ⟨1715705234403590288183537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4575213958409574101822765 1715705234403590288183537)
                      ·
                        rfl

theorem cell23_3341324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 3, 1, 2, 1, 3].length) (baseStart_3341324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3341324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3341324 prefixEnd_3341324 := by exact prefixLift 3341324
  have htrace : WordTrace (prefixWord ++ tailWord_3341324) baseStart_3341324 baseEnd_3341324 := by
    simpa [prefixWord, tailWord_3341324, baseEnd_3341324] using wordTrace_append hprefix tailTrace_3341324
  have hstable : (prefixWord ++ tailWord_3341324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3341324).length < 2 ^ (prefixWord ++ tailWord_3341324).sum := by decide
  have hdescent : baseEnd_3341324 < baseStart_3341324 := by decide
  rcases family_descends (prefixWord ++ tailWord_3341324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3341347 : List Nat := [1, 1, 1, 4, 3, 2, 1, 2, 4, 2, 2]
def baseStart_3341347 : Nat := 118140960795 + 3341347 * 2 ^ 59
def prefixEnd_3341347 : Nat := 4983230072969 + 3 ^ 40 * 3341347 * 2
def baseEnd_3341347 : Nat := 1715717044458643698195931

theorem tailTrace_3341347 : CollatzResearch.WordTrace tailWord_3341347 prefixEnd_3341347 1715717044458643698195931 := by
  unfold tailWord_3341347
  simp only [CollatzResearch.WordTrace]
  refine ⟨121868937025877950480414295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81245958017251966986942863 121868937025877950480414295)
  ·
    refine ⟨182803405538816925720621443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121868937025877950480414295 182803405538816925720621443)
    ·
      refine ⟨274205108308225388580932165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182803405538816925720621443 274205108308225388580932165)
      ·
        refine ⟨51413457807792260358924781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 274205108308225388580932165 51413457807792260358924781)
        ·
          refine ⟨19280046677922097634596793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51413457807792260358924781 19280046677922097634596793)
          ·
            refine ⟨14460035008441573225947595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19280046677922097634596793 14460035008441573225947595)
            ·
              refine ⟨21690052512662359838921393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14460035008441573225947595 21690052512662359838921393)
              ·
                refine ⟨16267539384496769879191045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21690052512662359838921393 16267539384496769879191045)
                ·
                  refine ⟨3050163634593144352348321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16267539384496769879191045 3050163634593144352348321)
                  ·
                    refine ⟨2287622725944858264261241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3050163634593144352348321 2287622725944858264261241)
                    ·
                      refine ⟨1715717044458643698195931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2287622725944858264261241 1715717044458643698195931)
                      ·
                        rfl

theorem cell23_3341347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 2, 4, 2, 2].length) (baseStart_3341347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3341347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3341347 prefixEnd_3341347 := by exact prefixLift 3341347
  have htrace : WordTrace (prefixWord ++ tailWord_3341347) baseStart_3341347 baseEnd_3341347 := by
    simpa [prefixWord, tailWord_3341347, baseEnd_3341347] using wordTrace_append hprefix tailTrace_3341347
  have hstable : (prefixWord ++ tailWord_3341347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3341347).length < 2 ^ (prefixWord ++ tailWord_3341347).sum := by decide
  have hdescent : baseEnd_3341347 < baseStart_3341347 := by decide
  rcases family_descends (prefixWord ++ tailWord_3341347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3341370 : List Nat := [3, 1, 1, 1, 3, 1, 2, 6, 5]
def baseStart_3341370 : Nat := 118140960795 + 3341370 * 2 ^ 59
def prefixEnd_3341370 : Nat := 4983230072969 + 3 ^ 40 * 3341370 * 2
def baseEnd_3341370 : Nat := 190636539390410789800925

theorem tailTrace_3341370 : CollatzResearch.WordTrace tailWord_3341370 prefixEnd_3341370 190636539390410789800925 := by
  unfold tailWord_3341370
  simp only [CollatzResearch.WordTrace]
  refine ⟨30467443976198656352125391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81246517269863083605667709 30467443976198656352125391)
  ·
    refine ⟨45701165964297984528188087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30467443976198656352125391 45701165964297984528188087)
    ·
      refine ⟨68551748946446976792282131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45701165964297984528188087 68551748946446976792282131)
      ·
        refine ⟨102827623419670465188423197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68551748946446976792282131 102827623419670465188423197)
        ·
          refine ⟨38560358782376424445658699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102827623419670465188423197 38560358782376424445658699)
          ·
            refine ⟨57840538173564636668488049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38560358782376424445658699 57840538173564636668488049)
            ·
              refine ⟨43380403630173477501366037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57840538173564636668488049 43380403630173477501366037)
              ·
                refine ⟨2033456420164381757876533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 43380403630173477501366037 2033456420164381757876533)
                ·
                  refine ⟨190636539390410789800925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2033456420164381757876533 190636539390410789800925)
                  ·
                    rfl

theorem cell23_3341370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 6, 5].length) (baseStart_3341370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3341370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3341370 prefixEnd_3341370 := by exact prefixLift 3341370
  have htrace : WordTrace (prefixWord ++ tailWord_3341370) baseStart_3341370 baseEnd_3341370 := by
    simpa [prefixWord, tailWord_3341370, baseEnd_3341370] using wordTrace_append hprefix tailTrace_3341370
  have hstable : (prefixWord ++ tailWord_3341370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3341370).length < 2 ^ (prefixWord ++ tailWord_3341370).sum := by decide
  have hdescent : baseEnd_3341370 < baseStart_3341370 := by decide
  rcases family_descends (prefixWord ++ tailWord_3341370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3341400 : List Nat := [2, 1, 2, 2, 1, 3, 4, 1, 2, 5]
def baseStart_3341400 : Nat := 118140960795 + 3341400 * 2 ^ 59
def prefixEnd_3341400 : Nat := 4983230072969 + 3 ^ 40 * 3341400 * 2
def baseEnd_3341400 : Nat := 571914752977777330277729

theorem tailTrace_3341400 : CollatzResearch.WordTrace tailWord_3341400 prefixEnd_3341400 571914752977777330277729 := by
  unfold tailWord_3341400
  simp only [CollatzResearch.WordTrace]
  refine ⟨60935435047342970266046827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81247246729790627021395769 60935435047342970266046827)
  ·
    refine ⟨91403152571014455399070241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60935435047342970266046827 91403152571014455399070241)
    ·
      refine ⟨68552364428260841549302681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91403152571014455399070241 68552364428260841549302681)
      ·
        refine ⟨51414273321195631161977011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68552364428260841549302681 51414273321195631161977011)
        ·
          refine ⟨77121409981793446742965517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51414273321195631161977011 77121409981793446742965517)
          ·
            refine ⟨28920528743172542528612069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77121409981793446742965517 28920528743172542528612069)
            ·
              refine ⟨5422599139344851724114763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28920528743172542528612069 5422599139344851724114763)
              ·
                refine ⟨8133898709017277586172145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5422599139344851724114763 8133898709017277586172145)
                ·
                  refine ⟨6100424031762958189629109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8133898709017277586172145 6100424031762958189629109)
                  ·
                    refine ⟨571914752977777330277729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6100424031762958189629109 571914752977777330277729)
                    ·
                      rfl

theorem cell23_3341400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 4, 1, 2, 5].length) (baseStart_3341400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3341400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3341400 prefixEnd_3341400 := by exact prefixLift 3341400
  have htrace : WordTrace (prefixWord ++ tailWord_3341400) baseStart_3341400 baseEnd_3341400 := by
    simpa [prefixWord, tailWord_3341400, baseEnd_3341400] using wordTrace_append hprefix tailTrace_3341400
  have hstable : (prefixWord ++ tailWord_3341400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3341400).length < 2 ^ (prefixWord ++ tailWord_3341400).sum := by decide
  have hdescent : baseEnd_3341400 < baseStart_3341400 := by decide
  rcases family_descends (prefixWord ++ tailWord_3341400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3341420 : List Nat := [2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 4]
def baseStart_3341420 : Nat := 118140960795 + 3341420 * 2 ^ 59
def prefixEnd_3341420 : Nat := 4983230072969 + 3 ^ 40 * 3341420 * 2
def baseEnd_3341420 : Nat := 1715754528546421912583095

theorem tailTrace_3341420 : CollatzResearch.WordTrace tailWord_3341420 prefixEnd_3341420 1715754528546421912583095 := by
  unfold tailWord_3341420
  simp only [CollatzResearch.WordTrace]
  refine ⟨60935799777306741973910857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81247733036408989298547809 60935799777306741973910857)
  ·
    refine ⟨45701849832980056480433143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60935799777306741973910857 45701849832980056480433143)
    ·
      refine ⟨68552774749470084720649715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45701849832980056480433143 68552774749470084720649715)
      ·
        refine ⟨102829162124205127080974573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68552774749470084720649715 102829162124205127080974573)
        ·
          refine ⟨38560935796576922655365465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102829162124205127080974573 38560935796576922655365465)
          ·
            refine ⟨28920701847432691991524099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38560935796576922655365465 28920701847432691991524099)
            ·
              refine ⟨43381052771149037987286149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28920701847432691991524099 43381052771149037987286149)
              ·
                refine ⟨8133947394590444622616153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43381052771149037987286149 8133947394590444622616153)
                ·
                  refine ⟨6100460545942833466962115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8133947394590444622616153 6100460545942833466962115)
                  ·
                    refine ⟨9150690818914250200443173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6100460545942833466962115 9150690818914250200443173)
                    ·
                      refine ⟨1715754528546421912583095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9150690818914250200443173 1715754528546421912583095)
                      ·
                        rfl

theorem cell23_3341420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 4].length) (baseStart_3341420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3341420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3341420 prefixEnd_3341420 := by exact prefixLift 3341420
  have htrace : WordTrace (prefixWord ++ tailWord_3341420) baseStart_3341420 baseEnd_3341420 := by
    simpa [prefixWord, tailWord_3341420, baseEnd_3341420] using wordTrace_append hprefix tailTrace_3341420
  have hstable : (prefixWord ++ tailWord_3341420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3341420).length < 2 ^ (prefixWord ++ tailWord_3341420).sum := by decide
  have hdescent : baseEnd_3341420 < baseStart_3341420 := by decide
  rcases family_descends (prefixWord ++ tailWord_3341420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3341423 : List Nat := [1, 1, 2, 1, 3, 3, 1, 1, 2, 3, 5]
def baseStart_3341423 : Nat := 118140960795 + 3341423 * 2 ^ 59
def prefixEnd_3341423 : Nat := 4983230072969 + 3 ^ 40 * 3341423 * 2
def baseEnd_3341423 : Nat := 1715756068988385400845581

theorem tailTrace_3341423 : CollatzResearch.WordTrace tailWord_3341423 prefixEnd_3341423 1715756068988385400845581 := by
  unfold tailWord_3341423
  simp only [CollatzResearch.WordTrace]
  refine ⟨121871708973602615460180923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81247805982401743640120615 121871708973602615460180923)
  ·
    refine ⟨182807563460403923190271385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121871708973602615460180923 182807563460403923190271385)
    ·
      refine ⟨137105672595302942392703539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182807563460403923190271385 137105672595302942392703539)
      ·
        refine ⟨205658508892954413589055309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137105672595302942392703539 205658508892954413589055309)
        ·
          refine ⟨77121940834857905095895741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 205658508892954413589055309 77121940834857905095895741)
          ·
            refine ⟨28920727813071714410960903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77121940834857905095895741 28920727813071714410960903)
            ·
              refine ⟨43381091719607571616441355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28920727813071714410960903 43381091719607571616441355)
              ·
                refine ⟨65071637579411357424662033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43381091719607571616441355 65071637579411357424662033)
                ·
                  refine ⟨48803728184558518068496525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65071637579411357424662033 48803728184558518068496525)
                  ·
                    refine ⟨18301398069209444275686197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 48803728184558518068496525 18301398069209444275686197)
                    ·
                      refine ⟨1715756068988385400845581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18301398069209444275686197 1715756068988385400845581)
                      ·
                        rfl

theorem cell23_3341423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 1, 2, 3, 5].length) (baseStart_3341423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3341423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3341423 prefixEnd_3341423 := by exact prefixLift 3341423
  have htrace : WordTrace (prefixWord ++ tailWord_3341423) baseStart_3341423 baseEnd_3341423 := by
    simpa [prefixWord, tailWord_3341423, baseEnd_3341423] using wordTrace_append hprefix tailTrace_3341423
  have hstable : (prefixWord ++ tailWord_3341423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3341423).length < 2 ^ (prefixWord ++ tailWord_3341423).sum := by decide
  have hdescent : baseEnd_3341423 < baseStart_3341423 := by decide
  rcases family_descends (prefixWord ++ tailWord_3341423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3341437 : List Nat := [1, 4, 1, 1, 3, 1, 3, 1, 2, 4, 2]
def baseStart_3341437 : Nat := 118140960795 + 3341437 * 2 ^ 59
def prefixEnd_3341437 : Nat := 4983230072969 + 3 ^ 40 * 3341437 * 2
def baseEnd_3341437 : Nat := 1715763257717548346070517

theorem tailTrace_3341437 : CollatzResearch.WordTrace tailWord_3341437 prefixEnd_3341437 1715763257717548346070517 := by
  unfold tailWord_3341437
  simp only [CollatzResearch.WordTrace]
  refine ⟨121872219595551895851190565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81248146397034597234127043 121872219595551895851190565)
  ·
    refine ⟨22851041174165980472098231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 121872219595551895851190565 22851041174165980472098231)
    ·
      refine ⟨34276561761248970708147347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22851041174165980472098231 34276561761248970708147347)
      ·
        refine ⟨51414842641873456062221021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34276561761248970708147347 51414842641873456062221021)
        ·
          refine ⟨19280565990702546023332883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51414842641873456062221021 19280565990702546023332883)
          ·
            refine ⟨28920848986053819034999325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19280565990702546023332883 28920848986053819034999325)
            ·
              refine ⟨10845318369770182138124747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28920848986053819034999325 10845318369770182138124747)
              ·
                refine ⟨16267977554655273207187121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10845318369770182138124747 16267977554655273207187121)
                ·
                  refine ⟨12200983165991454905390341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16267977554655273207187121 12200983165991454905390341)
                  ·
                    refine ⟨2287684343623397794760689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12200983165991454905390341 2287684343623397794760689)
                    ·
                      refine ⟨1715763257717548346070517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2287684343623397794760689 1715763257717548346070517)
                      ·
                        rfl

theorem cell23_3341437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 3, 1, 2, 4, 2].length) (baseStart_3341437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3341437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3341437 prefixEnd_3341437 := by exact prefixLift 3341437
  have htrace : WordTrace (prefixWord ++ tailWord_3341437) baseStart_3341437 baseEnd_3341437 := by
    simpa [prefixWord, tailWord_3341437, baseEnd_3341437] using wordTrace_append hprefix tailTrace_3341437
  have hstable : (prefixWord ++ tailWord_3341437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3341437).length < 2 ^ (prefixWord ++ tailWord_3341437).sum := by decide
  have hdescent : baseEnd_3341437 < baseStart_3341437 := by decide
  rcases family_descends (prefixWord ++ tailWord_3341437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3341440 : List Nat := [2, 1, 1, 2, 1, 3, 2, 2, 4, 2, 3]
def baseStart_3341440 : Nat := 118140960795 + 3341440 * 2 ^ 59
def prefixEnd_3341440 : Nat := 4983230072969 + 3 ^ 40 * 3341440 * 2
def baseEnd_3341440 : Nat := 1715764798159511834333003

theorem tailTrace_3341440 : CollatzResearch.WordTrace tailWord_3341440 prefixEnd_3341440 1715764798159511834333003 := by
  unfold tailWord_3341440
  simp only [CollatzResearch.WordTrace]
  refine ⟨60936164507270513681774887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81248219343027351575699849 60936164507270513681774887)
  ·
    refine ⟨91404246760905770522662331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60936164507270513681774887 91404246760905770522662331)
    ·
      refine ⟨137106370141358655783993497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91404246760905770522662331 137106370141358655783993497)
      ·
        refine ⟨102829777606018991837995123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137106370141358655783993497 102829777606018991837995123)
        ·
          refine ⟨154244666409028487756992685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102829777606018991837995123 154244666409028487756992685)
          ·
            refine ⟨57841749903385682908872257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 154244666409028487756992685 57841749903385682908872257)
            ·
              refine ⟨43381312427539262181654193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57841749903385682908872257 43381312427539262181654193)
              ·
                refine ⟨32535984320654446636240645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43381312427539262181654193 32535984320654446636240645)
                ·
                  refine ⟨6100497060122708744295121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32535984320654446636240645 6100497060122708744295121)
                  ·
                    refine ⟨4575372795092031558221341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6100497060122708744295121 4575372795092031558221341)
                    ·
                      refine ⟨1715764798159511834333003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4575372795092031558221341 1715764798159511834333003)
                      ·
                        rfl

theorem cell23_3341440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 2, 4, 2, 3].length) (baseStart_3341440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3341440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3341440 prefixEnd_3341440 := by exact prefixLift 3341440
  have htrace : WordTrace (prefixWord ++ tailWord_3341440) baseStart_3341440 baseEnd_3341440 := by
    simpa [prefixWord, tailWord_3341440, baseEnd_3341440] using wordTrace_append hprefix tailTrace_3341440
  have hstable : (prefixWord ++ tailWord_3341440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3341440).length < 2 ^ (prefixWord ++ tailWord_3341440).sum := by decide
  have hdescent : baseEnd_3341440 < baseStart_3341440 := by decide
  rcases family_descends (prefixWord ++ tailWord_3341440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3341454 : List Nat := [4, 1, 1, 3, 2, 3, 1, 1, 2, 1, 4]
def baseStart_3341454 : Nat := 118140960795 + 3341454 * 2 ^ 59
def prefixEnd_3341454 : Nat := 4983230072969 + 3 ^ 40 * 3341454 * 2
def baseEnd_3341454 : Nat := 1715771986888674779557939

theorem tailTrace_3341454 : CollatzResearch.WordTrace tailWord_3341454 prefixEnd_3341454 1715771986888674779557939 := by
  unfold tailWord_3341454
  simp only [CollatzResearch.WordTrace]
  refine ⟨15234104954561288469319927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81248559757660205169706277 15234104954561288469319927)
  ·
    refine ⟨22851157431841932703979891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15234104954561288469319927 22851157431841932703979891)
    ·
      refine ⟨34276736147762899055969837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22851157431841932703979891 34276736147762899055969837)
      ·
        refine ⟨12853776055411087145988689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34276736147762899055969837 12853776055411087145988689)
        ·
          refine ⟨9640332041558315359491517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12853776055411087145988689 9640332041558315359491517)
          ·
            refine ⟨3615124515584368259809319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9640332041558315359491517 3615124515584368259809319)
            ·
              refine ⟨5422686773376552389713979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3615124515584368259809319 5422686773376552389713979)
              ·
                refine ⟨8134030160064828584570969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5422686773376552389713979 8134030160064828584570969)
                ·
                  refine ⟨6100522620048621438428227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8134030160064828584570969 6100522620048621438428227)
                  ·
                    refine ⟨9150783930072932157642341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6100522620048621438428227 9150783930072932157642341)
                    ·
                      refine ⟨1715771986888674779557939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9150783930072932157642341 1715771986888674779557939)
                      ·
                        rfl

theorem cell23_3341454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 3, 1, 1, 2, 1, 4].length) (baseStart_3341454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3341454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3341454 prefixEnd_3341454 := by exact prefixLift 3341454
  have htrace : WordTrace (prefixWord ++ tailWord_3341454) baseStart_3341454 baseEnd_3341454 := by
    simpa [prefixWord, tailWord_3341454, baseEnd_3341454] using wordTrace_append hprefix tailTrace_3341454
  have hstable : (prefixWord ++ tailWord_3341454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3341454).length < 2 ^ (prefixWord ++ tailWord_3341454).sum := by decide
  have hdescent : baseEnd_3341454 < baseStart_3341454 := by decide
  rcases family_descends (prefixWord ++ tailWord_3341454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3341464 : List Nat := [2, 1, 2, 4, 2, 1, 1, 5, 1, 4]
def baseStart_3341464 : Nat := 118140960795 + 3341464 * 2 ^ 59
def prefixEnd_3341464 : Nat := 4983230072969 + 3 ^ 40 * 3341464 * 2
def baseEnd_3341464 : Nat := 571925707231739913477631

theorem tailTrace_3341464 : CollatzResearch.WordTrace tailWord_3341464 prefixEnd_3341464 571925707231739913477631 := by
  unfold tailWord_3341464
  simp only [CollatzResearch.WordTrace]
  refine ⟨60936602183227039731211723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81248802910969386308282297 60936602183227039731211723)
  ·
    refine ⟨91404903274840559596817585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60936602183227039731211723 91404903274840559596817585)
    ·
      refine ⟨68553677456130419697613189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91404903274840559596817585 68553677456130419697613189)
      ·
        refine ⟨12853814523024453693302473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 68553677456130419697613189 12853814523024453693302473)
        ·
          refine ⟨9640360892268340269976855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12853814523024453693302473 9640360892268340269976855)
          ·
            refine ⟨14460541338402510404965283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9640360892268340269976855 14460541338402510404965283)
            ·
              refine ⟨21690812007603765607447925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14460541338402510404965283 21690812007603765607447925)
              ·
                refine ⟨2033513625712853025698243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21690812007603765607447925 2033513625712853025698243)
                ·
                  refine ⟨3050270438569279538547365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2033513625712853025698243 3050270438569279538547365)
                  ·
                    refine ⟨571925707231739913477631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3050270438569279538547365 571925707231739913477631)
                    ·
                      rfl

theorem cell23_3341464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 5, 1, 4].length) (baseStart_3341464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3341464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3341464 prefixEnd_3341464 := by exact prefixLift 3341464
  have htrace : WordTrace (prefixWord ++ tailWord_3341464) baseStart_3341464 baseEnd_3341464 := by
    simpa [prefixWord, tailWord_3341464, baseEnd_3341464] using wordTrace_append hprefix tailTrace_3341464
  have hstable : (prefixWord ++ tailWord_3341464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3341464).length < 2 ^ (prefixWord ++ tailWord_3341464).sum := by decide
  have hdescent : baseEnd_3341464 < baseStart_3341464 := by decide
  rcases family_descends (prefixWord ++ tailWord_3341464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3341477 : List Nat := [1, 3, 1, 2, 1, 6, 1, 2, 6]
def baseStart_3341477 : Nat := 118140960795 + 3341477 * 2 ^ 59
def prefixEnd_3341477 : Nat := 4983230072969 + 3 ^ 40 * 3341477 * 2
def baseEnd_3341477 : Nat := 190642644104858687730037

theorem tailTrace_3341477 : CollatzResearch.WordTrace tailWord_3341477 prefixEnd_3341477 190642644104858687730037 := by
  unfold tailWord_3341477
  simp only [CollatzResearch.WordTrace]
  refine ⟨121873678515406982682646685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81249119010271321788431123 121873678515406982682646685)
  ·
    refine ⟨45702629443277618505992507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121873678515406982682646685 45702629443277618505992507)
    ·
      refine ⟨68553944164916427758988761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45702629443277618505992507 68553944164916427758988761)
      ·
        refine ⟨51415458123687320819241571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68553944164916427758988761 51415458123687320819241571)
        ·
          refine ⟨77123187185530981228862357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51415458123687320819241571 77123187185530981228862357)
          ·
            refine ⟨3615149399321764745102923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 77123187185530981228862357 3615149399321764745102923)
            ·
              refine ⟨5422724098982647117654385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3615149399321764745102923 5422724098982647117654385)
              ·
                refine ⟨4067043074236985338240789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5422724098982647117654385 4067043074236985338240789)
                ·
                  refine ⟨190642644104858687730037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4067043074236985338240789 190642644104858687730037)
                  ·
                    rfl

theorem cell23_3341477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 6, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 6, 1, 2, 6].length) (baseStart_3341477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3341477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3341477 prefixEnd_3341477 := by exact prefixLift 3341477
  have htrace : WordTrace (prefixWord ++ tailWord_3341477) baseStart_3341477 baseEnd_3341477 := by
    simpa [prefixWord, tailWord_3341477, baseEnd_3341477] using wordTrace_append hprefix tailTrace_3341477
  have hstable : (prefixWord ++ tailWord_3341477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3341477).length < 2 ^ (prefixWord ++ tailWord_3341477).sum := by decide
  have hdescent : baseEnd_3341477 < baseStart_3341477 := by decide
  rcases family_descends (prefixWord ++ tailWord_3341477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3341487 : List Nat := [1, 1, 2, 1, 2, 3, 3, 3, 3, 1, 3]
def baseStart_3341487 : Nat := 118140960795 + 3341487 * 2 ^ 59
def prefixEnd_3341487 : Nat := 4983230072969 + 3 ^ 40 * 3341487 * 2
def baseEnd_3341487 : Nat := 1715788931750273150445287

theorem tailTrace_3341487 : CollatzResearch.WordTrace tailWord_3341487 prefixEnd_3341487 1715788931750273150445287 := by
  unfold tailWord_3341487
  simp only [CollatzResearch.WordTrace]
  refine ⟨121874043245370754390510715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81249362163580502927007143 121874043245370754390510715)
  ·
    refine ⟨182811064868056131585766073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121874043245370754390510715 182811064868056131585766073)
    ·
      refine ⟨137108298651042098689324555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182811064868056131585766073 137108298651042098689324555)
      ·
        refine ⟨205662447976563148033986833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137108298651042098689324555 205662447976563148033986833)
        ·
          refine ⟨154246835982422361025490125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 205662447976563148033986833 154246835982422361025490125)
          ·
            refine ⟨57842563493408385384558797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 154246835982422361025490125 57842563493408385384558797)
            ·
              refine ⟨21690961310028144519209549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57842563493408385384558797 21690961310028144519209549)
              ·
                refine ⟨8134110491260554194703581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21690961310028144519209549 8134110491260554194703581)
                ·
                  refine ⟨3050291434222707823013843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8134110491260554194703581 3050291434222707823013843)
                  ·
                    refine ⟨4575437151334061734520765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3050291434222707823013843 4575437151334061734520765)
                    ·
                      refine ⟨1715788931750273150445287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4575437151334061734520765 1715788931750273150445287)
                      ·
                        rfl

theorem cell23_3341487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 3, 3, 1, 3].length) (baseStart_3341487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3341487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3341487 prefixEnd_3341487 := by exact prefixLift 3341487
  have htrace : WordTrace (prefixWord ++ tailWord_3341487) baseStart_3341487 baseEnd_3341487 := by
    simpa [prefixWord, tailWord_3341487, baseEnd_3341487] using wordTrace_append hprefix tailTrace_3341487
  have hstable : (prefixWord ++ tailWord_3341487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3341487).length < 2 ^ (prefixWord ++ tailWord_3341487).sum := by decide
  have hdescent : baseEnd_3341487 < baseStart_3341487 := by decide
  rcases family_descends (prefixWord ++ tailWord_3341487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3341497 : List Nat := [1, 2, 1, 4, 1, 3, 1, 2, 1, 5, 2]
def baseStart_3341497 : Nat := 118140960795 + 3341497 * 2 ^ 59
def prefixEnd_3341497 : Nat := 4983230072969 + 3 ^ 40 * 3341497 * 2
def baseEnd_3341497 : Nat := 1715794066556818111320241

theorem tailTrace_3341497 : CollatzResearch.WordTrace tailWord_3341497 prefixEnd_3341497 1715794066556818111320241 := by
  unfold tailWord_3341497
  simp only [CollatzResearch.WordTrace]
  refine ⟨121874407975334526098374745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81249605316889684065583163 121874407975334526098374745)
  ·
    refine ⟨91405805981500894573781059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121874407975334526098374745 91405805981500894573781059)
    ·
      refine ⟨137108708972251341860671589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91405805981500894573781059 137108708972251341860671589)
      ·
        refine ⟨25707882932297126598875923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 137108708972251341860671589 25707882932297126598875923)
        ·
          refine ⟨38561824398445689898313885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25707882932297126598875923 38561824398445689898313885)
          ·
            refine ⟨14460684149417133711867707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38561824398445689898313885 14460684149417133711867707)
            ·
              refine ⟨21691026224125700567801561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14460684149417133711867707 21691026224125700567801561)
              ·
                refine ⟨16268269668094275425851171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21691026224125700567801561 16268269668094275425851171)
                ·
                  refine ⟨24402404502141413138776757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16268269668094275425851171 24402404502141413138776757)
                  ·
                    refine ⟨2287725422075757481760321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 24402404502141413138776757 2287725422075757481760321)
                    ·
                      refine ⟨1715794066556818111320241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2287725422075757481760321 1715794066556818111320241)
                      ·
                        rfl

theorem cell23_3341497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 2, 1, 5, 2].length) (baseStart_3341497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3341497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3341497 prefixEnd_3341497 := by exact prefixLift 3341497
  have htrace : WordTrace (prefixWord ++ tailWord_3341497) baseStart_3341497 baseEnd_3341497 := by
    simpa [prefixWord, tailWord_3341497, baseEnd_3341497] using wordTrace_append hprefix tailTrace_3341497
  have hstable : (prefixWord ++ tailWord_3341497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3341497).length < 2 ^ (prefixWord ++ tailWord_3341497).sum := by decide
  have hdescent : baseEnd_3341497 < baseStart_3341497 := by decide
  rcases family_descends (prefixWord ++ tailWord_3341497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3341527 : List Nat := [1, 1, 3, 2, 1, 2, 4, 3, 1, 1, 4]
def baseStart_3341527 : Nat := 118140960795 + 3341527 * 2 ^ 59
def prefixEnd_3341527 : Nat := 4983230072969 + 3 ^ 40 * 3341527 * 2
def baseEnd_3341527 : Nat := 1715809470976452993945103

theorem tailTrace_3341527 : CollatzResearch.WordTrace tailWord_3341527 prefixEnd_3341527 1715809470976452993945103 := by
  unfold tailWord_3341527
  simp only [CollatzResearch.WordTrace]
  refine ⟨121875502165225841221966835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81250334776817227481311223 121875502165225841221966835)
  ·
    refine ⟨182813253247838761832950253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121875502165225841221966835 182813253247838761832950253)
    ·
      refine ⟨68554969967939535687356345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 182813253247838761832950253 68554969967939535687356345)
      ·
        refine ⟨51416227475954651765517259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68554969967939535687356345 51416227475954651765517259)
        ·
          refine ⟨77124341213931977648275889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51416227475954651765517259 77124341213931977648275889)
          ·
            refine ⟨57843255910448983236206917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77124341213931977648275889 57843255910448983236206917)
            ·
              refine ⟨10845610483209184356788797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57843255910448983236206917 10845610483209184356788797)
              ·
                refine ⟨4067103931203444133795799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10845610483209184356788797 4067103931203444133795799)
                ·
                  refine ⟨6100655896805166200693699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4067103931203444133795799 6100655896805166200693699)
                  ·
                    refine ⟨9150983845207749301040549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6100655896805166200693699 9150983845207749301040549)
                    ·
                      refine ⟨1715809470976452993945103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9150983845207749301040549 1715809470976452993945103)
                      ·
                        rfl

theorem cell23_3341527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 4, 3, 1, 1, 4].length) (baseStart_3341527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3341527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3341527 prefixEnd_3341527 := by exact prefixLift 3341527
  have htrace : WordTrace (prefixWord ++ tailWord_3341527) baseStart_3341527 baseEnd_3341527 := by
    simpa [prefixWord, tailWord_3341527, baseEnd_3341527] using wordTrace_append hprefix tailTrace_3341527
  have hstable : (prefixWord ++ tailWord_3341527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3341527).length < 2 ^ (prefixWord ++ tailWord_3341527).sum := by decide
  have hdescent : baseEnd_3341527 < baseStart_3341527 := by decide
  rcases family_descends (prefixWord ++ tailWord_3341527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3341537 : List Nat := [1, 2, 3, 1, 3, 2, 2, 1, 4, 4]
def baseStart_3341537 : Nat := 118140960795 + 3341537 * 2 ^ 59
def prefixEnd_3341537 : Nat := 4983230072969 + 3 ^ 40 * 3341537 * 2
def baseEnd_3341537 : Nat := 571938201927665984940019

theorem tailTrace_3341537 : CollatzResearch.WordTrace tailWord_3341537 prefixEnd_3341537 571938201927665984940019 := by
  unfold tailWord_3341537
  simp only [CollatzResearch.WordTrace]
  refine ⟨121875866895189612929830865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81250577930126408619887243 121875866895189612929830865)
  ·
    refine ⟨91406900171392209697373149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121875866895189612929830865 91406900171392209697373149)
    ·
      refine ⟨34277587564272078636514931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91406900171392209697373149 34277587564272078636514931)
      ·
        refine ⟨51416381346408117954772397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34277587564272078636514931 51416381346408117954772397)
        ·
          refine ⟨19281143004903044233039649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51416381346408117954772397 19281143004903044233039649)
          ·
            refine ⟨14460857253677283174779737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19281143004903044233039649 14460857253677283174779737)
            ·
              refine ⟨10845642940257962381084803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14460857253677283174779737 10845642940257962381084803)
              ·
                refine ⟨16268464410386943571627205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10845642940257962381084803 16268464410386943571627205)
                ·
                  refine ⟨3050337076947551919680101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16268464410386943571627205 3050337076947551919680101)
                  ·
                    refine ⟨571938201927665984940019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3050337076947551919680101 571938201927665984940019)
                    ·
                      rfl

theorem cell23_3341537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 2, 1, 4, 4].length) (baseStart_3341537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3341537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3341537 prefixEnd_3341537 := by exact prefixLift 3341537
  have htrace : WordTrace (prefixWord ++ tailWord_3341537) baseStart_3341537 baseEnd_3341537 := by
    simpa [prefixWord, tailWord_3341537, baseEnd_3341537] using wordTrace_append hprefix tailTrace_3341537
  have hstable : (prefixWord ++ tailWord_3341537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3341537).length < 2 ^ (prefixWord ++ tailWord_3341537).sum := by decide
  have hdescent : baseEnd_3341537 < baseStart_3341537 := by decide
  rcases family_descends (prefixWord ++ tailWord_3341537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3341540 : List Nat := [2, 3, 1, 1, 1, 2, 3, 2, 1, 1, 6]
def baseStart_3341540 : Nat := 118140960795 + 3341540 * 2 ^ 59
def prefixEnd_3341540 : Nat := 4983230072969 + 3 ^ 40 * 3341540 * 2
def baseEnd_3341540 : Nat := 1715816146224961443082543

theorem tailTrace_3341540 : CollatzResearch.WordTrace tailWord_3341540 prefixEnd_3341540 1715816146224961443082543 := by
  unfold tailWord_3341540
  simp only [CollatzResearch.WordTrace]
  refine ⟨60937988157089372221095037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81250650876119162961460049 60937988157089372221095037)
  ·
    refine ⟨22851745558908514582910639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60937988157089372221095037 22851745558908514582910639)
    ·
      refine ⟨34277618338362771874365959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22851745558908514582910639 34277618338362771874365959)
      ·
        refine ⟨51416427507544157811548939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34277618338362771874365959 51416427507544157811548939)
        ·
          refine ⟨77124641261316236717323409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51416427507544157811548939 77124641261316236717323409)
          ·
            refine ⟨57843480945987177537992557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77124641261316236717323409 57843480945987177537992557)
            ·
              refine ⟨21691305354745191576747209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57843480945987177537992557 21691305354745191576747209)
              ·
                refine ⟨16268479016058893682560407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21691305354745191576747209 16268479016058893682560407)
                ·
                  refine ⟨24402718524088340523840611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16268479016058893682560407 24402718524088340523840611)
                  ·
                    refine ⟨36604077786132510785760917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24402718524088340523840611 36604077786132510785760917)
                    ·
                      refine ⟨1715816146224961443082543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 36604077786132510785760917 1715816146224961443082543)
                      ·
                        rfl

theorem cell23_3341540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 2, 1, 1, 6].length) (baseStart_3341540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3341540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3341540 prefixEnd_3341540 := by exact prefixLift 3341540
  have htrace : WordTrace (prefixWord ++ tailWord_3341540) baseStart_3341540 baseEnd_3341540 := by
    simpa [prefixWord, tailWord_3341540, baseEnd_3341540] using wordTrace_append hprefix tailTrace_3341540
  have hstable : (prefixWord ++ tailWord_3341540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3341540).length < 2 ^ (prefixWord ++ tailWord_3341540).sum := by decide
  have hdescent : baseEnd_3341540 < baseStart_3341540 := by decide
  rcases family_descends (prefixWord ++ tailWord_3341540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3341550 : List Nat := [4, 1, 2, 1, 1, 1, 3, 10]
def baseStart_3341550 : Nat := 118140960795 + 3341550 * 2 ^ 59
def prefixEnd_3341550 : Nat := 4983230072969 + 3 ^ 40 * 3341550 * 2
def baseEnd_3341550 : Nat := 63548936334500237183611

theorem tailTrace_3341550 : CollatzResearch.WordTrace tailWord_3341550 prefixEnd_3341550 63548936334500237183611 := by
  unfold tailWord_3341550
  simp only [CollatzResearch.WordTrace]
  refine ⟨15234542630517814518756763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81250894029428344100036069 15234542630517814518756763)
  ·
    refine ⟨22851813945776721778135145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15234542630517814518756763 22851813945776721778135145)
    ·
      refine ⟨17138860459332541333601359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22851813945776721778135145 17138860459332541333601359)
      ·
        refine ⟨25708290688998812000402039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17138860459332541333601359 25708290688998812000402039)
        ·
          refine ⟨38562436033498218000603059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25708290688998812000402039 38562436033498218000603059)
          ·
            refine ⟨57843654050247327000904589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38562436033498218000603059 57843654050247327000904589)
            ·
              refine ⟨21691370268842747625339221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57843654050247327000904589 21691370268842747625339221)
              ·
                refine ⟨63548936334500237183611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 21691370268842747625339221 63548936334500237183611)
                ·
                  rfl

theorem cell23_3341550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 10].length) (baseStart_3341550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3341550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3341550 prefixEnd_3341550 := by exact prefixLift 3341550
  have htrace : WordTrace (prefixWord ++ tailWord_3341550) baseStart_3341550 baseEnd_3341550 := by
    simpa [prefixWord, tailWord_3341550, baseEnd_3341550] using wordTrace_append hprefix tailTrace_3341550
  have hstable : (prefixWord ++ tailWord_3341550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3341550).length < 2 ^ (prefixWord ++ tailWord_3341550).sum := by decide
  have hdescent : baseEnd_3341550 < baseStart_3341550 := by decide
  rcases family_descends (prefixWord ++ tailWord_3341550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3341564 : List Nat := [2, 2, 2, 1, 5, 1, 1, 1, 3, 2, 3]
def baseStart_3341564 : Nat := 118140960795 + 3341564 * 2 ^ 59
def prefixEnd_3341564 : Nat := 4983230072969 + 3 ^ 40 * 3341564 * 2
def baseEnd_3341564 : Nat := 1715828469760669349182433

theorem tailTrace_3341564 : CollatzResearch.WordTrace tailWord_3341564 prefixEnd_3341564 1715828469760669349182433 := by
  unfold tailWord_3341564
  simp only [CollatzResearch.WordTrace]
  refine ⟨60938425833045898270531873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81251234444061197694042497 60938425833045898270531873)
  ·
    refine ⟨45703819374784423702898905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60938425833045898270531873 45703819374784423702898905)
    ·
      refine ⟨34277864531088317777174179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45703819374784423702898905 34277864531088317777174179)
      ·
        refine ⟨51416796796632476665761269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34277864531088317777174179 51416796796632476665761269)
        ·
          refine ⟨4820324699684294687415119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 51416796796632476665761269 4820324699684294687415119)
          ·
            refine ⟨7230487049526442031122679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4820324699684294687415119 7230487049526442031122679)
            ·
              refine ⟨10845730574289663046684019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7230487049526442031122679 10845730574289663046684019)
              ·
                refine ⟨16268595861434494570026029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10845730574289663046684019 16268595861434494570026029)
                ·
                  refine ⟨6100723448037935463759761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16268595861434494570026029 6100723448037935463759761)
                  ·
                    refine ⟨4575542586028451597819821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6100723448037935463759761 4575542586028451597819821)
                    ·
                      refine ⟨1715828469760669349182433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4575542586028451597819821 1715828469760669349182433)
                      ·
                        rfl

theorem cell23_3341564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 1, 1, 3, 2, 3].length) (baseStart_3341564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3341564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3341564 prefixEnd_3341564 := by exact prefixLift 3341564
  have htrace : WordTrace (prefixWord ++ tailWord_3341564) baseStart_3341564 baseEnd_3341564 := by
    simpa [prefixWord, tailWord_3341564, baseEnd_3341564] using wordTrace_append hprefix tailTrace_3341564
  have hstable : (prefixWord ++ tailWord_3341564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3341564).length < 2 ^ (prefixWord ++ tailWord_3341564).sum := by decide
  have hdescent : baseEnd_3341564 < baseStart_3341564 := by decide
  rcases family_descends (prefixWord ++ tailWord_3341564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3341577 : List Nat := [1, 2, 1, 1, 3, 3, 3, 2, 1, 3, 3]
def baseStart_3341577 : Nat := 118140960795 + 3341577 * 2 ^ 59
def prefixEnd_3341577 : Nat := 4983230072969 + 3 ^ 40 * 3341577 * 2
def baseEnd_3341577 : Nat := 1715835145009177798319873

theorem tailTrace_3341577 : CollatzResearch.WordTrace tailWord_3341577 prefixEnd_3341577 1715835145009177798319873 := by
  unfold tailWord_3341577
  simp only [CollatzResearch.WordTrace]
  refine ⟨121877325815044699761286985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81251550543363133174191323 121877325815044699761286985)
  ·
    refine ⟨91407994361283524820965239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121877325815044699761286985 91407994361283524820965239)
    ·
      refine ⟨137111991541925287231447859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91407994361283524820965239 137111991541925287231447859)
      ·
        refine ⟨205667987312887930847171789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137111991541925287231447859 205667987312887930847171789)
        ·
          refine ⟨77125495242332974067689421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 205667987312887930847171789 77125495242332974067689421)
          ·
            refine ⟨28922060715874865275383533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77125495242332974067689421 28922060715874865275383533)
            ·
              refine ⟨10845772768453074478268825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28922060715874865275383533 10845772768453074478268825)
              ·
                refine ⟨8134329576339805858701619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10845772768453074478268825 8134329576339805858701619)
                ·
                  refine ⟨12201494364509708788052429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8134329576339805858701619 12201494364509708788052429)
                  ·
                    refine ⟨4575560386691140795519661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12201494364509708788052429 4575560386691140795519661)
                    ·
                      refine ⟨1715835145009177798319873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4575560386691140795519661 1715835145009177798319873)
                      ·
                        rfl

theorem cell23_3341577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 3, 2, 1, 3, 3].length) (baseStart_3341577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3341577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3341577 prefixEnd_3341577 := by exact prefixLift 3341577
  have htrace : WordTrace (prefixWord ++ tailWord_3341577) baseStart_3341577 baseEnd_3341577 := by
    simpa [prefixWord, tailWord_3341577, baseEnd_3341577] using wordTrace_append hprefix tailTrace_3341577
  have hstable : (prefixWord ++ tailWord_3341577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3341577).length < 2 ^ (prefixWord ++ tailWord_3341577).sum := by decide
  have hdescent : baseEnd_3341577 < baseStart_3341577 := by decide
  rcases family_descends (prefixWord ++ tailWord_3341577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3341597 : List Nat := [1, 4, 2, 3, 1, 1, 1, 1, 2, 7]
def baseStart_3341597 : Nat := 118140960795 + 3341597 * 2 ^ 59
def prefixEnd_3341597 : Nat := 4983230072969 + 3 ^ 40 * 3341597 * 2
def baseEnd_3341597 : Nat := 571948471540755906689927

theorem tailTrace_3341597 : CollatzResearch.WordTrace tailWord_3341597 prefixEnd_3341597 571948471540755906689927 := by
  unfold tailWord_3341597
  simp only [CollatzResearch.WordTrace]
  refine ⟨121878055274972243177015045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81252036849981495451343363 121878055274972243177015045)
  ·
    refine ⟨22852135364057295595690321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 121878055274972243177015045 22852135364057295595690321)
    ·
      refine ⟨17139101523042971696767741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22852135364057295595690321 17139101523042971696767741)
      ·
        refine ⟨6427163071141114386287903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17139101523042971696767741 6427163071141114386287903)
        ·
          refine ⟨9640744606711671579431855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6427163071141114386287903 9640744606711671579431855)
          ·
            refine ⟨14461116910067507369147783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9640744606711671579431855 14461116910067507369147783)
            ·
              refine ⟨21691675365101261053721675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14461116910067507369147783 21691675365101261053721675)
              ·
                refine ⟨32537513047651891580582513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21691675365101261053721675 32537513047651891580582513)
                ·
                  refine ⟨24403134785738918685436885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32537513047651891580582513 24403134785738918685436885)
                  ·
                    refine ⟨571948471540755906689927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24403134785738918685436885 571948471540755906689927)
                    ·
                      rfl

theorem cell23_3341597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 1, 2, 7].length) (baseStart_3341597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3341597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3341597 prefixEnd_3341597 := by exact prefixLift 3341597
  have htrace : WordTrace (prefixWord ++ tailWord_3341597) baseStart_3341597 baseEnd_3341597 := by
    simpa [prefixWord, tailWord_3341597, baseEnd_3341597] using wordTrace_append hprefix tailTrace_3341597
  have hstable : (prefixWord ++ tailWord_3341597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3341597).length < 2 ^ (prefixWord ++ tailWord_3341597).sum := by decide
  have hdescent : baseEnd_3341597 < baseStart_3341597 := by decide
  rcases family_descends (prefixWord ++ tailWord_3341597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3341604 : List Nat := [2, 3, 1, 3, 1, 1, 1, 1, 5, 3, 2]
def baseStart_3341604 : Nat := 118140960795 + 3341604 * 2 ^ 59
def prefixEnd_3341604 : Nat := 4983230072969 + 3 ^ 40 * 3341604 * 2
def baseEnd_3341604 : Nat := 1715849008986849192682249

theorem tailTrace_3341604 : CollatzResearch.WordTrace tailWord_3341604 prefixEnd_3341604 1715849008986849192682249 := by
  unfold tailWord_3341604
  simp only [CollatzResearch.WordTrace]
  refine ⟨60939155292973441686259933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81252207057297922248346577 60939155292973441686259933)
  ·
    refine ⟨22852183234865040632347475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60939155292973441686259933 22852183234865040632347475)
    ·
      refine ⟨34278274852297560948521213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22852183234865040632347475 34278274852297560948521213)
      ·
        refine ⟨12854353069611585355695455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34278274852297560948521213 12854353069611585355695455)
        ·
          refine ⟨19281529604417378033543183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12854353069611585355695455 19281529604417378033543183)
          ·
            refine ⟨28922294406626067050314775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19281529604417378033543183 28922294406626067050314775)
            ·
              refine ⟨43383441609939100575472163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28922294406626067050314775 43383441609939100575472163)
              ·
                refine ⟨65075162414908650863208245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43383441609939100575472163 65075162414908650863208245)
                ·
                  refine ⟨6100796476397686018425773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 65075162414908650863208245 6100796476397686018425773)
                  ·
                    refine ⟨2287798678649132256909665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6100796476397686018425773 2287798678649132256909665)
                    ·
                      refine ⟨1715849008986849192682249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2287798678649132256909665 1715849008986849192682249)
                      ·
                        rfl

theorem cell23_3341604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 1, 5, 3, 2].length) (baseStart_3341604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3341604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3341604 prefixEnd_3341604 := by exact prefixLift 3341604
  have htrace : WordTrace (prefixWord ++ tailWord_3341604) baseStart_3341604 baseEnd_3341604 := by
    simpa [prefixWord, tailWord_3341604, baseEnd_3341604] using wordTrace_append hprefix tailTrace_3341604
  have hstable : (prefixWord ++ tailWord_3341604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3341604).length < 2 ^ (prefixWord ++ tailWord_3341604).sum := by decide
  have hdescent : baseEnd_3341604 < baseStart_3341604 := by decide
  rcases family_descends (prefixWord ++ tailWord_3341604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3341640 : List Nat := [2, 1, 3, 1, 1, 2, 1, 1, 11]
def baseStart_3341640 : Nat := 118140960795 + 3341640 * 2 ^ 59
def prefixEnd_3341640 : Nat := 4983230072969 + 3 ^ 40 * 3341640 * 2
def baseEnd_3341640 : Nat := 190651943810045672425787

theorem tailTrace_3341640 : CollatzResearch.WordTrace tailWord_3341640 prefixEnd_3341640 190651943810045672425787 := by
  unfold tailWord_3341640
  simp only [CollatzResearch.WordTrace]
  refine ⟨60939811806908230760415187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81253082409210974347220249 60939811806908230760415187)
  ·
    refine ⟨91409717710362346140622781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60939811806908230760415187 91409717710362346140622781)
    ·
      refine ⟨34278644141385879802733543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91409717710362346140622781 34278644141385879802733543)
      ·
        refine ⟨51417966212078819704100315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34278644141385879802733543 51417966212078819704100315)
        ·
          refine ⟨77126949318118229556150473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51417966212078819704100315 77126949318118229556150473)
          ·
            refine ⟨57845211988588672167112855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77126949318118229556150473 57845211988588672167112855)
            ·
              refine ⟨86767817982883008250669283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57845211988588672167112855 86767817982883008250669283)
              ·
                refine ⟨130151726974324512376003925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86767817982883008250669283 130151726974324512376003925)
                ·
                  refine ⟨190651943810045672425787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 130151726974324512376003925 190651943810045672425787)
                  ·
                    rfl

theorem cell23_3341640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 1, 11].length) (baseStart_3341640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3341640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3341640 prefixEnd_3341640 := by exact prefixLift 3341640
  have htrace : WordTrace (prefixWord ++ tailWord_3341640) baseStart_3341640 baseEnd_3341640 := by
    simpa [prefixWord, tailWord_3341640, baseEnd_3341640] using wordTrace_append hprefix tailTrace_3341640
  have hstable : (prefixWord ++ tailWord_3341640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3341640).length < 2 ^ (prefixWord ++ tailWord_3341640).sum := by decide
  have hdescent : baseEnd_3341640 < baseStart_3341640 := by decide
  rcases family_descends (prefixWord ++ tailWord_3341640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3341687 : List Nat := [1, 1, 3, 1, 1, 2, 4, 3, 2, 5]
def baseStart_3341687 : Nat := 118140960795 + 3341687 * 2 ^ 59
def prefixEnd_3341687 : Nat := 4983230072969 + 3 ^ 40 * 3341687 * 2
def baseEnd_3341687 : Nat := 571963875960390789314789

theorem tailTrace_3341687 : CollatzResearch.WordTrace tailWord_3341687 prefixEnd_3341687 571963875960390789314789 := by
  unfold tailWord_3341687
  simp only [CollatzResearch.WordTrace]
  refine ⟨121881337844646188547791315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81254225229764125698527543 121881337844646188547791315)
  ·
    refine ⟨182822006766969282821686973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121881337844646188547791315 182822006766969282821686973)
    ·
      refine ⟨68558252537613481058132615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 182822006766969282821686973 68558252537613481058132615)
      ·
        refine ⟨102837378806420221587198923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68558252537613481058132615 102837378806420221587198923)
        ·
          refine ⟨154256068209630332380798385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102837378806420221587198923 154256068209630332380798385)
          ·
            refine ⟨115692051157222749285598789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 154256068209630332380798385 115692051157222749285598789)
            ·
              refine ⟨21692259591979265491049773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 115692051157222749285598789 21692259591979265491049773)
              ·
                refine ⟨8134597346992224559143665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21692259591979265491049773 8134597346992224559143665)
                ·
                  refine ⟨6100948010244168419357749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8134597346992224559143665 6100948010244168419357749)
                  ·
                    refine ⟨571963875960390789314789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6100948010244168419357749 571963875960390789314789)
                    ·
                      rfl

theorem cell23_3341687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 2, 5].length) (baseStart_3341687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3341687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3341687 prefixEnd_3341687 := by exact prefixLift 3341687
  have htrace : WordTrace (prefixWord ++ tailWord_3341687) baseStart_3341687 baseEnd_3341687 := by
    simpa [prefixWord, tailWord_3341687, baseEnd_3341687] using wordTrace_append hprefix tailTrace_3341687
  have hstable : (prefixWord ++ tailWord_3341687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3341687).length < 2 ^ (prefixWord ++ tailWord_3341687).sum := by decide
  have hdescent : baseEnd_3341687 < baseStart_3341687 := by decide
  rcases family_descends (prefixWord ++ tailWord_3341687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3341704 : List Nat := [2, 1, 3, 3, 1, 3, 1, 2, 2, 5]
def baseStart_3341704 : Nat := 118140960795 + 3341704 * 2 ^ 59
def prefixEnd_3341704 : Nat := 4983230072969 + 3 ^ 40 * 3341704 * 2
def baseEnd_3341704 : Nat := 571966785684099600477263

theorem tailTrace_3341704 : CollatzResearch.WordTrace tailWord_3341704 prefixEnd_3341704 571966785684099600477263 := by
  unfold tailWord_3341704
  simp only [CollatzResearch.WordTrace]
  refine ⟨60940978942792300225580083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81254638590389733634106777 60940978942792300225580083)
  ·
    refine ⟨91411468414188450338370125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60940978942792300225580083 91411468414188450338370125)
    ·
      refine ⟨34279300655320668876888797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91411468414188450338370125 34279300655320668876888797)
      ·
        refine ⟨12854737745745250828833299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34279300655320668876888797 12854737745745250828833299)
        ·
          refine ⟨19282106618617876243249949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12854737745745250828833299 19282106618617876243249949)
          ·
            refine ⟨7230789981981703591218731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19282106618617876243249949 7230789981981703591218731)
            ·
              refine ⟨10846184972972555386828097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7230789981981703591218731 10846184972972555386828097)
              ·
                refine ⟨8134638729729416540121073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10846184972972555386828097 8134638729729416540121073)
                ·
                  refine ⟨6100979047297062405090805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8134638729729416540121073 6100979047297062405090805)
                  ·
                    refine ⟨571966785684099600477263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6100979047297062405090805 571966785684099600477263)
                    ·
                      rfl

theorem cell23_3341704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 1, 2, 2, 5].length) (baseStart_3341704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3341704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3341704 prefixEnd_3341704 := by exact prefixLift 3341704
  have htrace : WordTrace (prefixWord ++ tailWord_3341704) baseStart_3341704 baseEnd_3341704 := by
    simpa [prefixWord, tailWord_3341704, baseEnd_3341704] using wordTrace_append hprefix tailTrace_3341704
  have hstable : (prefixWord ++ tailWord_3341704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3341704).length < 2 ^ (prefixWord ++ tailWord_3341704).sum := by decide
  have hdescent : baseEnd_3341704 < baseStart_3341704 := by decide
  rcases family_descends (prefixWord ++ tailWord_3341704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3341741 : List Nat := [1, 5, 2, 2, 1, 1, 1, 3, 2, 1, 4]
def baseStart_3341741 : Nat := 118140960795 + 3341741 * 2 ^ 59
def prefixEnd_3341741 : Nat := 4983230072969 + 3 ^ 40 * 3341741 * 2
def baseEnd_3341741 : Nat := 1715919355836515156669119

theorem tailTrace_3341741 : CollatzResearch.WordTrace tailWord_3341741 prefixEnd_3341741 1715919355836515156669119 := by
  unfold tailWord_3341741
  simp only [CollatzResearch.WordTrace]
  refine ⟨121883307386450555770257077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81255538257633703846838051 121883307386450555770257077)
  ·
    refine ⟨11426560067479739603461601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 121883307386450555770257077 11426560067479739603461601)
    ·
      refine ⟨8569920050609804702596201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11426560067479739603461601 8569920050609804702596201)
      ·
        refine ⟨6427440037957353526947151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8569920050609804702596201 6427440037957353526947151)
        ·
          refine ⟨9641160056936030290420727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6427440037957353526947151 9641160056936030290420727)
          ·
            refine ⟨14461740085404045435631091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9641160056936030290420727 14461740085404045435631091)
            ·
              refine ⟨21692610128106068153446637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14461740085404045435631091 21692610128106068153446637)
              ·
                refine ⟨8134728798039775557542489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21692610128106068153446637 8134728798039775557542489)
                ·
                  refine ⟨6101046598529831668156867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8134728798039775557542489 6101046598529831668156867)
                  ·
                    refine ⟨9151569897794747502235301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6101046598529831668156867 9151569897794747502235301)
                    ·
                      refine ⟨1715919355836515156669119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9151569897794747502235301 1715919355836515156669119)
                      ·
                        rfl

theorem cell23_3341741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 3, 2, 1, 4].length) (baseStart_3341741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3341741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3341741 prefixEnd_3341741 := by exact prefixLift 3341741
  have htrace : WordTrace (prefixWord ++ tailWord_3341741) baseStart_3341741 baseEnd_3341741 := by
    simpa [prefixWord, tailWord_3341741, baseEnd_3341741] using wordTrace_append hprefix tailTrace_3341741
  have hstable : (prefixWord ++ tailWord_3341741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3341741).length < 2 ^ (prefixWord ++ tailWord_3341741).sum := by decide
  have hdescent : baseEnd_3341741 < baseStart_3341741 := by decide
  rcases family_descends (prefixWord ++ tailWord_3341741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3341751 : List Nat := [1, 1, 3, 1, 3, 2, 2, 5, 1, 4]
def baseStart_3341751 : Nat := 118140960795 + 3341751 * 2 ^ 59
def prefixEnd_3341751 : Nat := 4983230072969 + 3 ^ 40 * 3341751 * 2
def baseEnd_3341751 : Nat := 571974830214353372514691

theorem tailTrace_3341751 : CollatzResearch.WordTrace tailWord_3341751 prefixEnd_3341751 571974830214353372514691 := by
  unfold tailWord_3341751
  simp only [CollatzResearch.WordTrace]
  refine ⟨121883672116414327478121107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81255781410942884985414071 121883672116414327478121107)
  ·
    refine ⟨182825508174621491217181661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121883672116414327478121107 182825508174621491217181661)
    ·
      refine ⟨68559565565483059206443123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 182825508174621491217181661 68559565565483059206443123)
      ·
        refine ⟨102839348348224588809664685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68559565565483059206443123 102839348348224588809664685)
        ·
          refine ⟨38564755630584220803624257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102839348348224588809664685 38564755630584220803624257)
          ·
            refine ⟨28923566722938165602718193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38564755630584220803624257 28923566722938165602718193)
            ·
              refine ⟨21692675042203624202038645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28923566722938165602718193 21692675042203624202038645)
              ·
                refine ⟨2033688285206589768941123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21692675042203624202038645 2033688285206589768941123)
                ·
                  refine ⟨3050532427809884653411685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2033688285206589768941123 3050532427809884653411685)
                  ·
                    refine ⟨571974830214353372514691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3050532427809884653411685 571974830214353372514691)
                    ·
                      rfl

theorem cell23_3341751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 5, 1, 4].length) (baseStart_3341751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3341751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3341751 prefixEnd_3341751 := by exact prefixLift 3341751
  have htrace : WordTrace (prefixWord ++ tailWord_3341751) baseStart_3341751 baseEnd_3341751 := by
    simpa [prefixWord, tailWord_3341751, baseEnd_3341751] using wordTrace_append hprefix tailTrace_3341751
  have hstable : (prefixWord ++ tailWord_3341751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3341751).length < 2 ^ (prefixWord ++ tailWord_3341751).sum := by decide
  have hdescent : baseEnd_3341751 < baseStart_3341751 := by decide
  rcases family_descends (prefixWord ++ tailWord_3341751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3341767 : List Nat := [1, 1, 4, 1, 1, 3, 2, 1, 1, 2, 6]
def baseStart_3341767 : Nat := 118140960795 + 3341767 * 2 ^ 59
def prefixEnd_3341767 : Nat := 4983230072969 + 3 ^ 40 * 3341767 * 2
def baseEnd_3341767 : Nat := 1715932706333532054943999

theorem tailTrace_3341767 : CollatzResearch.WordTrace tailWord_3341767 prefixEnd_3341767 1715932706333532054943999 := by
  unfold tailWord_3341767
  simp only [CollatzResearch.WordTrace]
  refine ⟨121884255684356362210703555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81256170456237574807135703 121884255684356362210703555)
  ·
    refine ⟨182826383526534543316055333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121884255684356362210703555 182826383526534543316055333)
    ·
      refine ⟨34279946911225226871760375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 182826383526534543316055333 34279946911225226871760375)
      ·
        refine ⟨51419920366837840307640563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34279946911225226871760375 51419920366837840307640563)
        ·
          refine ⟨77129880550256760461460845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51419920366837840307640563 77129880550256760461460845)
          ·
            refine ⟨28923705206346285173047817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77129880550256760461460845 28923705206346285173047817)
            ·
              refine ⟨21692778904759713879785863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28923705206346285173047817 21692778904759713879785863)
              ·
                refine ⟨32539168357139570819678795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21692778904759713879785863 32539168357139570819678795)
                ·
                  refine ⟨48808752535709356229518193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32539168357139570819678795 48808752535709356229518193)
                  ·
                    refine ⟨36606564401782017172138645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 48808752535709356229518193 36606564401782017172138645)
                    ·
                      refine ⟨1715932706333532054943999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 36606564401782017172138645 1715932706333532054943999)
                      ·
                        rfl

theorem cell23_3341767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 1, 1, 2, 6].length) (baseStart_3341767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3341767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3341767 prefixEnd_3341767 := by exact prefixLift 3341767
  have htrace : WordTrace (prefixWord ++ tailWord_3341767) baseStart_3341767 baseEnd_3341767 := by
    simpa [prefixWord, tailWord_3341767, baseEnd_3341767] using wordTrace_append hprefix tailTrace_3341767
  have hstable : (prefixWord ++ tailWord_3341767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3341767).length < 2 ^ (prefixWord ++ tailWord_3341767).sum := by decide
  have hdescent : baseEnd_3341767 < baseStart_3341767 := by decide
  rcases family_descends (prefixWord ++ tailWord_3341767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3341791 : List Nat := [1, 1, 2, 3, 3, 1, 3, 2, 3, 1, 3]
def baseStart_3341791 : Nat := 118140960795 + 3341791 * 2 ^ 59
def prefixEnd_3341791 : Nat := 4983230072969 + 3 ^ 40 * 3341791 * 2
def baseEnd_3341791 : Nat := 1715945029869239961043889

theorem tailTrace_3341791 : CollatzResearch.WordTrace tailWord_3341791 prefixEnd_3341791 1715945029869239961043889 := by
  unfold tailWord_3341791
  simp only [CollatzResearch.WordTrace]
  refine ⟨121885131036269414309577227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81256754024179609539718151 121885131036269414309577227)
  ·
    refine ⟨182827696554404121464365841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121885131036269414309577227 182827696554404121464365841)
    ·
      refine ⟨137120772415803091098274381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182827696554404121464365841 137120772415803091098274381)
      ·
        refine ⟨51420289655926159161852893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 137120772415803091098274381 51420289655926159161852893)
        ·
          refine ⟨19282608620972309685694835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51420289655926159161852893 19282608620972309685694835)
          ·
            refine ⟨28923912931458464528542253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19282608620972309685694835 28923912931458464528542253)
            ·
              refine ⟨10846467349296924198203345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28923912931458464528542253 10846467349296924198203345)
              ·
                refine ⟨8134850511972693148652509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10846467349296924198203345 8134850511972693148652509)
                ·
                  refine ⟨3050568941989759930744691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8134850511972693148652509 3050568941989759930744691)
                  ·
                    refine ⟨4575853412984639896117037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3050568941989759930744691 4575853412984639896117037)
                    ·
                      refine ⟨1715945029869239961043889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4575853412984639896117037 1715945029869239961043889)
                      ·
                        rfl

theorem cell23_3341791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 3, 2, 3, 1, 3].length) (baseStart_3341791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3341791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3341791 prefixEnd_3341791 := by exact prefixLift 3341791
  have htrace : WordTrace (prefixWord ++ tailWord_3341791) baseStart_3341791 baseEnd_3341791 := by
    simpa [prefixWord, tailWord_3341791, baseEnd_3341791] using wordTrace_append hprefix tailTrace_3341791
  have hstable : (prefixWord ++ tailWord_3341791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3341791).length < 2 ^ (prefixWord ++ tailWord_3341791).sum := by decide
  have hdescent : baseEnd_3341791 < baseStart_3341791 := by decide
  rcases family_descends (prefixWord ++ tailWord_3341791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3341808 : List Nat := [2, 1, 1, 1, 3, 4, 1, 5, 1, 1, 3]
def baseStart_3341808 : Nat := 118140960795 + 3341808 * 2 ^ 59
def prefixEnd_3341808 : Nat := 4983230072969 + 3 ^ 40 * 3341808 * 2
def baseEnd_3341808 : Nat := 1715953759040366394531311

theorem tailTrace_3341808 : CollatzResearch.WordTrace tailWord_3341808 prefixEnd_3341808 1715953759040366394531311 := by
  unfold tailWord_3341808
  simp only [CollatzResearch.WordTrace]
  refine ⟨60942875538603913106473039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81257167384805217475297385 60942875538603913106473039)
  ·
    refine ⟨91414313307905869659709559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60942875538603913106473039 91414313307905869659709559)
    ·
      refine ⟨137121469961858804489564339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91414313307905869659709559 137121469961858804489564339)
      ·
        refine ⟨205682204942788206734346509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137121469961858804489564339 205682204942788206734346509)
        ·
          refine ⟨77130826853545577525379941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 205682204942788206734346509 77130826853545577525379941)
          ·
            refine ⟨14462030035039795786008739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 77130826853545577525379941 14462030035039795786008739)
            ·
              refine ⟨21693045052559693679013109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14462030035039795786008739 21693045052559693679013109)
              ·
                refine ⟨2033722973677471282407479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21693045052559693679013109 2033722973677471282407479)
                ·
                  refine ⟨3050584460516206923611219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2033722973677471282407479 3050584460516206923611219)
                  ·
                    refine ⟨4575876690774310385416829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3050584460516206923611219 4575876690774310385416829)
                    ·
                      refine ⟨1715953759040366394531311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4575876690774310385416829 1715953759040366394531311)
                      ·
                        rfl

theorem cell23_3341808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 5, 1, 1, 3].length) (baseStart_3341808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3341808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3341808 prefixEnd_3341808 := by exact prefixLift 3341808
  have htrace : WordTrace (prefixWord ++ tailWord_3341808) baseStart_3341808 baseEnd_3341808 := by
    simpa [prefixWord, tailWord_3341808, baseEnd_3341808] using wordTrace_append hprefix tailTrace_3341808
  have hstable : (prefixWord ++ tailWord_3341808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3341808).length < 2 ^ (prefixWord ++ tailWord_3341808).sum := by decide
  have hdescent : baseEnd_3341808 < baseStart_3341808 := by decide
  rcases family_descends (prefixWord ++ tailWord_3341808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3341834 : List Nat := [3, 1, 2, 2, 2, 2, 1, 1, 3, 1, 5]
def baseStart_3341834 : Nat := 118140960795 + 3341834 * 2 ^ 59
def prefixEnd_3341834 : Nat := 4983230072969 + 3 ^ 40 * 3341834 * 2
def baseEnd_3341834 : Nat := 1715967109537383292806191

theorem tailTrace_3341834 : CollatzResearch.WordTrace tailWord_3341834 prefixEnd_3341834 1715967109537383292806191 := by
  unfold tailWord_3341834
  simp only [CollatzResearch.WordTrace]
  refine ⟨30471674843778408163348139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81257799583409088435595037 30471674843778408163348139)
  ·
    refine ⟨45707512265667612245022209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30471674843778408163348139 45707512265667612245022209)
    ·
      refine ⟨34280634199250709183766657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45707512265667612245022209 34280634199250709183766657)
      ·
        refine ⟨25710475649438031887824993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34280634199250709183766657 25710475649438031887824993)
        ·
          refine ⟨19282856737078523915868745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25710475649438031887824993 19282856737078523915868745)
          ·
            refine ⟨14462142552808892936901559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19282856737078523915868745 14462142552808892936901559)
            ·
              refine ⟨21693213829213339405352339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14462142552808892936901559 21693213829213339405352339)
              ·
                refine ⟨32539820743820009108028509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21693213829213339405352339 32539820743820009108028509)
                ·
                  refine ⟨12202432778932503415510691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32539820743820009108028509 12202432778932503415510691)
                  ·
                    refine ⟨18303649168398755123266037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12202432778932503415510691 18303649168398755123266037)
                    ·
                      refine ⟨1715967109537383292806191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18303649168398755123266037 1715967109537383292806191)
                      ·
                        rfl

theorem cell23_3341834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 1, 3, 1, 5].length) (baseStart_3341834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3341834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3341834 prefixEnd_3341834 := by exact prefixLift 3341834
  have htrace : WordTrace (prefixWord ++ tailWord_3341834) baseStart_3341834 baseEnd_3341834 := by
    simpa [prefixWord, tailWord_3341834, baseEnd_3341834] using wordTrace_append hprefix tailTrace_3341834
  have hstable : (prefixWord ++ tailWord_3341834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3341834).length < 2 ^ (prefixWord ++ tailWord_3341834).sum := by decide
  have hdescent : baseEnd_3341834 < baseStart_3341834 := by decide
  rcases family_descends (prefixWord ++ tailWord_3341834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3341848 : List Nat := [2, 1, 2, 3, 4, 1, 2, 2, 1, 1, 4]
def baseStart_3341848 : Nat := 118140960795 + 3341848 * 2 ^ 59
def prefixEnd_3341848 : Nat := 4983230072969 + 3 ^ 40 * 3341848 * 2
def baseEnd_3341848 : Nat := 1715974298266546238031127

theorem tailTrace_3341848 : CollatzResearch.WordTrace tailWord_3341848 prefixEnd_3341848 1715974298266546238031127 := by
  unfold tailWord_3341848
  simp only [CollatzResearch.WordTrace]
  refine ⟨60943604998531456522201099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81258139998041942029601465 60943604998531456522201099)
  ·
    refine ⟨91415407497797184783301649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60943604998531456522201099 91415407497797184783301649)
    ·
      refine ⟨68561555623347888587476237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91415407497797184783301649 68561555623347888587476237)
      ·
        refine ⟨25710583358755458220303589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68561555623347888587476237 25710583358755458220303589)
        ·
          refine ⟨4820734379766648416306923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25710583358755458220303589 4820734379766648416306923)
          ·
            refine ⟨7231101569649972624460385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4820734379766648416306923 7231101569649972624460385)
            ·
              refine ⟨5423326177237479468345289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7231101569649972624460385 5423326177237479468345289)
              ·
                refine ⟨4067494632928109601258967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5423326177237479468345289 4067494632928109601258967)
                ·
                  refine ⟨6101241949392164401888451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4067494632928109601258967 6101241949392164401888451)
                  ·
                    refine ⟨9151862924088246602832677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6101241949392164401888451 9151862924088246602832677)
                    ·
                      refine ⟨1715974298266546238031127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9151862924088246602832677 1715974298266546238031127)
                      ·
                        rfl

theorem cell23_3341848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 2, 2, 1, 1, 4].length) (baseStart_3341848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3341848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3341848 prefixEnd_3341848 := by exact prefixLift 3341848
  have htrace : WordTrace (prefixWord ++ tailWord_3341848) baseStart_3341848 baseEnd_3341848 := by
    simpa [prefixWord, tailWord_3341848, baseEnd_3341848] using wordTrace_append hprefix tailTrace_3341848
  have hstable : (prefixWord ++ tailWord_3341848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3341848).length < 2 ^ (prefixWord ++ tailWord_3341848).sum := by decide
  have hdescent : baseEnd_3341848 < baseStart_3341848 := by decide
  rcases family_descends (prefixWord ++ tailWord_3341848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3341867 : List Nat := [1, 1, 1, 1, 2, 1, 3, 1, 3, 9]
def baseStart_3341867 : Nat := 118140960795 + 3341867 * 2 ^ 59
def prefixEnd_3341867 : Nat := 4983230072969 + 3 ^ 40 * 3341867 * 2
def baseEnd_3341867 : Nat := 571994684799660554564513

theorem tailTrace_3341867 : CollatzResearch.WordTrace tailWord_3341867 prefixEnd_3341867 571994684799660554564513 := by
  unfold tailWord_3341867
  simp only [CollatzResearch.WordTrace]
  refine ⟨121887902983994079289343855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81258601989329386192895903 121887902983994079289343855)
  ·
    refine ⟨182831854475991118934015783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121887902983994079289343855 182831854475991118934015783)
    ·
      refine ⟨274247781713986678401023675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182831854475991118934015783 274247781713986678401023675)
      ·
        refine ⟨411371672570980017601535513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 274247781713986678401023675 411371672570980017601535513)
        ·
          refine ⟨308528754428235013201151635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 411371672570980017601535513 308528754428235013201151635)
          ·
            refine ⟨462793131642352519801727453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 308528754428235013201151635 462793131642352519801727453)
            ·
              refine ⟨173547424365882194925647795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 462793131642352519801727453 173547424365882194925647795)
              ·
                refine ⟨260321136548823292388471693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 173547424365882194925647795 260321136548823292388471693)
                ·
                  refine ⟨97620426205808734645676885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 260321136548823292388471693 97620426205808734645676885)
                  ·
                    refine ⟨571994684799660554564513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 97620426205808734645676885 571994684799660554564513)
                    ·
                      rfl

theorem cell23_3341867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 1, 3, 9].length) (baseStart_3341867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3341867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3341867 prefixEnd_3341867 := by exact prefixLift 3341867
  have htrace : WordTrace (prefixWord ++ tailWord_3341867) baseStart_3341867 baseEnd_3341867 := by
    simpa [prefixWord, tailWord_3341867, baseEnd_3341867] using wordTrace_append hprefix tailTrace_3341867
  have hstable : (prefixWord ++ tailWord_3341867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3341867).length < 2 ^ (prefixWord ++ tailWord_3341867).sum := by decide
  have hdescent : baseEnd_3341867 < baseStart_3341867 := by decide
  rcases family_descends (prefixWord ++ tailWord_3341867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3341882 : List Nat := [3, 1, 1, 1, 3, 2, 5, 2, 1, 2, 2]
def baseStart_3341882 : Nat := 118140960795 + 3341882 * 2 ^ 59
def prefixEnd_3341882 : Nat := 4983230072969 + 3 ^ 40 * 3341882 * 2
def baseEnd_3341882 : Nat := 1715991756608799105005971

theorem tailTrace_3341882 : CollatzResearch.WordTrace tailWord_3341882 prefixEnd_3341882 1715991756608799105005971 := by
  unfold tailWord_3341882
  simp only [CollatzResearch.WordTrace]
  refine ⟨30472112519734934212784975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81258966719293157900759933 30472112519734934212784975)
  ·
    refine ⟨45708168779602401319177463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30472112519734934212784975 45708168779602401319177463)
    ·
      refine ⟨68562253169403601978766195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45708168779602401319177463 68562253169403601978766195)
      ·
        refine ⟨102843379754105402968149293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68562253169403601978766195 102843379754105402968149293)
        ·
          refine ⟨38566267407789526113055985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102843379754105402968149293 38566267407789526113055985)
          ·
            refine ⟨28924700555842144584791989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38566267407789526113055985 28924700555842144584791989)
            ·
              refine ⟨2711690677110201054824249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28924700555842144584791989 2711690677110201054824249)
              ·
                refine ⟨2033768007832650791118187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2711690677110201054824249 2033768007832650791118187)
                ·
                  refine ⟨3050652011748976186677281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2033768007832650791118187 3050652011748976186677281)
                  ·
                    refine ⟨2287989008811732140007961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3050652011748976186677281 2287989008811732140007961)
                    ·
                      refine ⟨1715991756608799105005971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2287989008811732140007961 1715991756608799105005971)
                      ·
                        rfl

theorem cell23_3341882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 5, 2, 1, 2, 2].length) (baseStart_3341882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3341882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3341882 prefixEnd_3341882 := by exact prefixLift 3341882
  have htrace : WordTrace (prefixWord ++ tailWord_3341882) baseStart_3341882 baseEnd_3341882 := by
    simpa [prefixWord, tailWord_3341882, baseEnd_3341882] using wordTrace_append hprefix tailTrace_3341882
  have hstable : (prefixWord ++ tailWord_3341882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3341882).length < 2 ^ (prefixWord ++ tailWord_3341882).sum := by decide
  have hdescent : baseEnd_3341882 < baseStart_3341882 := by decide
  rcases family_descends (prefixWord ++ tailWord_3341882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3341898 : List Nat := [3, 1, 2, 1, 1, 3, 3, 3, 2, 1, 3]
def baseStart_3341898 : Nat := 118140960795 + 3341898 * 2 ^ 59
def prefixEnd_3341898 : Nat := 4983230072969 + 3 ^ 40 * 3341898 * 2
def baseEnd_3341898 : Nat := 1715999972299271042405897

theorem tailTrace_3341898 : CollatzResearch.WordTrace tailWord_3341898 prefixEnd_3341898 1715999972299271042405897 := by
  unfold tailWord_3341898
  simp only [CollatzResearch.WordTrace]
  refine ⟨30472258411720442895930587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81259355764587847722481565 30472258411720442895930587)
  ·
    refine ⟨45708387617580664343895881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30472258411720442895930587 45708387617580664343895881)
    ·
      refine ⟨34281290713185498257921911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45708387617580664343895881 34281290713185498257921911)
      ·
        refine ⟨51421936069778247386882867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34281290713185498257921911 51421936069778247386882867)
        ·
          refine ⟨77132904104667371080324301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51421936069778247386882867 77132904104667371080324301)
          ·
            refine ⟨28924839039250264155121613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77132904104667371080324301 28924839039250264155121613)
            ·
              refine ⟨10846814639718849058170605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28924839039250264155121613 10846814639718849058170605)
              ·
                refine ⟨4067555489894568396813977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10846814639718849058170605 4067555489894568396813977)
                ·
                  refine ⟨3050666617420926297610483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4067555489894568396813977 3050666617420926297610483)
                  ·
                    refine ⟨4575999926131389446415725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3050666617420926297610483 4575999926131389446415725)
                    ·
                      refine ⟨1715999972299271042405897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4575999926131389446415725 1715999972299271042405897)
                      ·
                        rfl

theorem cell23_3341898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 3, 3, 2, 1, 3].length) (baseStart_3341898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3341898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3341898 prefixEnd_3341898 := by exact prefixLift 3341898
  have htrace : WordTrace (prefixWord ++ tailWord_3341898) baseStart_3341898 baseEnd_3341898 := by
    simpa [prefixWord, tailWord_3341898, baseEnd_3341898] using wordTrace_append hprefix tailTrace_3341898
  have hstable : (prefixWord ++ tailWord_3341898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3341898).length < 2 ^ (prefixWord ++ tailWord_3341898).sum := by decide
  have hdescent : baseEnd_3341898 < baseStart_3341898 := by decide
  rcases family_descends (prefixWord ++ tailWord_3341898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3341908 : List Nat := [2, 4, 1, 1, 1, 2, 3, 1, 3, 3, 2]
def baseStart_3341908 : Nat := 118140960795 + 3341908 * 2 ^ 59
def prefixEnd_3341908 : Nat := 4983230072969 + 3 ^ 40 * 3341908 * 2
def baseEnd_3341908 : Nat := 1716005107105816003280851

theorem tailTrace_3341908 : CollatzResearch.WordTrace tailWord_3341908 prefixEnd_3341908 1716005107105816003280851 := by
  unfold tailWord_3341908
  simp only [CollatzResearch.WordTrace]
  refine ⟨60944699188422771645793189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81259598917897028861057585 60944699188422771645793189)
  ·
    refine ⟨11427131097829269683586223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60944699188422771645793189 11427131097829269683586223)
    ·
      refine ⟨17140696646743904525379335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11427131097829269683586223 17140696646743904525379335)
      ·
        refine ⟨25711044970115856788069003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17140696646743904525379335 25711044970115856788069003)
        ·
          refine ⟨38566567455173785182103505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25711044970115856788069003 38566567455173785182103505)
          ·
            refine ⟨28924925591380338886577629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38566567455173785182103505 28924925591380338886577629)
            ·
              refine ⟨10846847096767627082466611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28924925591380338886577629 10846847096767627082466611)
              ·
                refine ⟨16270270645151440623699917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10846847096767627082466611 16270270645151440623699917)
                ·
                  refine ⟨6101351491931790233887469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16270270645151440623699917 6101351491931790233887469)
                  ·
                    refine ⟨2288006809474421337707801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6101351491931790233887469 2288006809474421337707801)
                    ·
                      refine ⟨1716005107105816003280851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2288006809474421337707801 1716005107105816003280851)
                      ·
                        rfl

theorem cell23_3341908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 3, 1, 3, 3, 2].length) (baseStart_3341908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3341908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3341908 prefixEnd_3341908 := by exact prefixLift 3341908
  have htrace : WordTrace (prefixWord ++ tailWord_3341908) baseStart_3341908 baseEnd_3341908 := by
    simpa [prefixWord, tailWord_3341908, baseEnd_3341908] using wordTrace_append hprefix tailTrace_3341908
  have hstable : (prefixWord ++ tailWord_3341908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3341908).length < 2 ^ (prefixWord ++ tailWord_3341908).sum := by decide
  have hdescent : baseEnd_3341908 < baseStart_3341908 := by decide
  rcases family_descends (prefixWord ++ tailWord_3341908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3342006 : List Nat := [5, 1, 3, 1, 1, 2, 3, 1, 2, 2, 2]
def baseStart_3342006 : Nat := 118140960795 + 3342006 * 2 ^ 59
def prefixEnd_3342006 : Nat := 4983230072969 + 3 ^ 40 * 3342006 * 2
def baseEnd_3342006 : Nat := 1716055428209956619855401

theorem tailTrace_3342006 : CollatzResearch.WordTrace tailWord_3342006 prefixEnd_3342006 1716055428209956619855401 := by
  unfold tailWord_3342006
  simp only [CollatzResearch.WordTrace]
  refine ⟨7618310795655656626790867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 81261981820327004019102581 7618310795655656626790867)
  ·
    refine ⟨11427466193483484940186301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7618310795655656626790867 11427466193483484940186301)
    ·
      refine ⟨4285299822556306852569863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11427466193483484940186301 4285299822556306852569863)
      ·
        refine ⟨6427949733834460278854795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4285299822556306852569863 6427949733834460278854795)
        ·
          refine ⟨9641924600751690418282193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6427949733834460278854795 9641924600751690418282193)
          ·
            refine ⟨7231443450563767813711645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9641924600751690418282193 7231443450563767813711645)
            ·
              refine ⟨2711791293961412930141867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7231443450563767813711645 2711791293961412930141867)
              ·
                refine ⟨4067686940942119395212801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2711791293961412930141867 4067686940942119395212801)
                ·
                  refine ⟨3050765205706589546409601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4067686940942119395212801 3050765205706589546409601)
                  ·
                    refine ⟨2288073904279942159807201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3050765205706589546409601 2288073904279942159807201)
                    ·
                      refine ⟨1716055428209956619855401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2288073904279942159807201 1716055428209956619855401)
                      ·
                        rfl

theorem cell23_3342006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 3, 1, 2, 2, 2].length) (baseStart_3342006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3342006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3342006 prefixEnd_3342006 := by exact prefixLift 3342006
  have htrace : WordTrace (prefixWord ++ tailWord_3342006) baseStart_3342006 baseEnd_3342006 := by
    simpa [prefixWord, tailWord_3342006, baseEnd_3342006] using wordTrace_append hprefix tailTrace_3342006
  have hstable : (prefixWord ++ tailWord_3342006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3342006).length < 2 ^ (prefixWord ++ tailWord_3342006).sum := by decide
  have hdescent : baseEnd_3342006 < baseStart_3342006 := by decide
  rcases family_descends (prefixWord ++ tailWord_3342006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3342031 : List Nat := [1, 1, 2, 1, 1, 3, 1, 2, 6, 2, 3]
def baseStart_3342031 : Nat := 118140960795 + 3342031 * 2 ^ 59
def prefixEnd_3342031 : Nat := 4983230072969 + 3 ^ 40 * 3342031 * 2
def baseEnd_3342031 : Nat := 1716068265226319022042785

theorem tailTrace_3342031 : CollatzResearch.WordTrace tailWord_3342031 prefixEnd_3342031 1716068265226319022042785 := by
  unfold tailWord_3342031
  simp only [CollatzResearch.WordTrace]
  refine ⟨121893884555399935298313947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81262589703599956865542631 121893884555399935298313947)
  ·
    refine ⟨182840826833099902947470921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121893884555399935298313947 182840826833099902947470921)
    ·
      refine ⟨137130620124824927210603191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182840826833099902947470921 137130620124824927210603191)
      ·
        refine ⟨205695930187237390815904787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137130620124824927210603191 205695930187237390815904787)
        ·
          refine ⟨308543895280856086223857181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 205695930187237390815904787 308543895280856086223857181)
          ·
            refine ⟨115703960730321032333946443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 308543895280856086223857181 115703960730321032333946443)
            ·
              refine ⟨173555941095481548500919665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115703960730321032333946443 173555941095481548500919665)
              ·
                refine ⟨130166955821611161375689749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 173555941095481548500919665 130166955821611161375689749)
                ·
                  refine ⟨6101576054138023189485457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 130166955821611161375689749 6101576054138023189485457)
                  ·
                    refine ⟨4576182040603517392114093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6101576054138023189485457 4576182040603517392114093)
                    ·
                      refine ⟨1716068265226319022042785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4576182040603517392114093 1716068265226319022042785)
                      ·
                        rfl

theorem cell23_3342031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 2, 6, 2, 3].length) (baseStart_3342031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3342031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3342031 prefixEnd_3342031 := by exact prefixLift 3342031
  have htrace : WordTrace (prefixWord ++ tailWord_3342031) baseStart_3342031 baseEnd_3342031 := by
    simpa [prefixWord, tailWord_3342031, baseEnd_3342031] using wordTrace_append hprefix tailTrace_3342031
  have hstable : (prefixWord ++ tailWord_3342031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3342031).length < 2 ^ (prefixWord ++ tailWord_3342031).sum := by decide
  have hdescent : baseEnd_3342031 < baseStart_3342031 := by decide
  rcases family_descends (prefixWord ++ tailWord_3342031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3342111 : List Nat := [1, 1, 2, 4, 2, 1, 1, 2, 3, 6]
def baseStart_3342111 : Nat := 118140960795 + 3342111 * 2 ^ 59
def prefixEnd_3342111 : Nat := 4983230072969 + 3 ^ 40 * 3342111 * 2
def baseEnd_3342111 : Nat := 572036447892892903014139

theorem tailTrace_3342111 : CollatzResearch.WordTrace tailWord_3342111 prefixEnd_3342111 572036447892892903014139 := by
  unfold tailWord_3342111
  simp only [CollatzResearch.WordTrace]
  refine ⟨121896802395110108961226187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81264534930073405974150791 121896802395110108961226187)
  ·
    refine ⟨182845203592665163441839281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121896802395110108961226187 182845203592665163441839281)
    ·
      refine ⟨137133902694498872581379461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182845203592665163441839281 137133902694498872581379461)
      ·
        refine ⟨25712606755218538609008649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 137133902694498872581379461 25712606755218538609008649)
        ·
          refine ⟨19284455066413903956756487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25712606755218538609008649 19284455066413903956756487)
          ·
            refine ⟨28926682599620855935134731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19284455066413903956756487 28926682599620855935134731)
            ·
              refine ⟨43390023899431283902702097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28926682599620855935134731 43390023899431283902702097)
              ·
                refine ⟨32542517924573462927026573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43390023899431283902702097 32542517924573462927026573)
                ·
                  refine ⟨12203444221715048597634965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32542517924573462927026573 12203444221715048597634965)
                  ·
                    refine ⟨572036447892892903014139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12203444221715048597634965 572036447892892903014139)
                    ·
                      rfl

theorem cell23_3342111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 2, 3, 6].length) (baseStart_3342111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3342111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3342111 prefixEnd_3342111 := by exact prefixLift 3342111
  have htrace : WordTrace (prefixWord ++ tailWord_3342111) baseStart_3342111 baseEnd_3342111 := by
    simpa [prefixWord, tailWord_3342111, baseEnd_3342111] using wordTrace_append hprefix tailTrace_3342111
  have hstable : (prefixWord ++ tailWord_3342111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3342111).length < 2 ^ (prefixWord ++ tailWord_3342111).sum := by decide
  have hdescent : baseEnd_3342111 < baseStart_3342111 := by decide
  rcases family_descends (prefixWord ++ tailWord_3342111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3342112 : List Nat := [2, 1, 1, 5, 1, 1, 3, 4, 1, 1, 3]
def baseStart_3342112 : Nat := 118140960795 + 3342112 * 2 ^ 59
def prefixEnd_3342112 : Nat := 4983230072969 + 3 ^ 40 * 3342112 * 2
def baseEnd_3342112 : Nat := 1716109857159333205129913

theorem tailTrace_3342112 : CollatzResearch.WordTrace tailWord_3342112 prefixEnd_3342112 1716109857159333205129913 := by
  unfold tailWord_3342112
  simp only [CollatzResearch.WordTrace]
  refine ⟨60948419434053243066006295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81264559245404324088008393 60948419434053243066006295)
  ·
    refine ⟨91422629151079864599009443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60948419434053243066006295 91422629151079864599009443)
    ·
      refine ⟨137133943726619796898514165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91422629151079864599009443 137133943726619796898514165)
      ·
        refine ⟨12856307224370605959235703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 137133943726619796898514165 12856307224370605959235703)
        ·
          refine ⟨19284460836555908938853555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12856307224370605959235703 19284460836555908938853555)
          ·
            refine ⟨28926691254833863408280333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19284460836555908938853555 28926691254833863408280333)
            ·
              refine ⟨10847509220562698778105125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28926691254833863408280333 10847509220562698778105125)
              ·
                refine ⟨2033907978855506020894711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10847509220562698778105125 2033907978855506020894711)
                ·
                  refine ⟨3050861968283259031342067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2033907978855506020894711 3050861968283259031342067)
                  ·
                    refine ⟨4576292952424888547013101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3050861968283259031342067 4576292952424888547013101)
                    ·
                      refine ⟨1716109857159333205129913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4576292952424888547013101 1716109857159333205129913)
                      ·
                        rfl

theorem cell23_3342112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 3, 4, 1, 1, 3].length) (baseStart_3342112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3342112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3342112 prefixEnd_3342112 := by exact prefixLift 3342112
  have htrace : WordTrace (prefixWord ++ tailWord_3342112) baseStart_3342112 baseEnd_3342112 := by
    simpa [prefixWord, tailWord_3342112, baseEnd_3342112] using wordTrace_append hprefix tailTrace_3342112
  have hstable : (prefixWord ++ tailWord_3342112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3342112).length < 2 ^ (prefixWord ++ tailWord_3342112).sum := by decide
  have hdescent : baseEnd_3342112 < baseStart_3342112 := by decide
  rcases family_descends (prefixWord ++ tailWord_3342112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3342121 : List Nat := [1, 2, 1, 1, 1, 1, 1, 3, 1, 8, 3]
def baseStart_3342121 : Nat := 118140960795 + 3342121 * 2 ^ 59
def prefixEnd_3342121 : Nat := 4983230072969 + 3 ^ 40 * 3342121 * 2
def baseEnd_3342121 : Nat := 1716114478485223669917371

theorem tailTrace_3342121 : CollatzResearch.WordTrace tailWord_3342121 prefixEnd_3342121 1716114478485223669917371 := by
  unfold tailWord_3342121
  simp only [CollatzResearch.WordTrace]
  refine ⟨121897167125073880669090217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81264778083382587112726811 121897167125073880669090217)
  ·
    refine ⟨91422875343805410501817663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121897167125073880669090217 91422875343805410501817663)
    ·
      refine ⟨137134313015708115752726495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91422875343805410501817663 137134313015708115752726495)
      ·
        refine ⟨205701469523562173629089743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137134313015708115752726495 205701469523562173629089743)
        ·
          refine ⟨308552204285343260443634615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 205701469523562173629089743 308552204285343260443634615)
          ·
            refine ⟨462828306428014890665451923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 308552204285343260443634615 462828306428014890665451923)
            ·
              refine ⟨694242459642022335998177885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 462828306428014890665451923 694242459642022335998177885)
              ·
                refine ⟨260340922365758375999316707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 694242459642022335998177885 260340922365758375999316707)
                ·
                  refine ⟨390511383548637563998975061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 260340922365758375999316707 390511383548637563998975061)
                  ·
                    refine ⟨4576305275960596453112989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 390511383548637563998975061 4576305275960596453112989)
                    ·
                      refine ⟨1716114478485223669917371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4576305275960596453112989 1716114478485223669917371)
                      ·
                        rfl

theorem cell23_3342121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 8, 3].length) (baseStart_3342121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3342121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3342121 prefixEnd_3342121 := by exact prefixLift 3342121
  have htrace : WordTrace (prefixWord ++ tailWord_3342121) baseStart_3342121 baseEnd_3342121 := by
    simpa [prefixWord, tailWord_3342121, baseEnd_3342121] using wordTrace_append hprefix tailTrace_3342121
  have hstable : (prefixWord ++ tailWord_3342121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3342121).length < 2 ^ (prefixWord ++ tailWord_3342121).sum := by decide
  have hdescent : baseEnd_3342121 < baseStart_3342121 := by decide
  rcases family_descends (prefixWord ++ tailWord_3342121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3342152 : List Nat := [2, 1, 3, 1, 1, 6, 2, 1, 1, 1, 4]
def baseStart_3342152 : Nat := 118140960795 + 3342152 * 2 ^ 59
def prefixEnd_3342152 : Nat := 4983230072969 + 3 ^ 40 * 3342152 * 2
def baseEnd_3342152 : Nat := 1716130396385513048629729

theorem tailTrace_3342152 : CollatzResearch.WordTrace tailWord_3342152 prefixEnd_3342152 1716130396385513048629729 := by
  unfold tailWord_3342152
  simp only [CollatzResearch.WordTrace]
  refine ⟨60949148893980786481734355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81265531858641048642312473 60949148893980786481734355)
  ·
    refine ⟨91423723340971179722601533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60949148893980786481734355 91423723340971179722601533)
    ·
      refine ⟨34283896252864192395975575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91423723340971179722601533 34283896252864192395975575)
      ·
        refine ⟨51425844379296288593963363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34283896252864192395975575 51425844379296288593963363)
        ·
          refine ⟨77138766568944432890945045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51425844379296288593963363 77138766568944432890945045)
          ·
            refine ⟨3615879682919270291763049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 77138766568944432890945045 3615879682919270291763049)
            ·
              refine ⟨2711909762189452718822287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3615879682919270291763049 2711909762189452718822287)
              ·
                refine ⟨4067864643284179078233431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2711909762189452718822287 4067864643284179078233431)
                ·
                  refine ⟨6101796964926268617350147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4067864643284179078233431 6101796964926268617350147)
                  ·
                    refine ⟨9152695447389402926025221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6101796964926268617350147 9152695447389402926025221)
                    ·
                      refine ⟨1716130396385513048629729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9152695447389402926025221 1716130396385513048629729)
                      ·
                        rfl

theorem cell23_3342152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 6, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 6, 2, 1, 1, 1, 4].length) (baseStart_3342152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3342152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3342152 prefixEnd_3342152 := by exact prefixLift 3342152
  have htrace : WordTrace (prefixWord ++ tailWord_3342152) baseStart_3342152 baseEnd_3342152 := by
    simpa [prefixWord, tailWord_3342152, baseEnd_3342152] using wordTrace_append hprefix tailTrace_3342152
  have hstable : (prefixWord ++ tailWord_3342152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3342152).length < 2 ^ (prefixWord ++ tailWord_3342152).sum := by decide
  have hdescent : baseEnd_3342152 < baseStart_3342152 := by decide
  rcases family_descends (prefixWord ++ tailWord_3342152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3342162 : List Nat := [3, 2, 2, 1, 1, 5, 1, 2, 2, 4]
def baseStart_3342162 : Nat := 118140960795 + 3342162 * 2 ^ 59
def prefixEnd_3342162 : Nat := 4983230072969 + 3 ^ 40 * 3342162 * 2
def baseEnd_3342162 : Nat := 572045177064019336501561

theorem tailTrace_3342162 : CollatzResearch.WordTrace tailWord_3342162 prefixEnd_3342162 572045177064019336501561 := by
  unfold tailWord_3342162
  simp only [CollatzResearch.WordTrace]
  refine ⟨30474665629481336167833185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81265775011950229780888493 30474665629481336167833185)
  ·
    refine ⟨22855999222111002125874889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30474665629481336167833185 22855999222111002125874889)
    ·
      refine ⟨17141999416583251594406167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22855999222111002125874889 17141999416583251594406167)
      ·
        refine ⟨25712999124874877391609251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17141999416583251594406167 25712999124874877391609251)
        ·
          refine ⟨38569498687312316087413877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25712999124874877391609251 38569498687312316087413877)
          ·
            refine ⟨3615890501935529633195051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 38569498687312316087413877 3615890501935529633195051)
            ·
              refine ⟨5423835752903294449792577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3615890501935529633195051 5423835752903294449792577)
              ·
                refine ⟨4067876814677470837344433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5423835752903294449792577 4067876814677470837344433)
                ·
                  refine ⟨3050907611008103128008325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4067876814677470837344433 3050907611008103128008325)
                  ·
                    refine ⟨572045177064019336501561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3050907611008103128008325 572045177064019336501561)
                    ·
                      rfl

theorem cell23_3342162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 5, 1, 2, 2, 4].length) (baseStart_3342162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3342162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3342162 prefixEnd_3342162 := by exact prefixLift 3342162
  have htrace : WordTrace (prefixWord ++ tailWord_3342162) baseStart_3342162 baseEnd_3342162 := by
    simpa [prefixWord, tailWord_3342162, baseEnd_3342162] using wordTrace_append hprefix tailTrace_3342162
  have hstable : (prefixWord ++ tailWord_3342162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3342162).length < 2 ^ (prefixWord ++ tailWord_3342162).sum := by decide
  have hdescent : baseEnd_3342162 < baseStart_3342162 := by decide
  rcases family_descends (prefixWord ++ tailWord_3342162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3342185 : List Nat := [1, 2, 1, 1, 1, 3, 1, 7, 2, 1, 3]
def baseStart_3342185 : Nat := 118140960795 + 3342185 * 2 ^ 59
def prefixEnd_3342185 : Nat := 4983230072969 + 3 ^ 40 * 3342185 * 2
def baseEnd_3342185 : Nat := 1716147341247111419517077

theorem tailTrace_3342185 : CollatzResearch.WordTrace tailWord_3342185 prefixEnd_3342185 1716147341247111419517077 := by
  unfold tailWord_3342185
  simp only [CollatzResearch.WordTrace]
  refine ⟨121899501396842019599420009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81266334264561346399613339 121899501396842019599420009)
  ·
    refine ⟨91424626047631514699565007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121899501396842019599420009 91424626047631514699565007)
    ·
      refine ⟨137136939071447272049347511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91424626047631514699565007 137136939071447272049347511)
      ·
        refine ⟨205705408607170908074021267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137136939071447272049347511 205705408607170908074021267)
        ·
          refine ⟨308558112910756362111031901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 205705408607170908074021267 308558112910756362111031901)
          ·
            refine ⟨115709292341533635791636963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 308558112910756362111031901 115709292341533635791636963)
            ·
              refine ⟨173563938512300453687455445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115709292341533635791636963 173563938512300453687455445)
              ·
                refine ⟨4067904808882041883299737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 173563938512300453687455445 4067904808882041883299737)
                ·
                  refine ⟨3050928606661531412474803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4067904808882041883299737 3050928606661531412474803)
                  ·
                    refine ⟨4576392909992297118712205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3050928606661531412474803 4576392909992297118712205)
                    ·
                      refine ⟨1716147341247111419517077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4576392909992297118712205 1716147341247111419517077)
                      ·
                        rfl

theorem cell23_3342185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 7, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 7, 2, 1, 3].length) (baseStart_3342185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3342185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3342185 prefixEnd_3342185 := by exact prefixLift 3342185
  have htrace : WordTrace (prefixWord ++ tailWord_3342185) baseStart_3342185 baseEnd_3342185 := by
    simpa [prefixWord, tailWord_3342185, baseEnd_3342185] using wordTrace_append hprefix tailTrace_3342185
  have hstable : (prefixWord ++ tailWord_3342185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3342185).length < 2 ^ (prefixWord ++ tailWord_3342185).sum := by decide
  have hdescent : baseEnd_3342185 < baseStart_3342185 := by decide
  rcases family_descends (prefixWord ++ tailWord_3342185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3342212 : List Nat := [2, 3, 2, 1, 1, 1, 4, 3, 1, 3, 2]
def baseStart_3342212 : Nat := 118140960795 + 3342212 * 2 ^ 59
def prefixEnd_3342212 : Nat := 4983230072969 + 3 ^ 40 * 3342212 * 2
def baseEnd_3342212 : Nat := 1716161205224782813879453

theorem tailTrace_3342212 : CollatzResearch.WordTrace tailWord_3342212 prefixEnd_3342212 1716161205224782813879453 := by
  unfold tailWord_3342212
  simp only [CollatzResearch.WordTrace]
  refine ⟨60950243083872101605326445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81266990778496135473768593 60950243083872101605326445)
  ·
    refine ⟨22856341156452038101997417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60950243083872101605326445 22856341156452038101997417)
    ·
      refine ⟨17142255867339028576498063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22856341156452038101997417 17142255867339028576498063)
      ·
        refine ⟨25713383801008542864747095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17142255867339028576498063 25713383801008542864747095)
        ·
          refine ⟨38570075701512814297120643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25713383801008542864747095 38570075701512814297120643)
          ·
            refine ⟨57855113552269221445680965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38570075701512814297120643 57855113552269221445680965)
            ·
              refine ⟨10847833791050479021065181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57855113552269221445680965 10847833791050479021065181)
              ·
                refine ⟨4067937671643929632899443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10847833791050479021065181 4067937671643929632899443)
                ·
                  refine ⟨6101906507465894449349165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4067937671643929632899443 6101906507465894449349165)
                  ·
                    refine ⟨2288214940299710418505937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6101906507465894449349165 2288214940299710418505937)
                    ·
                      refine ⟨1716161205224782813879453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2288214940299710418505937 1716161205224782813879453)
                      ·
                        rfl

theorem cell23_3342212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 4, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 4, 3, 1, 3, 2].length) (baseStart_3342212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3342212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3342212 prefixEnd_3342212 := by exact prefixLift 3342212
  have htrace : WordTrace (prefixWord ++ tailWord_3342212) baseStart_3342212 baseEnd_3342212 := by
    simpa [prefixWord, tailWord_3342212, baseEnd_3342212] using wordTrace_append hprefix tailTrace_3342212
  have hstable : (prefixWord ++ tailWord_3342212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3342212).length < 2 ^ (prefixWord ++ tailWord_3342212).sum := by decide
  have hdescent : baseEnd_3342212 < baseStart_3342212 := by decide
  rcases family_descends (prefixWord ++ tailWord_3342212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3342230 : List Nat := [5, 3, 1, 1, 3, 1, 2, 1, 2, 4]
def baseStart_3342230 : Nat := 118140960795 + 3342230 * 2 ^ 59
def prefixEnd_3342230 : Nat := 4983230072969 + 3 ^ 40 * 3342230 * 2
def baseEnd_3342230 : Nat := 572056815958854581151457

theorem tailTrace_3342230 : CollatzResearch.WordTrace tailWord_3342230 prefixEnd_3342230 572056815958854581151457 := by
  unfold tailWord_3342230
  simp only [CollatzResearch.WordTrace]
  refine ⟨7618821417604937017800509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 81267428454452661523205429 7618821417604937017800509)
  ·
    refine ⟨2857058031601851381675191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7618821417604937017800509 2857058031601851381675191)
    ·
      refine ⟨4285587047402777072512787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2857058031601851381675191 4285587047402777072512787)
      ·
        refine ⟨6428380571104165608769181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4285587047402777072512787 6428380571104165608769181)
        ·
          refine ⟨2410642714164062103288443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6428380571104165608769181 2410642714164062103288443)
          ·
            refine ⟨3615964071246093154932665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2410642714164062103288443 3615964071246093154932665)
            ·
              refine ⟨2711973053434569866199499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3615964071246093154932665 2711973053434569866199499)
              ·
                refine ⟨4067959580151854799299249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2711973053434569866199499 4067959580151854799299249)
                ·
                  refine ⟨3050969685113891099474437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4067959580151854799299249 3050969685113891099474437)
                  ·
                    refine ⟨572056815958854581151457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3050969685113891099474437 572056815958854581151457)
                    ·
                      rfl

theorem cell23_3342230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 1, 2, 1, 2, 4].length) (baseStart_3342230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3342230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3342230 prefixEnd_3342230 := by exact prefixLift 3342230
  have htrace : WordTrace (prefixWord ++ tailWord_3342230) baseStart_3342230 baseEnd_3342230 := by
    simpa [prefixWord, tailWord_3342230, baseEnd_3342230] using wordTrace_append hprefix tailTrace_3342230
  have hstable : (prefixWord ++ tailWord_3342230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3342230).length < 2 ^ (prefixWord ++ tailWord_3342230).sum := by decide
  have hdescent : baseEnd_3342230 < baseStart_3342230 := by decide
  rcases family_descends (prefixWord ++ tailWord_3342230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3342236 : List Nat := [2, 2, 3, 3, 1, 3, 2, 1, 2, 1, 3]
def baseStart_3342236 : Nat := 118140960795 + 3342236 * 2 ^ 59
def prefixEnd_3342236 : Nat := 4983230072969 + 3 ^ 40 * 3342236 * 2
def baseEnd_3342236 : Nat := 1716173528760490719979343

theorem tailTrace_3342236 : CollatzResearch.WordTrace tailWord_3342236 prefixEnd_3342236 1716173528760490719979343 := by
  unfold tailWord_3342236
  simp only [CollatzResearch.WordTrace]
  refine ⟨60950680759828627654763281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81267574346438170206351041 60950680759828627654763281)
  ·
    refine ⟨45713010569871470741072461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60950680759828627654763281 45713010569871470741072461)
    ·
      refine ⟨17142378963701801527902173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45713010569871470741072461 17142378963701801527902173)
      ·
        refine ⟨6428392111388175572963315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17142378963701801527902173 6428392111388175572963315)
        ·
          refine ⟨9642588167082263359444973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6428392111388175572963315 9642588167082263359444973)
          ·
            refine ⟨3615970562655848759791865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9642588167082263359444973 3615970562655848759791865)
            ·
              refine ⟨2711977921991886569843899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3615970562655848759791865 2711977921991886569843899)
              ·
                refine ⟨4067966882987829854765849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2711977921991886569843899 4067966882987829854765849)
                ·
                  refine ⟨3050975162240872391074387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4067966882987829854765849 3050975162240872391074387)
                  ·
                    refine ⟨4576462743361308586611581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3050975162240872391074387 4576462743361308586611581)
                    ·
                      refine ⟨1716173528760490719979343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4576462743361308586611581 1716173528760490719979343)
                      ·
                        rfl

theorem cell23_3342236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 3, 2, 1, 2, 1, 3].length) (baseStart_3342236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3342236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3342236 prefixEnd_3342236 := by exact prefixLift 3342236
  have htrace : WordTrace (prefixWord ++ tailWord_3342236) baseStart_3342236 baseEnd_3342236 := by
    simpa [prefixWord, tailWord_3342236, baseEnd_3342236] using wordTrace_append hprefix tailTrace_3342236
  have hstable : (prefixWord ++ tailWord_3342236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3342236).length < 2 ^ (prefixWord ++ tailWord_3342236).sum := by decide
  have hdescent : baseEnd_3342236 < baseStart_3342236 := by decide
  rcases family_descends (prefixWord ++ tailWord_3342236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3342265 : List Nat := [1, 2, 1, 4, 2, 1, 2, 5, 5]
def baseStart_3342265 : Nat := 118140960795 + 3342265 * 2 ^ 59
def prefixEnd_3342265 : Nat := 4983230072969 + 3 ^ 40 * 3342265 * 2
def baseEnd_3342265 : Nat := 190687602188830122946301

theorem tailTrace_3342265 : CollatzResearch.WordTrace tailWord_3342265 prefixEnd_3342265 190687602188830122946301 := by
  unfold tailWord_3342265
  simp only [CollatzResearch.WordTrace]
  refine ⟨121902419236552193262332249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81268279491034795508221499 121902419236552193262332249)
  ·
    refine ⟨91426814427414144946749187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121902419236552193262332249 91426814427414144946749187)
    ·
      refine ⟨137140221641121217420123781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91426814427414144946749187 137140221641121217420123781)
      ·
        refine ⟨25713791557710228266273209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 137140221641121217420123781 25713791557710228266273209)
        ·
          refine ⟨19285343668282671199704907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25713791557710228266273209 19285343668282671199704907)
          ·
            refine ⟨28928015502424006799557361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19285343668282671199704907 28928015502424006799557361)
            ·
              refine ⟨21696011626818005099668021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28928015502424006799557361 21696011626818005099668021)
              ·
                refine ⟨2034001090014187978093877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21696011626818005099668021 2034001090014187978093877)
                ·
                  refine ⟨190687602188830122946301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2034001090014187978093877 190687602188830122946301)
                  ·
                    rfl

theorem cell23_3342265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 5, 5].length) (baseStart_3342265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3342265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3342265 prefixEnd_3342265 := by exact prefixLift 3342265
  have htrace : WordTrace (prefixWord ++ tailWord_3342265) baseStart_3342265 baseEnd_3342265 := by
    simpa [prefixWord, tailWord_3342265, baseEnd_3342265] using wordTrace_append hprefix tailTrace_3342265
  have hstable : (prefixWord ++ tailWord_3342265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3342265).length < 2 ^ (prefixWord ++ tailWord_3342265).sum := by decide
  have hdescent : baseEnd_3342265 < baseStart_3342265 := by decide
  rcases family_descends (prefixWord ++ tailWord_3342265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3342282 : List Nat := [3, 1, 2, 1, 2, 1, 6, 2, 5]
def baseStart_3342282 : Nat := 118140960795 + 3342282 * 2 ^ 59
def prefixEnd_3342282 : Nat := 4983230072969 + 3 ^ 40 * 3342282 * 2
def baseEnd_3342282 : Nat := 190688572096733060000459

theorem tailTrace_3342282 : CollatzResearch.WordTrace tailWord_3342282 prefixEnd_3342282 190688572096733060000459 := by
  unfold tailWord_3342282
  simp only [CollatzResearch.WordTrace]
  refine ⟨30475759819372651291425275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81268692851660403443800733 30475759819372651291425275)
  ·
    refine ⟨45713639729058976937137913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30475759819372651291425275 45713639729058976937137913)
    ·
      refine ⟨34285229796794232702853435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45713639729058976937137913 34285229796794232702853435)
      ·
        refine ⟨51427844695191349054280153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34285229796794232702853435 51427844695191349054280153)
        ·
          refine ⟨38570883521393511790710115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51427844695191349054280153 38570883521393511790710115)
          ·
            refine ⟨57856325282090267686065173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38570883521393511790710115 57856325282090267686065173)
            ·
              refine ⟨2712015247597981297784305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 57856325282090267686065173 2712015247597981297784305)
              ·
                refine ⟨2034011435698485973338229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2712015247597981297784305 2034011435698485973338229)
                ·
                  refine ⟨190688572096733060000459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2034011435698485973338229 190688572096733060000459)
                  ·
                    rfl

theorem cell23_3342282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 6, 2, 5].length) (baseStart_3342282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3342282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3342282 prefixEnd_3342282 := by exact prefixLift 3342282
  have htrace : WordTrace (prefixWord ++ tailWord_3342282) baseStart_3342282 baseEnd_3342282 := by
    simpa [prefixWord, tailWord_3342282, baseEnd_3342282] using wordTrace_append hprefix tailTrace_3342282
  have hstable : (prefixWord ++ tailWord_3342282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3342282).length < 2 ^ (prefixWord ++ tailWord_3342282).sum := by decide
  have hdescent : baseEnd_3342282 < baseStart_3342282 := by decide
  rcases family_descends (prefixWord ++ tailWord_3342282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3342288 : List Nat := [2, 1, 1, 1, 1, 2, 6, 1, 1, 2, 5]
def baseStart_3342288 : Nat := 118140960795 + 3342288 * 2 ^ 59
def prefixEnd_3342288 : Nat := 4983230072969 + 3 ^ 40 * 3342288 * 2
def baseEnd_3342288 : Nat := 1716200229754524516529103

theorem tailTrace_3342288 : CollatzResearch.WordTrace tailWord_3342288 prefixEnd_3342288 1716200229754524516529103 := by
  unfold tailWord_3342288
  simp only [CollatzResearch.WordTrace]
  refine ⟨60951629057734434095209759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81268838743645912126946345 60951629057734434095209759)
  ·
    refine ⟨91427443586601651142814639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60951629057734434095209759 91427443586601651142814639)
    ·
      refine ⟨137141165379902476714221959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91427443586601651142814639 137141165379902476714221959)
      ·
        refine ⟨205711748069853715071332939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137141165379902476714221959 205711748069853715071332939)
        ·
          refine ⟨308567622104780572606999409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 205711748069853715071332939 308567622104780572606999409)
          ·
            refine ⟨231425716578585429455249557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 308567622104780572606999409 231425716578585429455249557)
            ·
              refine ⟨10848080464621192005714823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 231425716578585429455249557 10848080464621192005714823)
              ·
                refine ⟨16272120696931788008572235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10848080464621192005714823 16272120696931788008572235)
                ·
                  refine ⟨24408181045397682012858353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16272120696931788008572235 24408181045397682012858353)
                  ·
                    refine ⟨18306135784048261509643765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24408181045397682012858353 18306135784048261509643765)
                    ·
                      refine ⟨1716200229754524516529103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18306135784048261509643765 1716200229754524516529103)
                      ·
                        rfl

theorem cell23_3342288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 6, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 6, 1, 1, 2, 5].length) (baseStart_3342288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3342288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3342288 prefixEnd_3342288 := by exact prefixLift 3342288
  have htrace : WordTrace (prefixWord ++ tailWord_3342288) baseStart_3342288 baseEnd_3342288 := by
    simpa [prefixWord, tailWord_3342288, baseEnd_3342288] using wordTrace_append hprefix tailTrace_3342288
  have hstable : (prefixWord ++ tailWord_3342288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3342288).length < 2 ^ (prefixWord ++ tailWord_3342288).sum := by decide
  have hdescent : baseEnd_3342288 < baseStart_3342288 := by decide
  rcases family_descends (prefixWord ++ tailWord_3342288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3342328 : List Nat := [2, 1, 2, 1, 1, 3, 3, 1, 2, 1, 6]
def baseStart_3342328 : Nat := 118140960795 + 3342328 * 2 ^ 59
def prefixEnd_3342328 : Nat := 4983230072969 + 3 ^ 40 * 3342328 * 2
def baseEnd_3342328 : Nat := 1716220768980704360028919

theorem tailTrace_3342328 : CollatzResearch.WordTrace tailWord_3342328 prefixEnd_3342328 1716220768980704360028919 := by
  unfold tailWord_3342328
  simp only [CollatzResearch.WordTrace]
  refine ⟨60952358517661977510937819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81269811356882636681250425 60952358517661977510937819)
  ·
    refine ⟨91428537776492966266406729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60952358517661977510937819 91428537776492966266406729)
    ·
      refine ⟨68571403332369724699805047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91428537776492966266406729 68571403332369724699805047)
      ·
        refine ⟨102857104998554587049707571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68571403332369724699805047 102857104998554587049707571)
        ·
          refine ⟨154285657497831880574561357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102857104998554587049707571 154285657497831880574561357)
          ·
            refine ⟨57857121561686955215460509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 154285657497831880574561357 57857121561686955215460509)
            ·
              refine ⟨21696420585632608205797691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57857121561686955215460509 21696420585632608205797691)
              ·
                refine ⟨32544630878448912308696537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21696420585632608205797691 32544630878448912308696537)
                ·
                  refine ⟨24408473158836684231522403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32544630878448912308696537 24408473158836684231522403)
                  ·
                    refine ⟨36612709738255026347283605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24408473158836684231522403 36612709738255026347283605)
                    ·
                      refine ⟨1716220768980704360028919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 36612709738255026347283605 1716220768980704360028919)
                      ·
                        rfl

theorem cell23_3342328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 1, 2, 1, 6].length) (baseStart_3342328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3342328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3342328 prefixEnd_3342328 := by exact prefixLift 3342328
  have htrace : WordTrace (prefixWord ++ tailWord_3342328) baseStart_3342328 baseEnd_3342328 := by
    simpa [prefixWord, tailWord_3342328, baseEnd_3342328] using wordTrace_append hprefix tailTrace_3342328
  have hstable : (prefixWord ++ tailWord_3342328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3342328).length < 2 ^ (prefixWord ++ tailWord_3342328).sum := by decide
  have hdescent : baseEnd_3342328 < baseStart_3342328 := by decide
  rcases family_descends (prefixWord ++ tailWord_3342328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3342335 : List Nat := [1, 1, 2, 2, 1, 2, 1, 6, 2, 2, 3]
def baseStart_3342335 : Nat := 118140960795 + 3342335 * 2 ^ 59
def prefixEnd_3342335 : Nat := 4983230072969 + 3 ^ 40 * 3342335 * 2
def baseEnd_3342335 : Nat := 1716224363345285832641387

theorem tailTrace_3342335 : CollatzResearch.WordTrace tailWord_3342335 prefixEnd_3342335 1716224363345285832641387 := by
  unfold tailWord_3342335
  simp only [CollatzResearch.WordTrace]
  refine ⟨121904972346298595217380459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81269981564199063478253639 121904972346298595217380459)
  ·
    refine ⟨182857458519447892826070689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121904972346298595217380459 182857458519447892826070689)
    ·
      refine ⟨137143093889585919619553017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182857458519447892826070689 137143093889585919619553017)
      ·
        refine ⟨102857320417189439714664763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137143093889585919619553017 102857320417189439714664763)
        ·
          refine ⟨154285980625784159571997145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102857320417189439714664763 154285980625784159571997145)
          ·
            refine ⟨115714485469338119678997859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 154285980625784159571997145 115714485469338119678997859)
            ·
              refine ⟨173571728204007179518496789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115714485469338119678997859 173571728204007179518496789)
              ·
                refine ⟨8136174759562836539929537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 173571728204007179518496789 8136174759562836539929537)
                ·
                  refine ⟨6102131069672127404947153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8136174759562836539929537 6102131069672127404947153)
                  ·
                    refine ⟨4576598302254095553710365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6102131069672127404947153 4576598302254095553710365)
                    ·
                      refine ⟨1716224363345285832641387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4576598302254095553710365 1716224363345285832641387)
                      ·
                        rfl

theorem cell23_3342335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 6, 2, 2, 3].length) (baseStart_3342335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3342335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3342335 prefixEnd_3342335 := by exact prefixLift 3342335
  have htrace : WordTrace (prefixWord ++ tailWord_3342335) baseStart_3342335 baseEnd_3342335 := by
    simpa [prefixWord, tailWord_3342335, baseEnd_3342335] using wordTrace_append hprefix tailTrace_3342335
  have hstable : (prefixWord ++ tailWord_3342335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3342335).length < 2 ^ (prefixWord ++ tailWord_3342335).sum := by decide
  have hdescent : baseEnd_3342335 < baseStart_3342335 := by decide
  rcases family_descends (prefixWord ++ tailWord_3342335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3342399 : List Nat := [1, 1, 2, 2, 3, 1, 2, 6, 1, 1, 3]
def baseStart_3342399 : Nat := 118140960795 + 3342399 * 2 ^ 59
def prefixEnd_3342399 : Nat := 4983230072969 + 3 ^ 40 * 3342399 * 2
def baseEnd_3342399 : Nat := 1716257226107173582241093

theorem tailTrace_3342399 : CollatzResearch.WordTrace tailWord_3342399 prefixEnd_3342399 1716257226107173582241093 := by
  unfold tailWord_3342399
  simp only [CollatzResearch.WordTrace]
  refine ⟨121907306618066734147710251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81271537745377822765140167 121907306618066734147710251)
  ·
    refine ⟨182860959927100101221565377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121907306618066734147710251 182860959927100101221565377)
    ·
      refine ⟨137145719945325075916174033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182860959927100101221565377 137145719945325075916174033)
      ·
        refine ⟨102859289958993806937130525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137145719945325075916174033 102859289958993806937130525)
        ·
          refine ⟨38572233734622677601423947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102859289958993806937130525 38572233734622677601423947)
          ·
            refine ⟨57858350601934016402135921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38572233734622677601423947 57858350601934016402135921)
            ·
              refine ⟨43393762951450512301601941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57858350601934016402135921 43393762951450512301601941)
              ·
                refine ⟨2034082638349242764137591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 43393762951450512301601941 2034082638349242764137591)
                ·
                  refine ⟨3051123957523864146206387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2034082638349242764137591 3051123957523864146206387)
                  ·
                    refine ⟨4576685936285796219309581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3051123957523864146206387 4576685936285796219309581)
                    ·
                      refine ⟨1716257226107173582241093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4576685936285796219309581 1716257226107173582241093)
                      ·
                        rfl

theorem cell23_3342399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 6, 1, 1, 3].length) (baseStart_3342399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3342399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3342399 prefixEnd_3342399 := by exact prefixLift 3342399
  have htrace : WordTrace (prefixWord ++ tailWord_3342399) baseStart_3342399 baseEnd_3342399 := by
    simpa [prefixWord, tailWord_3342399, baseEnd_3342399] using wordTrace_append hprefix tailTrace_3342399
  have hstable : (prefixWord ++ tailWord_3342399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3342399).length < 2 ^ (prefixWord ++ tailWord_3342399).sum := by decide
  have hdescent : baseEnd_3342399 < baseStart_3342399 := by decide
  rcases family_descends (prefixWord ++ tailWord_3342399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3342405 : List Nat := [1, 3, 1, 1, 1, 3, 1, 4, 3, 1, 4]
def baseStart_3342405 : Nat := 118140960795 + 3342405 * 2 ^ 59
def prefixEnd_3342405 : Nat := 4983230072969 + 3 ^ 40 * 3342405 * 2
def baseEnd_3342405 : Nat := 1716260306991100558766065

theorem tailTrace_3342405 : CollatzResearch.WordTrace tailWord_3342405 prefixEnd_3342405 1716260306991100558766065 := by
  unfold tailWord_3342405
  simp only [CollatzResearch.WordTrace]
  refine ⟨121907525456044997172428669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81271683637363331448285779 121907525456044997172428669)
  ·
    refine ⟨45715322046016873939660751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121907525456044997172428669 45715322046016873939660751)
    ·
      refine ⟨68572983069025310909491127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45715322046016873939660751 68572983069025310909491127)
      ·
        refine ⟨102859474603537966364236691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68572983069025310909491127 102859474603537966364236691)
        ·
          refine ⟨154289211905306949546355037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102859474603537966364236691 154289211905306949546355037)
          ·
            refine ⟨57858454464490106079883139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 154289211905306949546355037 57858454464490106079883139)
            ·
              refine ⟨86787681696735159119824709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57858454464490106079883139 86787681696735159119824709)
              ·
                refine ⟨16272690318137842334967133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 86787681696735159119824709 16272690318137842334967133)
                ·
                  refine ⟨6102258869301690875612675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16272690318137842334967133 6102258869301690875612675)
                  ·
                    refine ⟨9153388303952536313419013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6102258869301690875612675 9153388303952536313419013)
                    ·
                      refine ⟨1716260306991100558766065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9153388303952536313419013 1716260306991100558766065)
                      ·
                        rfl

theorem cell23_3342405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 4, 3, 1, 4].length) (baseStart_3342405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3342405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3342405 prefixEnd_3342405 := by exact prefixLift 3342405
  have htrace : WordTrace (prefixWord ++ tailWord_3342405) baseStart_3342405 baseEnd_3342405 := by
    simpa [prefixWord, tailWord_3342405, baseEnd_3342405] using wordTrace_append hprefix tailTrace_3342405
  have hstable : (prefixWord ++ tailWord_3342405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3342405).length < 2 ^ (prefixWord ++ tailWord_3342405).sum := by decide
  have hdescent : baseEnd_3342405 < baseStart_3342405 := by decide
  rcases family_descends (prefixWord ++ tailWord_3342405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3342435 : List Nat := [1, 1, 1, 5, 1, 1, 3, 1, 3, 2, 4]
def baseStart_3342435 : Nat := 118140960795 + 3342435 * 2 ^ 59
def prefixEnd_3342435 : Nat := 4983230072969 + 3 ^ 40 * 3342435 * 2
def baseEnd_3342435 : Nat := 1716275711410735441390927

theorem tailTrace_3342435 : CollatzResearch.WordTrace tailWord_3342435 prefixEnd_3342435 1716275711410735441390927 := by
  unfold tailWord_3342435
  simp only [CollatzResearch.WordTrace]
  refine ⟨121908619645936312296020759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81272413097290874864013839 121908619645936312296020759)
  ·
    refine ⟨182862929468904468444031139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121908619645936312296020759 182862929468904468444031139)
    ·
      refine ⟨274294394203356702666046709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182862929468904468444031139 274294394203356702666046709)
      ·
        refine ⟨25715099456564690874941879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 274294394203356702666046709 25715099456564690874941879)
        ·
          refine ⟨38572649184847036312412819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25715099456564690874941879 38572649184847036312412819)
          ·
            refine ⟨57858973777270554468619229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38572649184847036312412819 57858973777270554468619229)
            ·
              refine ⟨21697115166476457925732211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57858973777270554468619229 21697115166476457925732211)
              ·
                refine ⟨32545672749714686888598317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21697115166476457925732211 32545672749714686888598317)
                ·
                  refine ⟨12204627281143007583224369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32545672749714686888598317 12204627281143007583224369)
                  ·
                    refine ⟨9153470460857255687418277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12204627281143007583224369 9153470460857255687418277)
                    ·
                      refine ⟨1716275711410735441390927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9153470460857255687418277 1716275711410735441390927)
                      ·
                        rfl

theorem cell23_3342435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 1, 3, 2, 4].length) (baseStart_3342435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3342435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3342435 prefixEnd_3342435 := by exact prefixLift 3342435
  have htrace : WordTrace (prefixWord ++ tailWord_3342435) baseStart_3342435 baseEnd_3342435 := by
    simpa [prefixWord, tailWord_3342435, baseEnd_3342435] using wordTrace_append hprefix tailTrace_3342435
  have hstable : (prefixWord ++ tailWord_3342435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3342435).length < 2 ^ (prefixWord ++ tailWord_3342435).sum := by decide
  have hdescent : baseEnd_3342435 < baseStart_3342435 := by decide
  rcases family_descends (prefixWord ++ tailWord_3342435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3342439 : List Nat := [1, 1, 5, 1, 1, 2, 5, 1, 1, 1, 4]
def baseStart_3342439 : Nat := 118140960795 + 3342439 * 2 ^ 59
def prefixEnd_3342439 : Nat := 4983230072969 + 3 ^ 40 * 3342439 * 2
def baseEnd_3342439 : Nat := 1716277765333353425740909

theorem tailTrace_3342439 : CollatzResearch.WordTrace tailWord_3342439 prefixEnd_3342439 1716277765333353425740909 := by
  unfold tailWord_3342439
  simp only [CollatzResearch.WordTrace]
  refine ⟨121908765537921820979166371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81272510358614547319444247 121908765537921820979166371)
  ·
    refine ⟨182863148306882731468749557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121908765537921820979166371 182863148306882731468749557)
    ·
      refine ⟨17143420153770256075195271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 182863148306882731468749557 17143420153770256075195271)
      ·
        refine ⟨25715130230655384112792907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17143420153770256075195271 25715130230655384112792907)
        ·
          refine ⟨38572695345983076169189361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25715130230655384112792907 38572695345983076169189361)
          ·
            refine ⟨28929521509487307126892021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38572695345983076169189361 28929521509487307126892021)
            ·
              refine ⟨2712142641514435043146127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28929521509487307126892021 2712142641514435043146127)
              ·
                refine ⟨4068213962271652564719191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2712142641514435043146127 4068213962271652564719191)
                ·
                  refine ⟨6102320943407478847078787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4068213962271652564719191 6102320943407478847078787)
                  ·
                    refine ⟨9153481415111218270618181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6102320943407478847078787 9153481415111218270618181)
                    ·
                      refine ⟨1716277765333353425740909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9153481415111218270618181 1716277765333353425740909)
                      ·
                        rfl

theorem cell23_3342439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 5, 1, 1, 1, 4].length) (baseStart_3342439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3342439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3342439 prefixEnd_3342439 := by exact prefixLift 3342439
  have htrace : WordTrace (prefixWord ++ tailWord_3342439) baseStart_3342439 baseEnd_3342439 := by
    simpa [prefixWord, tailWord_3342439, baseEnd_3342439] using wordTrace_append hprefix tailTrace_3342439
  have hstable : (prefixWord ++ tailWord_3342439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3342439).length < 2 ^ (prefixWord ++ tailWord_3342439).sum := by decide
  have hdescent : baseEnd_3342439 < baseStart_3342439 := by decide
  rcases family_descends (prefixWord ++ tailWord_3342439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3342485 : List Nat := [1, 3, 2, 1, 1, 1, 4, 1, 2, 2, 5]
def baseStart_3342485 : Nat := 118140960795 + 3342485 * 2 ^ 59
def prefixEnd_3342485 : Nat := 4983230072969 + 3 ^ 40 * 3342485 * 2
def baseEnd_3342485 : Nat := 1716301385443460245765697

theorem tailTrace_3342485 : CollatzResearch.WordTrace tailWord_3342485 prefixEnd_3342485 1716301385443460245765697 := by
  unfold tailWord_3342485
  simp only [CollatzResearch.WordTrace]
  refine ⟨121910443295755170835340909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81273628863836780556893939 121910443295755170835340909)
  ·
    refine ⟨45716416235908189063252841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121910443295755170835340909 45716416235908189063252841)
    ·
      refine ⟨34287312176931141797439631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45716416235908189063252841 34287312176931141797439631)
      ·
        refine ⟨51430968265396712696159447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34287312176931141797439631 51430968265396712696159447)
        ·
          refine ⟨77146452398095069044239171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51430968265396712696159447 77146452398095069044239171)
          ·
            refine ⟨115719678597142603566358757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77146452398095069044239171 115719678597142603566358757)
            ·
              refine ⟨21697439736964238168692267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 115719678597142603566358757 21697439736964238168692267)
              ·
                refine ⟨32546159605446357253038401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21697439736964238168692267 32546159605446357253038401)
                ·
                  refine ⟨24409619704084767939778801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32546159605446357253038401 24409619704084767939778801)
                  ·
                    refine ⟨18307214778063575954834101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24409619704084767939778801 18307214778063575954834101)
                    ·
                      refine ⟨1716301385443460245765697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18307214778063575954834101 1716301385443460245765697)
                      ·
                        rfl

theorem cell23_3342485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 1, 2, 2, 5].length) (baseStart_3342485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3342485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3342485 prefixEnd_3342485 := by exact prefixLift 3342485
  have htrace : WordTrace (prefixWord ++ tailWord_3342485) baseStart_3342485 baseEnd_3342485 := by
    simpa [prefixWord, tailWord_3342485, baseEnd_3342485] using wordTrace_append hprefix tailTrace_3342485
  have hstable : (prefixWord ++ tailWord_3342485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3342485).length < 2 ^ (prefixWord ++ tailWord_3342485).sum := by decide
  have hdescent : baseEnd_3342485 < baseStart_3342485 := by decide
  rcases family_descends (prefixWord ++ tailWord_3342485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3342490 : List Nat := [3, 1, 1, 5, 2, 1, 2, 3, 1, 2, 2]
def baseStart_3342490 : Nat := 118140960795 + 3342490 * 2 ^ 59
def prefixEnd_3342490 : Nat := 4983230072969 + 3 ^ 40 * 3342490 * 2
def baseEnd_3342490 : Nat := 1716303952846732726203175

theorem tailTrace_3342490 : CollatzResearch.WordTrace tailWord_3342490 prefixEnd_3342490 1716303952846732726203175 := by
  unfold tailWord_3342490
  simp only [CollatzResearch.WordTrace]
  refine ⟨30477656415184264172318231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81273750440491371126181949 30477656415184264172318231)
  ·
    refine ⟨45716484622776396258477347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30477656415184264172318231 45716484622776396258477347)
    ·
      refine ⟨68574726934164594387716021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45716484622776396258477347 68574726934164594387716021)
      ·
        refine ⟨6428880650077930723848377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 68574726934164594387716021 6428880650077930723848377)
        ·
          refine ⟨4821660487558448042886283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6428880650077930723848377 4821660487558448042886283)
          ·
            refine ⟨7232490731337672064329425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4821660487558448042886283 7232490731337672064329425)
            ·
              refine ⟨5424368048503254048247069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7232490731337672064329425 5424368048503254048247069)
              ·
                refine ⟨2034138018188720268092651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5424368048503254048247069 2034138018188720268092651)
                ·
                  refine ⟨3051207027283080402138977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2034138018188720268092651 3051207027283080402138977)
                  ·
                    refine ⟨2288405270462310301604233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3051207027283080402138977 2288405270462310301604233)
                    ·
                      refine ⟨1716303952846732726203175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2288405270462310301604233 1716303952846732726203175)
                      ·
                        rfl

theorem cell23_3342490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 2, 3, 1, 2, 2].length) (baseStart_3342490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3342490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3342490 prefixEnd_3342490 := by exact prefixLift 3342490
  have htrace : WordTrace (prefixWord ++ tailWord_3342490) baseStart_3342490 baseEnd_3342490 := by
    simpa [prefixWord, tailWord_3342490, baseEnd_3342490] using wordTrace_append hprefix tailTrace_3342490
  have hstable : (prefixWord ++ tailWord_3342490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3342490).length < 2 ^ (prefixWord ++ tailWord_3342490).sum := by decide
  have hdescent : baseEnd_3342490 < baseStart_3342490 := by decide
  rcases family_descends (prefixWord ++ tailWord_3342490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3342515 : List Nat := [1, 1, 1, 2, 3, 2, 1, 2, 4, 1, 5]
def baseStart_3342515 : Nat := 118140960795 + 3342515 * 2 ^ 59
def prefixEnd_3342515 : Nat := 4983230072969 + 3 ^ 40 * 3342515 * 2
def baseEnd_3342515 : Nat := 1716316789863095128390559

theorem tailTrace_3342515 : CollatzResearch.WordTrace tailWord_3342515 prefixEnd_3342515 1716316789863095128390559 := by
  unfold tailWord_3342515
  simp only [CollatzResearch.WordTrace]
  refine ⟨121911537485646485958932999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81274358323764323972621999 121911537485646485958932999)
  ·
    refine ⟨182867306228469728938399499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121911537485646485958932999 182867306228469728938399499)
    ·
      refine ⟨274300959342704593407599249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182867306228469728938399499 274300959342704593407599249)
      ·
        refine ⟨205725719507028445055699437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 274300959342704593407599249 205725719507028445055699437)
        ·
          refine ⟨77147144815135666895887289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 205725719507028445055699437 77147144815135666895887289)
          ·
            refine ⟨57860358611351750171915467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77147144815135666895887289 57860358611351750171915467)
            ·
              refine ⟨86790537917027625257873201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57860358611351750171915467 86790537917027625257873201)
              ·
                refine ⟨65092903437770718943404901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86790537917027625257873201 65092903437770718943404901)
                ·
                  refine ⟨12204919394582009801888419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 65092903437770718943404901 12204919394582009801888419)
                  ·
                    refine ⟨18307379091873014702832629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12204919394582009801888419 18307379091873014702832629)
                    ·
                      refine ⟨1716316789863095128390559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18307379091873014702832629 1716316789863095128390559)
                      ·
                        rfl

theorem cell23_3342515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 2, 4, 1, 5].length) (baseStart_3342515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3342515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3342515 prefixEnd_3342515 := by exact prefixLift 3342515
  have htrace : WordTrace (prefixWord ++ tailWord_3342515) baseStart_3342515 baseEnd_3342515 := by
    simpa [prefixWord, tailWord_3342515, baseEnd_3342515] using wordTrace_append hprefix tailTrace_3342515
  have hstable : (prefixWord ++ tailWord_3342515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3342515).length < 2 ^ (prefixWord ++ tailWord_3342515).sum := by decide
  have hdescent : baseEnd_3342515 < baseStart_3342515 := by decide
  rcases family_descends (prefixWord ++ tailWord_3342515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3342546 : List Nat := [3, 2, 2, 2, 1, 2, 1, 2, 4, 2, 2]
def baseStart_3342546 : Nat := 118140960795 + 3342546 * 2 ^ 59
def prefixEnd_3342546 : Nat := 4983230072969 + 3 ^ 40 * 3342546 * 2
def baseEnd_3342546 : Nat := 1716332707763384507102917

theorem tailTrace_3342546 : CollatzResearch.WordTrace tailWord_3342546 prefixEnd_3342546 1716332707763384507102917 := by
  unfold tailWord_3342546
  simp only [CollatzResearch.WordTrace]
  refine ⟨30478167037133544563327873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81275112099022785502207661 30478167037133544563327873)
  ·
    refine ⟨22858625277850158422495905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30478167037133544563327873 22858625277850158422495905)
    ·
      refine ⟨17143968958387618816871929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22858625277850158422495905 17143968958387618816871929)
      ·
        refine ⟨12857976718790714112653947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17143968958387618816871929 12857976718790714112653947)
        ·
          refine ⟨19286965078186071168980921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12857976718790714112653947 19286965078186071168980921)
          ·
            refine ⟨14465223808639553376735691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19286965078186071168980921 14465223808639553376735691)
            ·
              refine ⟨21697835712959330065103537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14465223808639553376735691 21697835712959330065103537)
              ·
                refine ⟨16273376784719497548827653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21697835712959330065103537 16273376784719497548827653)
                ·
                  refine ⟨3051258147134905790405185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16273376784719497548827653 3051258147134905790405185)
                  ·
                    refine ⟨2288443610351179342803889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3051258147134905790405185 2288443610351179342803889)
                    ·
                      refine ⟨1716332707763384507102917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2288443610351179342803889 1716332707763384507102917)
                      ·
                        rfl

theorem cell23_3342546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 2, 4, 2, 2].length) (baseStart_3342546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3342546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3342546 prefixEnd_3342546 := by exact prefixLift 3342546
  have htrace : WordTrace (prefixWord ++ tailWord_3342546) baseStart_3342546 baseEnd_3342546 := by
    simpa [prefixWord, tailWord_3342546, baseEnd_3342546] using wordTrace_append hprefix tailTrace_3342546
  have hstable : (prefixWord ++ tailWord_3342546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3342546).length < 2 ^ (prefixWord ++ tailWord_3342546).sum := by decide
  have hdescent : baseEnd_3342546 < baseStart_3342546 := by decide
  rcases family_descends (prefixWord ++ tailWord_3342546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3342549 : List Nat := [1, 3, 2, 4, 2, 1, 1, 1, 2, 1, 5]
def baseStart_3342549 : Nat := 118140960795 + 3342549 * 2 ^ 59
def prefixEnd_3342549 : Nat := 4983230072969 + 3 ^ 40 * 3342549 * 2
def baseEnd_3342549 : Nat := 1716334248205347995365403

theorem tailTrace_3342549 : CollatzResearch.WordTrace tailWord_3342549 prefixEnd_3342549 1716334248205347995365403 := by
  unfold tailWord_3342549
  simp only [CollatzResearch.WordTrace]
  refine ⟨121912777567523309765670701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81275185045015539843780467 121912777567523309765670701)
  ·
    refine ⟨45717291587821241162126513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121912777567523309765670701 45717291587821241162126513)
    ·
      refine ⟨34287968690865930871594885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45717291587821241162126513 34287968690865930871594885)
      ·
        refine ⟨6428994129537362038424041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34287968690865930871594885 6428994129537362038424041)
        ·
          refine ⟨4821745597153021528818031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6428994129537362038424041 4821745597153021528818031)
          ·
            refine ⟨7232618395729532293227047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4821745597153021528818031 7232618395729532293227047)
            ·
              refine ⟨10848927593594298439840571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7232618395729532293227047 10848927593594298439840571)
              ·
                refine ⟨16273391390391447659760857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10848927593594298439840571 16273391390391447659760857)
                ·
                  refine ⟨12205043542793585744820643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16273391390391447659760857 12205043542793585744820643)
                  ·
                    refine ⟨18307565314190378617230965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12205043542793585744820643 18307565314190378617230965)
                    ·
                      refine ⟨1716334248205347995365403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18307565314190378617230965 1716334248205347995365403)
                      ·
                        rfl

theorem cell23_3342549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 1, 1, 2, 1, 5].length) (baseStart_3342549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3342549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3342549 prefixEnd_3342549 := by exact prefixLift 3342549
  have htrace : WordTrace (prefixWord ++ tailWord_3342549) baseStart_3342549 baseEnd_3342549 := by
    simpa [prefixWord, tailWord_3342549, baseEnd_3342549] using wordTrace_append hprefix tailTrace_3342549
  have hstable : (prefixWord ++ tailWord_3342549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3342549).length < 2 ^ (prefixWord ++ tailWord_3342549).sum := by decide
  have hdescent : baseEnd_3342549 < baseStart_3342549 := by decide
  rcases family_descends (prefixWord ++ tailWord_3342549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3342582 : List Nat := [5, 1, 1, 1, 1, 1, 2, 1, 3, 7]
def baseStart_3342582 : Nat := 118140960795 + 3342582 * 2 ^ 59
def prefixEnd_3342582 : Nat := 4983230072969 + 3 ^ 40 * 3342582 * 2
def baseEnd_3342582 : Nat := 572117064355648788750917

theorem tailTrace_3342582 : CollatzResearch.WordTrace tailWord_3342582 prefixEnd_3342582 572117064355648788750917 := by
  unfold tailWord_3342582
  simp only [CollatzResearch.WordTrace]
  refine ⟨7619623823525234775101375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 81275987450935837601081333 7619623823525234775101375)
  ·
    refine ⟨11429435735287852162652063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7619623823525234775101375 11429435735287852162652063)
    ·
      refine ⟨17144153602931778243978095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11429435735287852162652063 17144153602931778243978095)
      ·
        refine ⟨25716230404397667365967143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17144153602931778243978095 25716230404397667365967143)
        ·
          refine ⟨38574345606596501048950715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25716230404397667365967143 38574345606596501048950715)
          ·
            refine ⟨57861518409894751573426073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38574345606596501048950715 57861518409894751573426073)
            ·
              refine ⟨43396138807421063680069555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57861518409894751573426073 43396138807421063680069555)
              ·
                refine ⟨65094208211131595520104333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43396138807421063680069555 65094208211131595520104333)
                ·
                  refine ⟨24410328079174348320039125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 65094208211131595520104333 24410328079174348320039125)
                  ·
                    refine ⟨572117064355648788750917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24410328079174348320039125 572117064355648788750917)
                    ·
                      rfl

theorem cell23_3342582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 1, 3, 7].length) (baseStart_3342582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3342582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3342582 prefixEnd_3342582 := by exact prefixLift 3342582
  have htrace : WordTrace (prefixWord ++ tailWord_3342582) baseStart_3342582 baseEnd_3342582 := by
    simpa [prefixWord, tailWord_3342582, baseEnd_3342582] using wordTrace_append hprefix tailTrace_3342582
  have hstable : (prefixWord ++ tailWord_3342582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3342582).length < 2 ^ (prefixWord ++ tailWord_3342582).sum := by decide
  have hdescent : baseEnd_3342582 < baseStart_3342582 := by decide
  rcases family_descends (prefixWord ++ tailWord_3342582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3342602 : List Nat := [3, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4]
def baseStart_3342602 : Nat := 118140960795 + 3342602 * 2 ^ 59
def prefixEnd_3342602 : Nat := 4983230072969 + 3 ^ 40 * 3342602 * 2
def baseEnd_3342602 : Nat := 1716361462680036288002659

theorem tailTrace_3342602 : CollatzResearch.WordTrace tailWord_3342602 prefixEnd_3342602 1716361462680036288002659 := by
  unfold tailWord_3342602
  simp only [CollatzResearch.WordTrace]
  refine ⟨30478677659082824954337515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81276473757554199878233373 30478677659082824954337515)
  ·
    refine ⟨45718016488624237431506273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30478677659082824954337515 45718016488624237431506273)
    ·
      refine ⟨34288512366468178073629705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45718016488624237431506273 34288512366468178073629705)
      ·
        refine ⟨25716384274851133555222279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34288512366468178073629705 25716384274851133555222279)
        ·
          refine ⟨38574576412276700332833419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25716384274851133555222279 38574576412276700332833419)
          ·
            refine ⟨57861864618415050499250129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38574576412276700332833419 57861864618415050499250129)
            ·
              refine ⟨43396398463811287874437597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57861864618415050499250129 43396398463811287874437597)
              ·
                refine ⟨16273649423929232952914099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43396398463811287874437597 16273649423929232952914099)
                ·
                  refine ⟨24410474135893849429371149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16273649423929232952914099 24410474135893849429371149)
                  ·
                    refine ⟨9153927800960193536014181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24410474135893849429371149 9153927800960193536014181)
                    ·
                      refine ⟨1716361462680036288002659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9153927800960193536014181 1716361462680036288002659)
                      ·
                        rfl

theorem cell23_3342602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4].length) (baseStart_3342602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3342602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3342602 prefixEnd_3342602 := by exact prefixLift 3342602
  have htrace : WordTrace (prefixWord ++ tailWord_3342602) baseStart_3342602 baseEnd_3342602 := by
    simpa [prefixWord, tailWord_3342602, baseEnd_3342602] using wordTrace_append hprefix tailTrace_3342602
  have hstable : (prefixWord ++ tailWord_3342602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3342602).length < 2 ^ (prefixWord ++ tailWord_3342602).sum := by decide
  have hdescent : baseEnd_3342602 < baseStart_3342602 := by decide
  rcases family_descends (prefixWord ++ tailWord_3342602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3342676 : List Nat := [2, 4, 1, 1, 2, 4, 1, 2, 6]
def baseStart_3342676 : Nat := 118140960795 + 3342676 * 2 ^ 59
def prefixEnd_3342676 : Nat := 4983230072969 + 3 ^ 40 * 3342676 * 2
def baseEnd_3342676 : Nat := 190711051138718777608591

theorem tailTrace_3342676 : CollatzResearch.WordTrace tailWord_3342676 prefixEnd_3342676 190711051138718777608591 := by
  unfold tailWord_3342676
  simp only [CollatzResearch.WordTrace]
  refine ⟨60958704819031605227771941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81278273092042140303695921 60958704819031605227771941)
  ·
    refine ⟨11429757153568425980207239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60958704819031605227771941 11429757153568425980207239)
    ·
      refine ⟨17144635730352638970310859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11429757153568425980207239 17144635730352638970310859)
      ·
        refine ⟨25716953595528958455466289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17144635730352638970310859 25716953595528958455466289)
        ·
          refine ⟨19287715196646718841599717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25716953595528958455466289 19287715196646718841599717)
          ·
            refine ⟨3616446599371259782799947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19287715196646718841599717 3616446599371259782799947)
            ·
              refine ⟨5424669899056889674199921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3616446599371259782799947 5424669899056889674199921)
              ·
                refine ⟨4068502424292667255649941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5424669899056889674199921 4068502424292667255649941)
                ·
                  refine ⟨190711051138718777608591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4068502424292667255649941 190711051138718777608591)
                  ·
                    rfl

theorem cell23_3342676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 4, 1, 2, 6].length) (baseStart_3342676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3342676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3342676 prefixEnd_3342676 := by exact prefixLift 3342676
  have htrace : WordTrace (prefixWord ++ tailWord_3342676) baseStart_3342676 baseEnd_3342676 := by
    simpa [prefixWord, tailWord_3342676, baseEnd_3342676] using wordTrace_append hprefix tailTrace_3342676
  have hstable : (prefixWord ++ tailWord_3342676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3342676).length < 2 ^ (prefixWord ++ tailWord_3342676).sum := by decide
  have hdescent : baseEnd_3342676 < baseStart_3342676 := by decide
  rcases family_descends (prefixWord ++ tailWord_3342676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3342696 : List Nat := [2, 1, 4, 2, 2, 1, 1, 2, 1, 5, 2]
def baseStart_3342696 : Nat := 118140960795 + 3342696 * 2 ^ 59
def prefixEnd_3342696 : Nat := 4983230072969 + 3 ^ 40 * 3342696 * 2
def baseEnd_3342696 : Nat := 1716409729861558920227227

theorem tailTrace_3342696 : CollatzResearch.WordTrace tailWord_3342696 prefixEnd_3342696 1716409729861558920227227 := by
  unfold tailWord_3342696
  simp only [CollatzResearch.WordTrace]
  refine ⟨60959069548995376935635971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81278759398660502580847961 60959069548995376935635971)
  ·
    refine ⟨91438604323493065403453957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60959069548995376935635971 91438604323493065403453957)
    ·
      refine ⟨17144738310654949763147617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 91438604323493065403453957 17144738310654949763147617)
      ·
        refine ⟨12858553732991212322360713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17144738310654949763147617 12858553732991212322360713)
        ·
          refine ⟨9643915299743409241770535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12858553732991212322360713 9643915299743409241770535)
          ·
            refine ⟨14465872949615113862655803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9643915299743409241770535 14465872949615113862655803)
            ·
              refine ⟨21698809424422670793983705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14465872949615113862655803 21698809424422670793983705)
              ·
                refine ⟨16274107068317003095487779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21698809424422670793983705 16274107068317003095487779)
                ·
                  refine ⟨24411160602475504643231669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16274107068317003095487779 24411160602475504643231669)
                  ·
                    refine ⟨2288546306482078560302969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 24411160602475504643231669 2288546306482078560302969)
                    ·
                      refine ⟨1716409729861558920227227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2288546306482078560302969 1716409729861558920227227)
                      ·
                        rfl

theorem cell23_3342696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 2, 1, 5, 2].length) (baseStart_3342696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3342696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3342696 prefixEnd_3342696 := by exact prefixLift 3342696
  have htrace : WordTrace (prefixWord ++ tailWord_3342696) baseStart_3342696 baseEnd_3342696 := by
    simpa [prefixWord, tailWord_3342696, baseEnd_3342696] using wordTrace_append hprefix tailTrace_3342696
  have hstable : (prefixWord ++ tailWord_3342696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3342696).length < 2 ^ (prefixWord ++ tailWord_3342696).sum := by decide
  have hdescent : baseEnd_3342696 < baseStart_3342696 := by decide
  rcases family_descends (prefixWord ++ tailWord_3342696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3342706 : List Nat := [3, 2, 1, 2, 1, 4, 2, 2, 1, 5]
def baseStart_3342706 : Nat := 118140960795 + 3342706 * 2 ^ 59
def prefixEnd_3342706 : Nat := 4983230072969 + 3 ^ 40 * 3342706 * 2
def baseEnd_3342706 : Nat := 572138288222701293700727

theorem tailTrace_3342706 : CollatzResearch.WordTrace tailWord_3342706 prefixEnd_3342706 572138288222701293700727 := by
  unfold tailWord_3342706
  simp only [CollatzResearch.WordTrace]
  refine ⟨30479625956988631394783993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81279002551969683719423981 30479625956988631394783993)
  ·
    refine ⟨22859719467741473546087995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30479625956988631394783993 22859719467741473546087995)
    ·
      refine ⟨34289579201612210319131993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22859719467741473546087995 34289579201612210319131993)
      ·
        refine ⟨25717184401209157739348995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34289579201612210319131993 25717184401209157739348995)
        ·
          refine ⟨38575776601813736609023493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25717184401209157739348995 38575776601813736609023493)
          ·
            refine ⟨7232958112840075614191905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38575776601813736609023493 7232958112840075614191905)
            ·
              refine ⟨5424718584630056710643929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7232958112840075614191905 5424718584630056710643929)
              ·
                refine ⟨4068538938472542532982947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5424718584630056710643929 4068538938472542532982947)
                ·
                  refine ⟨6102808407708813799474421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4068538938472542532982947 6102808407708813799474421)
                  ·
                    refine ⟨572138288222701293700727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6102808407708813799474421 572138288222701293700727)
                    ·
                      rfl

theorem cell23_3342706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 2, 2, 1, 5].length) (baseStart_3342706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3342706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3342706 prefixEnd_3342706 := by exact prefixLift 3342706
  have htrace : WordTrace (prefixWord ++ tailWord_3342706) baseStart_3342706 baseEnd_3342706 := by
    simpa [prefixWord, tailWord_3342706, baseEnd_3342706] using wordTrace_append hprefix tailTrace_3342706
  have hstable : (prefixWord ++ tailWord_3342706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3342706).length < 2 ^ (prefixWord ++ tailWord_3342706).sum := by decide
  have hdescent : baseEnd_3342706 < baseStart_3342706 := by decide
  rcases family_descends (prefixWord ++ tailWord_3342706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3342729 : List Nat := [1, 2, 1, 1, 6, 1, 1, 3, 1, 1, 5]
def baseStart_3342729 : Nat := 118140960795 + 3342729 * 2 ^ 59
def prefixEnd_3342729 : Nat := 4983230072969 + 3 ^ 40 * 3342729 * 2
def baseEnd_3342729 : Nat := 1716426674723157291114575

theorem tailTrace_3342729 : CollatzResearch.WordTrace tailWord_3342729 prefixEnd_3342729 1716426674723157291114575 := by
  unfold tailWord_3342729
  simp only [CollatzResearch.WordTrace]
  refine ⟨121919342706871200507223241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81279561804580800338148827 121919342706871200507223241)
  ·
    refine ⟨91439507030153400380417431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121919342706871200507223241 91439507030153400380417431)
    ·
      refine ⟨137159260545230100570626147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91439507030153400380417431 137159260545230100570626147)
      ·
        refine ⟨205738890817845150855939221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137159260545230100570626147 205738890817845150855939221)
        ·
          refine ⟨9644010507086491446372151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 205738890817845150855939221 9644010507086491446372151)
          ·
            refine ⟨14466015760629737169558227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9644010507086491446372151 14466015760629737169558227)
            ·
              refine ⟨21699023640944605754337341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14466015760629737169558227 21699023640944605754337341)
              ·
                refine ⟨8137133865354227157876503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21699023640944605754337341 8137133865354227157876503)
                ·
                  refine ⟨12205700798031340736814755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8137133865354227157876503 12205700798031340736814755)
                  ·
                    refine ⟨18308551197047011105222133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12205700798031340736814755 18308551197047011105222133)
                    ·
                      refine ⟨1716426674723157291114575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18308551197047011105222133 1716426674723157291114575)
                      ·
                        rfl

theorem cell23_3342729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 3, 1, 1, 5].length) (baseStart_3342729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3342729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3342729 prefixEnd_3342729 := by exact prefixLift 3342729
  have htrace : WordTrace (prefixWord ++ tailWord_3342729) baseStart_3342729 baseEnd_3342729 := by
    simpa [prefixWord, tailWord_3342729, baseEnd_3342729] using wordTrace_append hprefix tailTrace_3342729
  have hstable : (prefixWord ++ tailWord_3342729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3342729).length < 2 ^ (prefixWord ++ tailWord_3342729).sum := by decide
  have hdescent : baseEnd_3342729 < baseStart_3342729 := by decide
  rcases family_descends (prefixWord ++ tailWord_3342729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3342730 : List Nat := [3, 1, 2, 5, 1, 1, 1, 2, 2, 3, 2]
def baseStart_3342730 : Nat := 118140960795 + 3342730 * 2 ^ 59
def prefixEnd_3342730 : Nat := 4983230072969 + 3 ^ 40 * 3342730 * 2
def baseEnd_3342730 : Nat := 1716427188203811787202071

theorem tailTrace_3342730 : CollatzResearch.WordTrace tailWord_3342730 prefixEnd_3342730 1716427188203811787202071 := by
  unfold tailWord_3342730
  simp only [CollatzResearch.WordTrace]
  refine ⟨30479844794966894419502411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81279586119911718452006429 30479844794966894419502411)
  ·
    refine ⟨45719767192450341629253617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30479844794966894419502411 45719767192450341629253617)
    ·
      refine ⟨34289825394337756221940213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45719767192450341629253617 34289825394337756221940213)
      ·
        refine ⟨3214671130719164645806895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 34289825394337756221940213 3214671130719164645806895)
        ·
          refine ⟨4822006696078746968710343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3214671130719164645806895 4822006696078746968710343)
          ·
            refine ⟨7233010044118120453065515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4822006696078746968710343 7233010044118120453065515)
            ·
              refine ⟨10849515066177180679598273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7233010044118120453065515 10849515066177180679598273)
              ·
                refine ⟨8137136299632885509698705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10849515066177180679598273 8137136299632885509698705)
                ·
                  refine ⟨6102852224724664132274029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8137136299632885509698705 6102852224724664132274029)
                  ·
                    refine ⟨2288569584271749049602761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6102852224724664132274029 2288569584271749049602761)
                    ·
                      refine ⟨1716427188203811787202071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2288569584271749049602761 1716427188203811787202071)
                      ·
                        rfl

theorem cell23_3342730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 1, 2, 2, 3, 2].length) (baseStart_3342730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3342730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3342730 prefixEnd_3342730 := by exact prefixLift 3342730
  have htrace : WordTrace (prefixWord ++ tailWord_3342730) baseStart_3342730 baseEnd_3342730 := by
    simpa [prefixWord, tailWord_3342730, baseEnd_3342730] using wordTrace_append hprefix tailTrace_3342730
  have hstable : (prefixWord ++ tailWord_3342730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3342730).length < 2 ^ (prefixWord ++ tailWord_3342730).sum := by decide
  have hdescent : baseEnd_3342730 < baseStart_3342730 := by decide
  rcases family_descends (prefixWord ++ tailWord_3342730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3342732 : List Nat := [2, 2, 1, 2, 1, 4, 11]
def baseStart_3342732 : Nat := 118140960795 + 3342732 * 2 ^ 59
def prefixEnd_3342732 : Nat := 4983230072969 + 3 ^ 40 * 3342732 * 2
def baseEnd_3342732 : Nat := 21190471792161984930581

theorem tailTrace_3342732 : CollatzResearch.WordTrace tailWord_3342732 prefixEnd_3342732 21190471792161984930581 := by
  unfold tailWord_3342732
  simp only [CollatzResearch.WordTrace]
  refine ⟨60959726062930166009791225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81279634750573554679721633 60959726062930166009791225)
  ·
    refine ⟨45719794547197624507343419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60959726062930166009791225 45719794547197624507343419)
    ·
      refine ⟨68579691820796436761015129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45719794547197624507343419 68579691820796436761015129)
      ·
        refine ⟨51434768865597327570761347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68579691820796436761015129 51434768865597327570761347)
        ·
          refine ⟨77152153298395991356142021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51434768865597327570761347 77152153298395991356142021)
          ·
            refine ⟨14466028743449248379276629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 77152153298395991356142021 14466028743449248379276629)
            ·
              refine ⟨21190471792161984930581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 14466028743449248379276629 21190471792161984930581)
              ·
                rfl

theorem cell23_3342732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 11].length) (baseStart_3342732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3342732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3342732 prefixEnd_3342732 := by exact prefixLift 3342732
  have htrace : WordTrace (prefixWord ++ tailWord_3342732) baseStart_3342732 baseEnd_3342732 := by
    simpa [prefixWord, tailWord_3342732, baseEnd_3342732] using wordTrace_append hprefix tailTrace_3342732
  have hstable : (prefixWord ++ tailWord_3342732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3342732).length < 2 ^ (prefixWord ++ tailWord_3342732).sum := by decide
  have hdescent : baseEnd_3342732 < baseStart_3342732 := by decide
  rcases family_descends (prefixWord ++ tailWord_3342732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3342743 : List Nat := [1, 1, 3, 3, 1, 1, 5, 1, 3, 2, 2]
def baseStart_3342743 : Nat := 118140960795 + 3342743 * 2 ^ 59
def prefixEnd_3342743 : Nat := 4983230072969 + 3 ^ 40 * 3342743 * 2
def baseEnd_3342743 : Nat := 1716433863452320236339511

theorem tailTrace_3342743 : CollatzResearch.WordTrace tailWord_3342743 prefixEnd_3342743 1716433863452320236339511 := by
  unfold tailWord_3342743
  simp only [CollatzResearch.WordTrace]
  refine ⟨121919853328820480898232883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81279902219213653932155255 121919853328820480898232883)
  ·
    refine ⟨182879779993230721347349325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121919853328820480898232883 182879779993230721347349325)
    ·
      refine ⟨68579917497461520505255997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 182879779993230721347349325 68579917497461520505255997)
      ·
        refine ⟨25717469061548070189470999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68579917497461520505255997 25717469061548070189470999)
        ·
          refine ⟨38576203592322105284206499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25717469061548070189470999 38576203592322105284206499)
          ·
            refine ⟨57864305388483157926309749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38576203592322105284206499 57864305388483157926309749)
            ·
              refine ⟨5424778630170296055591539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 57864305388483157926309749 5424778630170296055591539)
              ·
                refine ⟨8137167945255444083387309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5424778630170296055591539 8137167945255444083387309)
                ·
                  refine ⟨3051437979470791531270241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8137167945255444083387309 3051437979470791531270241)
                  ·
                    refine ⟨2288578484603093648452681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3051437979470791531270241 2288578484603093648452681)
                    ·
                      refine ⟨1716433863452320236339511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2288578484603093648452681 1716433863452320236339511)
                      ·
                        rfl

theorem cell23_3342743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 5, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 5, 1, 3, 2, 2].length) (baseStart_3342743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3342743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3342743 prefixEnd_3342743 := by exact prefixLift 3342743
  have htrace : WordTrace (prefixWord ++ tailWord_3342743) baseStart_3342743 baseEnd_3342743 := by
    simpa [prefixWord, tailWord_3342743, baseEnd_3342743] using wordTrace_append hprefix tailTrace_3342743
  have hstable : (prefixWord ++ tailWord_3342743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3342743).length < 2 ^ (prefixWord ++ tailWord_3342743).sum := by decide
  have hdescent : baseEnd_3342743 < baseStart_3342743 := by decide
  rcases family_descends (prefixWord ++ tailWord_3342743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3342760 : List Nat := [2, 1, 6, 1, 1, 3, 1, 2, 1, 1, 4]
def baseStart_3342760 : Nat := 118140960795 + 3342760 * 2 ^ 59
def prefixEnd_3342760 : Nat := 4983230072969 + 3 ^ 40 * 3342760 * 2
def baseEnd_3342760 : Nat := 1716442592623446669826933

theorem tailTrace_3342760 : CollatzResearch.WordTrace tailWord_3342760 prefixEnd_3342760 1716442592623446669826933 := by
  unfold tailWord_3342760
  simp only [CollatzResearch.WordTrace]
  refine ⟨60960236684879446400800867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81280315579839261867734489 60960236684879446400800867)
  ·
    refine ⟨91440355027319169601201301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60960236684879446400800867 91440355027319169601201301)
    ·
      refine ⟨4286266641905586075056311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 91440355027319169601201301 4286266641905586075056311)
      ·
        refine ⟨6429399962858379112584467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4286266641905586075056311 6429399962858379112584467)
        ·
          refine ⟨9644099944287568668876701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6429399962858379112584467 9644099944287568668876701)
          ·
            refine ⟨3616537479107838250828763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9644099944287568668876701 3616537479107838250828763)
            ·
              refine ⟨5424806218661757376243145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3616537479107838250828763 5424806218661757376243145)
              ·
                refine ⟨4068604663996318032182359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5424806218661757376243145 4068604663996318032182359)
                ·
                  refine ⟨6102906995994477048273539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4068604663996318032182359 6102906995994477048273539)
                  ·
                    refine ⟨9154360493991715572410309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6102906995994477048273539 9154360493991715572410309)
                    ·
                      refine ⟨1716442592623446669826933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9154360493991715572410309 1716442592623446669826933)
                      ·
                        rfl

theorem cell23_3342760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 3, 1, 2, 1, 1, 4].length) (baseStart_3342760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3342760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3342760 prefixEnd_3342760 := by exact prefixLift 3342760
  have htrace : WordTrace (prefixWord ++ tailWord_3342760) baseStart_3342760 baseEnd_3342760 := by
    simpa [prefixWord, tailWord_3342760, baseEnd_3342760] using wordTrace_append hprefix tailTrace_3342760
  have hstable : (prefixWord ++ tailWord_3342760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3342760).length < 2 ^ (prefixWord ++ tailWord_3342760).sum := by decide
  have hdescent : baseEnd_3342760 < baseStart_3342760 := by decide
  rcases family_descends (prefixWord ++ tailWord_3342760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3342780 : List Nat := [2, 2, 2, 4, 1, 2, 3, 1, 1, 2, 3]
def baseStart_3342780 : Nat := 118140960795 + 3342780 * 2 ^ 59
def prefixEnd_3342780 : Nat := 4983230072969 + 3 ^ 40 * 3342780 * 2
def baseEnd_3342780 : Nat := 1716452862236536591576841

theorem tailTrace_3342780 : CollatzResearch.WordTrace tailWord_3342780 prefixEnd_3342780 1716452862236536591576841 := by
  unfold tailWord_3342780
  simp only [CollatzResearch.WordTrace]
  refine ⟨60960601414843218108664897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81280801886457624144886529 60960601414843218108664897)
  ·
    refine ⟨45720451061132413581498673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60960601414843218108664897 45720451061132413581498673)
    ·
      refine ⟨34290338295849310186124005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45720451061132413581498673 34290338295849310186124005)
      ·
        refine ⟨6429438430471745659898251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34290338295849310186124005 6429438430471745659898251)
        ·
          refine ⟨9644157645707618489847377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6429438430471745659898251 9644157645707618489847377)
          ·
            refine ⟨7233118234280713867385533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9644157645707618489847377 7233118234280713867385533)
            ·
              refine ⟨2712419337855267700269575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7233118234280713867385533 2712419337855267700269575)
              ·
                refine ⟨4068629006782901550404363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2712419337855267700269575 4068629006782901550404363)
                ·
                  refine ⟨6102943510174352325606545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4068629006782901550404363 6102943510174352325606545)
                  ·
                    refine ⟨4577207632630764244204909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6102943510174352325606545 4577207632630764244204909)
                    ·
                      refine ⟨1716452862236536591576841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4577207632630764244204909 1716452862236536591576841)
                      ·
                        rfl

theorem cell23_3342780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 3, 1, 1, 2, 3].length) (baseStart_3342780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3342780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3342780 prefixEnd_3342780 := by exact prefixLift 3342780
  have htrace : WordTrace (prefixWord ++ tailWord_3342780) baseStart_3342780 baseEnd_3342780 := by
    simpa [prefixWord, tailWord_3342780, baseEnd_3342780] using wordTrace_append hprefix tailTrace_3342780
  have hstable : (prefixWord ++ tailWord_3342780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3342780).length < 2 ^ (prefixWord ++ tailWord_3342780).sum := by decide
  have hdescent : baseEnd_3342780 < baseStart_3342780 := by decide
  rcases family_descends (prefixWord ++ tailWord_3342780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3342809 : List Nat := [1, 2, 1, 2, 4, 1, 3, 1, 2, 6]
def baseStart_3342809 : Nat := 118140960795 + 3342809 * 2 ^ 59
def prefixEnd_3342809 : Nat := 4983230072969 + 3 ^ 40 * 3342809 * 2
def baseEnd_3342809 : Nat := 572155917725172326038069

theorem tailTrace_3342809 : CollatzResearch.WordTrace tailWord_3342809 prefixEnd_3342809 572155917725172326038069 := by
  unfold tailWord_3342809
  simp only [CollatzResearch.WordTrace]
  refine ⟨121922260546581374170135481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81281507031054249446756987 121922260546581374170135481)
  ·
    refine ⟨91441695409936030627601611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121922260546581374170135481 91441695409936030627601611)
    ·
      refine ⟨137162543114904045941402417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91441695409936030627601611 137162543114904045941402417)
      ·
        refine ⟨102871907336178034456051813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137162543114904045941402417 102871907336178034456051813)
        ·
          refine ⟨19288482625533381460509715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 102871907336178034456051813 19288482625533381460509715)
          ·
            refine ⟨28932723938300072190764573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19288482625533381460509715 28932723938300072190764573)
            ·
              refine ⟨10849771476862527071536715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28932723938300072190764573 10849771476862527071536715)
              ·
                refine ⟨16274657215293790607305073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10849771476862527071536715 16274657215293790607305073)
                ·
                  refine ⟨12205992911470342955478805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16274657215293790607305073 12205992911470342955478805)
                  ·
                    refine ⟨572155917725172326038069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12205992911470342955478805 572155917725172326038069)
                    ·
                      rfl

theorem cell23_3342809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 3, 1, 2, 6].length) (baseStart_3342809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3342809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3342809 prefixEnd_3342809 := by exact prefixLift 3342809
  have htrace : WordTrace (prefixWord ++ tailWord_3342809) baseStart_3342809 baseEnd_3342809 := by
    simpa [prefixWord, tailWord_3342809, baseEnd_3342809] using wordTrace_append hprefix tailTrace_3342809
  have hstable : (prefixWord ++ tailWord_3342809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3342809).length < 2 ^ (prefixWord ++ tailWord_3342809).sum := by decide
  have hdescent : baseEnd_3342809 < baseStart_3342809 := by decide
  rcases family_descends (prefixWord ++ tailWord_3342809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3342833 : List Nat := [1, 2, 2, 2, 3, 1, 2, 2, 4, 2, 2]
def baseStart_3342833 : Nat := 118140960795 + 3342833 * 2 ^ 59
def prefixEnd_3342833 : Nat := 4983230072969 + 3 ^ 40 * 3342833 * 2
def baseEnd_3342833 : Nat := 1716480076711224884214097

theorem tailTrace_3342833 : CollatzResearch.WordTrace tailWord_3342833 prefixEnd_3342833 1716480076711224884214097 := by
  unfold tailWord_3342833
  simp only [CollatzResearch.WordTrace]
  refine ⟨121923135898494426269009153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81282090598996284179339435 121923135898494426269009153)
  ·
    refine ⟨91442351923870819701756865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121923135898494426269009153 91442351923870819701756865)
    ·
      refine ⟨68581763942903114776317649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91442351923870819701756865 68581763942903114776317649)
      ·
        refine ⟨51436322957177336082238237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68581763942903114776317649 51436322957177336082238237)
        ·
          refine ⟨19288621108941501030839339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51436322957177336082238237 19288621108941501030839339)
          ·
            refine ⟨28932931663412251546259009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19288621108941501030839339 28932931663412251546259009)
            ·
              refine ⟨21699698747559188659694257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28932931663412251546259009 21699698747559188659694257)
              ·
                refine ⟨16274774060669391494770693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21699698747559188659694257 16274774060669391494770693)
                ·
                  refine ⟨3051520136375510905269505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16274774060669391494770693 3051520136375510905269505)
                  ·
                    refine ⟨2288640102281633178952129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3051520136375510905269505 2288640102281633178952129)
                    ·
                      refine ⟨1716480076711224884214097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2288640102281633178952129 1716480076711224884214097)
                      ·
                        rfl

theorem cell23_3342833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 2, 4, 2, 2].length) (baseStart_3342833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3342833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3342833 prefixEnd_3342833 := by exact prefixLift 3342833
  have htrace : WordTrace (prefixWord ++ tailWord_3342833) baseStart_3342833 baseEnd_3342833 := by
    simpa [prefixWord, tailWord_3342833, baseEnd_3342833] using wordTrace_append hprefix tailTrace_3342833
  have hstable : (prefixWord ++ tailWord_3342833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3342833).length < 2 ^ (prefixWord ++ tailWord_3342833).sum := by decide
  have hdescent : baseEnd_3342833 < baseStart_3342833 := by decide
  rcases family_descends (prefixWord ++ tailWord_3342833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3342837 : List Nat := [1, 3, 5, 1, 2, 1, 1, 3, 1, 3, 2]
def baseStart_3342837 : Nat := 118140960795 + 3342837 * 2 ^ 59
def prefixEnd_3342837 : Nat := 4983230072969 + 3 ^ 40 * 3342837 * 2
def baseEnd_3342837 : Nat := 1716482130633842868564079

theorem tailTrace_3342837 : CollatzResearch.WordTrace tailWord_3342837 prefixEnd_3342837 1716482130633842868564079 := by
  unfold tailWord_3342837
  simp only [CollatzResearch.WordTrace]
  refine ⟨121923281790479934952154765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81282187860319956634769843 121923281790479934952154765)
  ·
    refine ⟨45721230671429975607058037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121923281790479934952154765 45721230671429975607058037)
    ·
      refine ⟨4286365375446560213161691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 45721230671429975607058037 4286365375446560213161691)
      ·
        refine ⟨6429548063169840319742537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4286365375446560213161691 6429548063169840319742537)
        ·
          refine ⟨4822161047377380239806903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6429548063169840319742537 4822161047377380239806903)
          ·
            refine ⟨7233241571066070359710355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4822161047377380239806903 7233241571066070359710355)
            ·
              refine ⟨10849862356599105539565533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7233241571066070359710355 10849862356599105539565533)
              ·
                refine ⟨4068698383724664577337075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10849862356599105539565533 4068698383724664577337075)
                ·
                  refine ⟨6103047575586996866005613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4068698383724664577337075 6103047575586996866005613)
                  ·
                    refine ⟨2288642840845123824752105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6103047575586996866005613 2288642840845123824752105)
                    ·
                      refine ⟨1716482130633842868564079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2288642840845123824752105 1716482130633842868564079)
                      ·
                        rfl

theorem cell23_3342837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 1, 3, 1, 3, 2].length) (baseStart_3342837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3342837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3342837 prefixEnd_3342837 := by exact prefixLift 3342837
  have htrace : WordTrace (prefixWord ++ tailWord_3342837) baseStart_3342837 baseEnd_3342837 := by
    simpa [prefixWord, tailWord_3342837, baseEnd_3342837] using wordTrace_append hprefix tailTrace_3342837
  have hstable : (prefixWord ++ tailWord_3342837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3342837).length < 2 ^ (prefixWord ++ tailWord_3342837).sum := by decide
  have hdescent : baseEnd_3342837 < baseStart_3342837 := by decide
  rcases family_descends (prefixWord ++ tailWord_3342837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3342869 : List Nat := [1, 3, 2, 1, 3, 1, 1, 1, 3, 7]
def baseStart_3342869 : Nat := 118140960795 + 3342869 * 2 ^ 59
def prefixEnd_3342869 : Nat := 4983230072969 + 3 ^ 40 * 3342869 * 2
def baseEnd_3342869 : Nat := 572166187338262247787977

theorem tailTrace_3342869 : CollatzResearch.WordTrace tailWord_3342869 prefixEnd_3342869 572166187338262247787977 := by
  unfold tailWord_3342869
  simp only [CollatzResearch.WordTrace]
  refine ⟨121924448926364004417319661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81282965950909336278213107 121924448926364004417319661)
  ·
    refine ⟨45721668347386501656494873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121924448926364004417319661 45721668347386501656494873)
    ·
      refine ⟨34291251260539876242371155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45721668347386501656494873 34291251260539876242371155)
      ·
        refine ⟨51436876890809814363556733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34291251260539876242371155 51436876890809814363556733)
        ·
          refine ⟨19288828834053680386333775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51436876890809814363556733 19288828834053680386333775)
          ·
            refine ⟨28933243251080520579500663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19288828834053680386333775 28933243251080520579500663)
            ·
              refine ⟨43399864876620780869250995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28933243251080520579500663 43399864876620780869250995)
              ·
                refine ⟨65099797314931171303876493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43399864876620780869250995 65099797314931171303876493)
                ·
                  refine ⟨24412423993099189238953685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 65099797314931171303876493 24412423993099189238953685)
                  ·
                    refine ⟨572166187338262247787977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24412423993099189238953685 572166187338262247787977)
                    ·
                      rfl

theorem cell23_3342869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 1, 3, 7].length) (baseStart_3342869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3342869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3342869 prefixEnd_3342869 := by exact prefixLift 3342869
  have htrace : WordTrace (prefixWord ++ tailWord_3342869) baseStart_3342869 baseEnd_3342869 := by
    simpa [prefixWord, tailWord_3342869, baseEnd_3342869] using wordTrace_append hprefix tailTrace_3342869
  have hstable : (prefixWord ++ tailWord_3342869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3342869).length < 2 ^ (prefixWord ++ tailWord_3342869).sum := by decide
  have hdescent : baseEnd_3342869 < baseStart_3342869 := by decide
  rcases family_descends (prefixWord ++ tailWord_3342869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3342879 : List Nat := [1, 1, 2, 4, 1, 1, 1, 2, 3, 2, 5]
def baseStart_3342879 : Nat := 118140960795 + 3342879 * 2 ^ 59
def prefixEnd_3342879 : Nat := 4983230072969 + 3 ^ 40 * 3342879 * 2
def baseEnd_3342879 : Nat := 1716503696821331704238885

theorem tailTrace_3342879 : CollatzResearch.WordTrace tailWord_3342879 prefixEnd_3342879 1716503696821331704238885 := by
  unfold tailWord_3342879
  simp only [CollatzResearch.WordTrace]
  refine ⟨121924813656327776125183691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81283209104218517416789127 121924813656327776125183691)
  ·
    refine ⟨182887220484491664187775537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121924813656327776125183691 182887220484491664187775537)
    ·
      refine ⟨137165415363368748140831653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182887220484491664187775537 137165415363368748140831653)
      ·
        refine ⟨25718515380631640276405935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 137165415363368748140831653 25718515380631640276405935)
        ·
          refine ⟨38577773070947460414608903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25718515380631640276405935 38577773070947460414608903)
          ·
            refine ⟨57866659606421190621913355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38577773070947460414608903 57866659606421190621913355)
            ·
              refine ⟨86799989409631785932870033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57866659606421190621913355 86799989409631785932870033)
              ·
                refine ⟨65099992057223839449652525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86799989409631785932870033 65099992057223839449652525)
                ·
                  refine ⟨24412497021458939793619697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 65099992057223839449652525 24412497021458939793619697)
                  ·
                    refine ⟨18309372766094204845214773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24412497021458939793619697 18309372766094204845214773)
                    ·
                      refine ⟨1716503696821331704238885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18309372766094204845214773 1716503696821331704238885)
                      ·
                        rfl

theorem cell23_3342879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 2, 3, 2, 5].length) (baseStart_3342879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3342879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3342879 prefixEnd_3342879 := by exact prefixLift 3342879
  have htrace : WordTrace (prefixWord ++ tailWord_3342879) baseStart_3342879 baseEnd_3342879 := by
    simpa [prefixWord, tailWord_3342879, baseEnd_3342879] using wordTrace_append hprefix tailTrace_3342879
  have hstable : (prefixWord ++ tailWord_3342879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3342879).length < 2 ^ (prefixWord ++ tailWord_3342879).sum := by decide
  have hdescent : baseEnd_3342879 < baseStart_3342879 := by decide
  rcases family_descends (prefixWord ++ tailWord_3342879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3342890 : List Nat := [3, 1, 4, 1, 1, 4, 1, 3, 5]
def baseStart_3342890 : Nat := 118140960795 + 3342890 * 2 ^ 59
def prefixEnd_3342890 : Nat := 4983230072969 + 3 ^ 40 * 3342890 * 2
def baseEnd_3342890 : Nat := 190723260567614573466815

theorem tailTrace_3342890 : CollatzResearch.WordTrace tailWord_3342890 prefixEnd_3342890 190723260567614573466815 := by
  unfold tailWord_3342890
  simp only [CollatzResearch.WordTrace]
  refine ⟨30481303714821981250958531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81283476572858616669222749 30481303714821981250958531)
  ·
    refine ⟨45721955572232971876437797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30481303714821981250958531 45721955572232971876437797)
    ·
      refine ⟨8572866669793682226832087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45721955572232971876437797 8572866669793682226832087)
      ·
        refine ⟨12859300004690523340248131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8572866669793682226832087 12859300004690523340248131)
        ·
          refine ⟨19288950007035785010372197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12859300004690523340248131 19288950007035785010372197)
          ·
            refine ⟨3616678126319209689444787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19288950007035785010372197 3616678126319209689444787)
            ·
              refine ⟨5425017189478814534167181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3616678126319209689444787 5425017189478814534167181)
              ·
                refine ⟨2034381446054555450312693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5425017189478814534167181 2034381446054555450312693)
                ·
                  refine ⟨190723260567614573466815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2034381446054555450312693 190723260567614573466815)
                  ·
                    rfl

theorem cell23_3342890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 4, 1, 3, 5].length) (baseStart_3342890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3342890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3342890 prefixEnd_3342890 := by exact prefixLift 3342890
  have htrace : WordTrace (prefixWord ++ tailWord_3342890) baseStart_3342890 baseEnd_3342890 := by
    simpa [prefixWord, tailWord_3342890, baseEnd_3342890] using wordTrace_append hprefix tailTrace_3342890
  have hstable : (prefixWord ++ tailWord_3342890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3342890).length < 2 ^ (prefixWord ++ tailWord_3342890).sum := by decide
  have hdescent : baseEnd_3342890 < baseStart_3342890 := by decide
  rcases family_descends (prefixWord ++ tailWord_3342890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3342906 : List Nat := [3, 1, 1, 1, 3, 3, 1, 1, 4, 1, 4]
def baseStart_3342906 : Nat := 118140960795 + 3342906 * 2 ^ 59
def prefixEnd_3342906 : Nat := 4983230072969 + 3 ^ 40 * 3342906 * 2
def baseEnd_3342906 : Nat := 1716517560799003098601261

theorem tailTrace_3342906 : CollatzResearch.WordTrace tailWord_3342906 prefixEnd_3342906 1716517560799003098601261 := by
  unfold tailWord_3342906
  simp only [CollatzResearch.WordTrace]
  refine ⟨30481449606807489934104143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81283865618153306490944381 30481449606807489934104143)
  ·
    refine ⟨45722174410211234901156215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30481449606807489934104143 45722174410211234901156215)
    ·
      refine ⟨68583261615316852351734323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45722174410211234901156215 68583261615316852351734323)
      ·
        refine ⟨102874892422975278527601485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68583261615316852351734323 102874892422975278527601485)
        ·
          refine ⟨38578084658615729447850557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102874892422975278527601485 38578084658615729447850557)
          ·
            refine ⟨14466781746980898542943959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38578084658615729447850557 14466781746980898542943959)
            ·
              refine ⟨21700172620471347814415939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14466781746980898542943959 21700172620471347814415939)
              ·
                refine ⟨32550258930707021721623909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21700172620471347814415939 32550258930707021721623909)
                ·
                  refine ⟨6103173549507566572804483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32550258930707021721623909 6103173549507566572804483)
                  ·
                    refine ⟨9154760324261349859206725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6103173549507566572804483 9154760324261349859206725)
                    ·
                      refine ⟨1716517560799003098601261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9154760324261349859206725 1716517560799003098601261)
                      ·
                        rfl

theorem cell23_3342906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 1, 4, 1, 4].length) (baseStart_3342906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3342906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3342906 prefixEnd_3342906 := by exact prefixLift 3342906
  have htrace : WordTrace (prefixWord ++ tailWord_3342906) baseStart_3342906 baseEnd_3342906 := by
    simpa [prefixWord, tailWord_3342906, baseEnd_3342906] using wordTrace_append hprefix tailTrace_3342906
  have hstable : (prefixWord ++ tailWord_3342906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3342906).length < 2 ^ (prefixWord ++ tailWord_3342906).sum := by decide
  have hdescent : baseEnd_3342906 < baseStart_3342906 := by decide
  rcases family_descends (prefixWord ++ tailWord_3342906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3342926 : List Nat := [4, 1, 1, 1, 1, 2, 2, 1, 3, 4, 3]
def baseStart_3342926 : Nat := 118140960795 + 3342926 * 2 ^ 59
def prefixEnd_3342926 : Nat := 4983230072969 + 3 ^ 40 * 3342926 * 2
def baseEnd_3342926 : Nat := 1716527830412093020351169

theorem tailTrace_3342926 : CollatzResearch.WordTrace tailWord_3342926 prefixEnd_3342926 1716527830412093020351169 := by
  unfold tailWord_3342926
  simp only [CollatzResearch.WordTrace]
  refine ⟨15240815985894687894018079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81284351924771668768096421 15240815985894687894018079)
  ·
    refine ⟨22861223978842031841027119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15240815985894687894018079 22861223978842031841027119)
    ·
      refine ⟨34291835968263047761540679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22861223978842031841027119 34291835968263047761540679)
      ·
        refine ⟨51437753952394571642311019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34291835968263047761540679 51437753952394571642311019)
        ·
          refine ⟨77156630928591857463466529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51437753952394571642311019 77156630928591857463466529)
          ·
            refine ⟨57867473196443893097599897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77156630928591857463466529 57867473196443893097599897)
            ·
              refine ⟨43400604897332919823199923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57867473196443893097599897 43400604897332919823199923)
              ·
                refine ⟨65100907345999379734799885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43400604897332919823199923 65100907345999379734799885)
                ·
                  refine ⟨24412840254749767400549957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 65100907345999379734799885 24412840254749767400549957)
                  ·
                    refine ⟨4577407547765581387603117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24412840254749767400549957 4577407547765581387603117)
                    ·
                      refine ⟨1716527830412093020351169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4577407547765581387603117 1716527830412093020351169)
                      ·
                        rfl

theorem cell23_3342926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 1, 3, 4, 3].length) (baseStart_3342926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3342926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3342926 prefixEnd_3342926 := by exact prefixLift 3342926
  have htrace : WordTrace (prefixWord ++ tailWord_3342926) baseStart_3342926 baseEnd_3342926 := by
    simpa [prefixWord, tailWord_3342926, baseEnd_3342926] using wordTrace_append hprefix tailTrace_3342926
  have hstable : (prefixWord ++ tailWord_3342926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3342926).length < 2 ^ (prefixWord ++ tailWord_3342926).sum := by decide
  have hdescent : baseEnd_3342926 < baseStart_3342926 := by decide
  rcases family_descends (prefixWord ++ tailWord_3342926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3342940 : List Nat := [2, 2, 4, 1, 3, 1, 2, 1, 2, 1, 4]
def baseStart_3342940 : Nat := 118140960795 + 3342940 * 2 ^ 59
def prefixEnd_3342940 : Nat := 4983230072969 + 3 ^ 40 * 3342940 * 2
def baseEnd_3342940 : Nat := 1716535019141255965576105

theorem tailTrace_3342940 : CollatzResearch.WordTrace tailWord_3342940 prefixEnd_3342940 1716535019141255965576105 := by
  unfold tailWord_3342940
  simp only [CollatzResearch.WordTrace]
  refine ⟨60963519254553391771577137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81284692339404522362102849 60963519254553391771577137)
  ·
    refine ⟨45722639440915043828682853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60963519254553391771577137 45722639440915043828682853)
    ·
      refine ⟨8572994895171570717878035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45722639440915043828682853 8572994895171570717878035)
      ·
        refine ⟨12859492342757356076817053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8572994895171570717878035 12859492342757356076817053)
        ·
          refine ⟨4822309628534008528806395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12859492342757356076817053 4822309628534008528806395)
          ·
            refine ⟨7233464442801012793209593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4822309628534008528806395 7233464442801012793209593)
            ·
              refine ⟨5425098332100759594907195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7233464442801012793209593 5425098332100759594907195)
              ·
                refine ⟨8137647498151139392360793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5425098332100759594907195 8137647498151139392360793)
                ·
                  refine ⟨6103235623613354544270595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8137647498151139392360793 6103235623613354544270595)
                  ·
                    refine ⟨9154853435420031816405893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6103235623613354544270595 9154853435420031816405893)
                    ·
                      refine ⟨1716535019141255965576105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9154853435420031816405893 1716535019141255965576105)
                      ·
                        rfl

theorem cell23_3342940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 2, 1, 2, 1, 4].length) (baseStart_3342940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3342940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3342940 prefixEnd_3342940 := by exact prefixLift 3342940
  have htrace : WordTrace (prefixWord ++ tailWord_3342940) baseStart_3342940 baseEnd_3342940 := by
    simpa [prefixWord, tailWord_3342940, baseEnd_3342940] using wordTrace_append hprefix tailTrace_3342940
  have hstable : (prefixWord ++ tailWord_3342940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3342940).length < 2 ^ (prefixWord ++ tailWord_3342940).sum := by decide
  have hdescent : baseEnd_3342940 < baseStart_3342940 := by decide
  rcases family_descends (prefixWord ++ tailWord_3342940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3342976 : List Nat := [2, 1, 1, 2, 1, 5, 1, 2, 3, 5]
def baseStart_3342976 : Nat := 118140960795 + 3342976 * 2 ^ 59
def prefixEnd_3342976 : Nat := 4983230072969 + 3 ^ 40 * 3342976 * 2
def baseEnd_3342976 : Nat := 572184501481605941575313

theorem tailTrace_3342976 : CollatzResearch.WordTrace tailWord_3342976 prefixEnd_3342976 572184501481605941575313 := by
  unfold tailWord_3342976
  simp only [CollatzResearch.WordTrace]
  refine ⟨60964175768488180845732391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81285567691317574460976521 60964175768488180845732391)
  ·
    refine ⟨91446263652732271268598587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60964175768488180845732391 91446263652732271268598587)
    ·
      refine ⟨137169395479098406902897881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91446263652732271268598587 137169395479098406902897881)
      ·
        refine ⟨102877046609323805177173411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137169395479098406902897881 102877046609323805177173411)
        ·
          refine ⟨154315569913985707765760117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102877046609323805177173411 154315569913985707765760117)
          ·
            refine ⟨14467084679436160103040011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 154315569913985707765760117 14467084679436160103040011)
            ·
              refine ⟨21700627019154240154560017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14467084679436160103040011 21700627019154240154560017)
              ·
                refine ⟨16275470264365680115920013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21700627019154240154560017 16275470264365680115920013)
                ·
                  refine ⟨6103301349137130043470005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16275470264365680115920013 6103301349137130043470005)
                  ·
                    refine ⟨572184501481605941575313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6103301349137130043470005 572184501481605941575313)
                    ·
                      rfl

theorem cell23_3342976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 2, 3, 5].length) (baseStart_3342976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3342976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3342976 prefixEnd_3342976 := by exact prefixLift 3342976
  have htrace : WordTrace (prefixWord ++ tailWord_3342976) baseStart_3342976 baseEnd_3342976 := by
    simpa [prefixWord, tailWord_3342976, baseEnd_3342976] using wordTrace_append hprefix tailTrace_3342976
  have hstable : (prefixWord ++ tailWord_3342976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3342976).length < 2 ^ (prefixWord ++ tailWord_3342976).sum := by decide
  have hdescent : baseEnd_3342976 < baseStart_3342976 := by decide
  rcases family_descends (prefixWord ++ tailWord_3342976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3342983 : List Nat := [1, 1, 4, 2, 1, 2, 2, 2, 1, 5, 2]
def baseStart_3342983 : Nat := 118140960795 + 3342983 * 2 ^ 59
def prefixEnd_3342983 : Nat := 4983230072969 + 3 ^ 40 * 3342983 * 2
def baseEnd_3342983 : Nat := 1716557098809399297338407

theorem tailTrace_3342983 : CollatzResearch.WordTrace tailWord_3342983 prefixEnd_3342983 1716557098809399297338407 := by
  unfold tailWord_3342983
  simp only [CollatzResearch.WordTrace]
  refine ⟨121928606847951001886969603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81285737898634001257979735 121928606847951001886969603)
  ·
    refine ⟨182892910271926502830454405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121928606847951001886969603 182892910271926502830454405)
    ·
      refine ⟨34292420675986219280710201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 182892910271926502830454405 34292420675986219280710201)
      ·
        refine ⟨25719315506989664460532651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34292420675986219280710201 25719315506989664460532651)
        ·
          refine ⟨38578973260484496690798977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25719315506989664460532651 38578973260484496690798977)
          ·
            refine ⟨28934229945363372518099233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38578973260484496690798977 28934229945363372518099233)
            ·
              refine ⟨21700672459022529388574425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28934229945363372518099233 21700672459022529388574425)
              ·
                refine ⟨16275504344266897041430819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21700672459022529388574425 16275504344266897041430819)
                ·
                  refine ⟨24413256516400345562146229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16275504344266897041430819 24413256516400345562146229)
                  ·
                    refine ⟨2288742798412532396451209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 24413256516400345562146229 2288742798412532396451209)
                    ·
                      refine ⟨1716557098809399297338407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2288742798412532396451209 1716557098809399297338407)
                      ·
                        rfl

theorem cell23_3342983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 2, 1, 5, 2].length) (baseStart_3342983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3342983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3342983 prefixEnd_3342983 := by exact prefixLift 3342983
  have htrace : WordTrace (prefixWord ++ tailWord_3342983) baseStart_3342983 baseEnd_3342983 := by
    simpa [prefixWord, tailWord_3342983, baseEnd_3342983] using wordTrace_append hprefix tailTrace_3342983
  have hstable : (prefixWord ++ tailWord_3342983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3342983).length < 2 ^ (prefixWord ++ tailWord_3342983).sum := by decide
  have hdescent : baseEnd_3342983 < baseStart_3342983 := by decide
  rcases family_descends (prefixWord ++ tailWord_3342983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3342990 : List Nat := [4, 1, 1, 3, 1, 1, 3, 2, 3, 1, 3]
def baseStart_3342990 : Nat := 118140960795 + 3342990 * 2 ^ 59
def prefixEnd_3342990 : Nat := 4983230072969 + 3 ^ 40 * 3342990 * 2
def baseEnd_3342990 : Nat := 1716560693173980769950875

theorem tailTrace_3342990 : CollatzResearch.WordTrace tailWord_3342990 prefixEnd_3342990 1716560693173980769950875 := by
  unfold tailWord_3342990
  simp only [CollatzResearch.WordTrace]
  refine ⟨15241107769865705260309303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81285908105950428054982949 15241107769865705260309303)
  ·
    refine ⟨22861661654798557890463955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15241107769865705260309303 22861661654798557890463955)
    ·
      refine ⟨34292492482197836835695933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22861661654798557890463955 34292492482197836835695933)
      ·
        refine ⟨12859684680824188813385975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34292492482197836835695933 12859684680824188813385975)
        ·
          refine ⟨19289527021236283220078963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12859684680824188813385975 19289527021236283220078963)
          ·
            refine ⟨28934290531854424830118445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19289527021236283220078963 28934290531854424830118445)
            ·
              refine ⟨10850358949445409311294417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28934290531854424830118445 10850358949445409311294417)
              ·
                refine ⟨8137769212084056983470813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10850358949445409311294417 8137769212084056983470813)
                ·
                  refine ⟨3051663454531521368801555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8137769212084056983470813 3051663454531521368801555)
                  ·
                    refine ⟨4577495181797282053202333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3051663454531521368801555 4577495181797282053202333)
                    ·
                      refine ⟨1716560693173980769950875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4577495181797282053202333 1716560693173980769950875)
                      ·
                        rfl

theorem cell23_3342990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 3, 2, 3, 1, 3].length) (baseStart_3342990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3342990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3342990 prefixEnd_3342990 := by exact prefixLift 3342990
  have htrace : WordTrace (prefixWord ++ tailWord_3342990) baseStart_3342990 baseEnd_3342990 := by
    simpa [prefixWord, tailWord_3342990, baseEnd_3342990] using wordTrace_append hprefix tailTrace_3342990
  have hstable : (prefixWord ++ tailWord_3342990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3342990).length < 2 ^ (prefixWord ++ tailWord_3342990).sum := by decide
  have hdescent : baseEnd_3342990 < baseStart_3342990 := by decide
  rcases family_descends (prefixWord ++ tailWord_3342990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3343023 : List Nat := [1, 1, 2, 1, 2, 6, 1, 1, 4, 4]
def baseStart_3343023 : Nat := 118140960795 + 3343023 * 2 ^ 59
def prefixEnd_3343023 : Nat := 4983230072969 + 3 ^ 40 * 3343023 * 2
def baseEnd_3343023 : Nat := 572192546011859713612741

theorem tailTrace_3343023 : CollatzResearch.WordTrace tailWord_3343023 prefixEnd_3343023 572192546011859713612741 := by
  unfold tailWord_3343023
  simp only [CollatzResearch.WordTrace]
  refine ⟨121930065767806088718425723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81286710511870725812283815 121930065767806088718425723)
  ·
    refine ⟨182895098651709133077638585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121930065767806088718425723 182895098651709133077638585)
    ·
      refine ⟨137171323988781849808228939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182895098651709133077638585 137171323988781849808228939)
      ·
        refine ⟨205756985983172774712343409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137171323988781849808228939 205756985983172774712343409)
        ·
          refine ⟨154317739487379581034257557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 205756985983172774712343409 154317739487379581034257557)
          ·
            refine ⟨7233644038470917860980823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 154317739487379581034257557 7233644038470917860980823)
            ·
              refine ⟨10850466057706376791471235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7233644038470917860980823 10850466057706376791471235)
              ·
                refine ⟨16275699086559565187206853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10850466057706376791471235 16275699086559565187206853)
                ·
                  refine ⟨3051693578729918472601285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16275699086559565187206853 3051693578729918472601285)
                  ·
                    refine ⟨572192546011859713612741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3051693578729918472601285 572192546011859713612741)
                    ·
                      rfl

theorem cell23_3343023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 1, 1, 4, 4].length) (baseStart_3343023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3343023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3343023 prefixEnd_3343023 := by exact prefixLift 3343023
  have htrace : WordTrace (prefixWord ++ tailWord_3343023) baseStart_3343023 baseEnd_3343023 := by
    simpa [prefixWord, tailWord_3343023, baseEnd_3343023] using wordTrace_append hprefix tailTrace_3343023
  have hstable : (prefixWord ++ tailWord_3343023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3343023).length < 2 ^ (prefixWord ++ tailWord_3343023).sum := by decide
  have hdescent : baseEnd_3343023 < baseStart_3343023 := by decide
  rcases family_descends (prefixWord ++ tailWord_3343023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3343026 : List Nat := [3, 2, 1, 1, 1, 2, 1, 4, 1, 1, 6]
def baseStart_3343026 : Nat := 118140960795 + 3343026 * 2 ^ 59
def prefixEnd_3343026 : Nat := 4983230072969 + 3 ^ 40 * 3343026 * 2
def baseEnd_3343026 : Nat := 1716579178477542629100709

theorem tailTrace_3343026 : CollatzResearch.WordTrace tailWord_3343026 prefixEnd_3343026 1716579178477542629100709 := by
  unfold tailWord_3343026
  simp only [CollatzResearch.WordTrace]
  refine ⟨30482543796698805057696233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81286783457863480153856621 30482543796698805057696233)
  ·
    refine ⟨22861907847524103793272175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30482543796698805057696233 22861907847524103793272175)
    ·
      refine ⟨34292861771286155689908263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22861907847524103793272175 34292861771286155689908263)
      ·
        refine ⟨51439292656929233534862395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34292861771286155689908263 51439292656929233534862395)
        ·
          refine ⟨77158938985393850302293593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51439292656929233534862395 77158938985393850302293593)
          ·
            refine ⟨57869204239045387726720195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77158938985393850302293593 57869204239045387726720195)
            ·
              refine ⟨86803806358568081590080293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57869204239045387726720195 86803806358568081590080293)
              ·
                refine ⟨16275713692231515298140055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 86803806358568081590080293 16275713692231515298140055)
                ·
                  refine ⟨24413570538347272947210083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16275713692231515298140055 24413570538347272947210083)
                  ·
                    refine ⟨36620355807520909420815125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24413570538347272947210083 36620355807520909420815125)
                    ·
                      refine ⟨1716579178477542629100709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 36620355807520909420815125 1716579178477542629100709)
                      ·
                        rfl

theorem cell23_3343026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 4, 1, 1, 6].length) (baseStart_3343026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3343026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3343026 prefixEnd_3343026 := by exact prefixLift 3343026
  have htrace : WordTrace (prefixWord ++ tailWord_3343026) baseStart_3343026 baseEnd_3343026 := by
    simpa [prefixWord, tailWord_3343026, baseEnd_3343026] using wordTrace_append hprefix tailTrace_3343026
  have hstable : (prefixWord ++ tailWord_3343026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3343026).length < 2 ^ (prefixWord ++ tailWord_3343026).sum := by decide
  have hdescent : baseEnd_3343026 < baseStart_3343026 := by decide
  rcases family_descends (prefixWord ++ tailWord_3343026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3343036 : List Nat := [2, 2, 2, 3, 1, 1, 2, 10]
def baseStart_3343036 : Nat := 118140960795 + 3343036 * 2 ^ 59
def prefixEnd_3343036 : Nat := 4983230072969 + 3 ^ 40 * 3343036 * 2
def baseEnd_3343036 : Nat := 63577196788299540369469

theorem tailTrace_3343036 : CollatzResearch.WordTrace tailWord_3343036 prefixEnd_3343036 63577196788299540369469 := by
  unfold tailWord_3343036
  simp only [CollatzResearch.WordTrace]
  refine ⟨60965269958379495969324481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81287026611172661292432641 60965269958379495969324481)
  ·
    refine ⟨45723952468784621976993361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60965269958379495969324481 45723952468784621976993361)
    ·
      refine ⟨34292964351588466482745021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45723952468784621976993361 34292964351588466482745021)
      ·
        refine ⟨12859861631845674931029383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34292964351588466482745021 12859861631845674931029383)
        ·
          refine ⟨19289792447768512396544075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12859861631845674931029383 19289792447768512396544075)
          ·
            refine ⟨28934688671652768594816113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19289792447768512396544075 28934688671652768594816113)
            ·
              refine ⟨21701016503739576446112085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28934688671652768594816113 21701016503739576446112085)
              ·
                refine ⟨63577196788299540369469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 21701016503739576446112085 63577196788299540369469)
                ·
                  rfl

theorem cell23_3343036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 10].length) (baseStart_3343036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3343036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3343036 prefixEnd_3343036 := by exact prefixLift 3343036
  have htrace : WordTrace (prefixWord ++ tailWord_3343036) baseStart_3343036 baseEnd_3343036 := by
    simpa [prefixWord, tailWord_3343036, baseEnd_3343036] using wordTrace_append hprefix tailTrace_3343036
  have hstable : (prefixWord ++ tailWord_3343036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3343036).length < 2 ^ (prefixWord ++ tailWord_3343036).sum := by decide
  have hdescent : baseEnd_3343036 < baseStart_3343036 := by decide
  rcases family_descends (prefixWord ++ tailWord_3343036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3343050 : List Nat := [3, 1, 2, 1, 4, 1, 1, 4, 1, 2, 3]
def baseStart_3343050 : Nat := 118140960795 + 3343050 * 2 ^ 59
def prefixEnd_3343050 : Nat := 4983230072969 + 3 ^ 40 * 3343050 * 2
def baseEnd_3343050 : Nat := 1716591502013250535200599

theorem tailTrace_3343050 : CollatzResearch.WordTrace tailWord_3343050 prefixEnd_3343050 1716591502013250535200599 := by
  unfold tailWord_3343050
  simp only [CollatzResearch.WordTrace]
  refine ⟨30482762634677068082414651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81287367025805514886439069 30482762634677068082414651)
  ·
    refine ⟨45724143952015602123621977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30482762634677068082414651 45724143952015602123621977)
    ·
      refine ⟨34293107964011701592716483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45724143952015602123621977 34293107964011701592716483)
      ·
        refine ⟨51439661946017552389074725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34293107964011701592716483 51439661946017552389074725)
        ·
          refine ⟨9644936614878291072951511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51439661946017552389074725 9644936614878291072951511)
          ·
            refine ⟨14467404922317436609427267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9644936614878291072951511 14467404922317436609427267)
            ·
              refine ⟨21701107383476154914140901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14467404922317436609427267 21701107383476154914140901)
              ·
                refine ⟨4068957634401779046401419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21701107383476154914140901 4068957634401779046401419)
                ·
                  refine ⟨6103436451602668569602129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4068957634401779046401419 6103436451602668569602129)
                  ·
                    refine ⟨4577577338702001427201597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6103436451602668569602129 4577577338702001427201597)
                    ·
                      refine ⟨1716591502013250535200599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4577577338702001427201597 1716591502013250535200599)
                      ·
                        rfl

theorem cell23_3343050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 4, 1, 2, 3].length) (baseStart_3343050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3343050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3343050 prefixEnd_3343050 := by exact prefixLift 3343050
  have htrace : WordTrace (prefixWord ++ tailWord_3343050) baseStart_3343050 baseEnd_3343050 := by
    simpa [prefixWord, tailWord_3343050, baseEnd_3343050] using wordTrace_append hprefix tailTrace_3343050
  have hstable : (prefixWord ++ tailWord_3343050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3343050).length < 2 ^ (prefixWord ++ tailWord_3343050).sum := by decide
  have hdescent : baseEnd_3343050 < baseStart_3343050 := by decide
  rcases family_descends (prefixWord ++ tailWord_3343050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3343064 : List Nat := [2, 1, 2, 2, 3, 2, 3, 3, 1, 2, 2]
def baseStart_3343064 : Nat := 118140960795 + 3343064 * 2 ^ 59
def prefixEnd_3343064 : Nat := 4983230072969 + 3 ^ 40 * 3343064 * 2
def baseEnd_3343064 : Nat := 1716598690742413480425535

theorem tailTrace_3343064 : CollatzResearch.WordTrace tailWord_3343064 prefixEnd_3343064 1716598690742413480425535 := by
  unfold tailWord_3343064
  simp only [CollatzResearch.WordTrace]
  refine ⟨60965780580328776360334123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81287707440438368480445497 60965780580328776360334123)
  ·
    refine ⟨91448670870493164540501185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60965780580328776360334123 91448670870493164540501185)
    ·
      refine ⟨68586503152869873405375889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91448670870493164540501185 68586503152869873405375889)
      ·
        refine ⟨51439877364652405054031917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68586503152869873405375889 51439877364652405054031917)
        ·
          refine ⟨19289954011744651895261969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51439877364652405054031917 19289954011744651895261969)
          ·
            refine ⟨14467465508808488921446477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19289954011744651895261969 14467465508808488921446477)
            ·
              refine ⟨5425299565803183345542429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14467465508808488921446477 5425299565803183345542429)
              ·
                refine ⟨2034487337176193754578411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5425299565803183345542429 2034487337176193754578411)
                ·
                  refine ⟨3051731005764290631867617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2034487337176193754578411 3051731005764290631867617)
                  ·
                    refine ⟨2288798254323217973900713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3051731005764290631867617 2288798254323217973900713)
                    ·
                      refine ⟨1716598690742413480425535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2288798254323217973900713 1716598690742413480425535)
                      ·
                        rfl

theorem cell23_3343064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 3, 3, 1, 2, 2].length) (baseStart_3343064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3343064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3343064 prefixEnd_3343064 := by exact prefixLift 3343064
  have htrace : WordTrace (prefixWord ++ tailWord_3343064) baseStart_3343064 baseEnd_3343064 := by
    simpa [prefixWord, tailWord_3343064, baseEnd_3343064] using wordTrace_append hprefix tailTrace_3343064
  have hstable : (prefixWord ++ tailWord_3343064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3343064).length < 2 ^ (prefixWord ++ tailWord_3343064).sum := by decide
  have hdescent : baseEnd_3343064 < baseStart_3343064 := by decide
  rcases family_descends (prefixWord ++ tailWord_3343064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3343096 : List Nat := [2, 1, 2, 1, 1, 2, 4, 1, 1, 8]
def baseStart_3343096 : Nat := 118140960795 + 3343096 * 2 ^ 59
def prefixEnd_3343096 : Nat := 4983230072969 + 3 ^ 40 * 3343096 * 2
def baseEnd_3343096 : Nat := 572205040707785785075129

theorem tailTrace_3343096 : CollatzResearch.WordTrace tailWord_3343096 prefixEnd_3343096 572205040707785785075129 := by
  unfold tailWord_3343096
  simp only [CollatzResearch.WordTrace]
  refine ⟨60966364148270811092916571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81288485531027748123888761 60966364148270811092916571)
  ·
    refine ⟨91449546222406216639374857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60966364148270811092916571 91449546222406216639374857)
    ·
      refine ⟨68587159666804662479531143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91449546222406216639374857 68587159666804662479531143)
      ·
        refine ⟨102880739500206993719296715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68587159666804662479531143 102880739500206993719296715)
        ·
          refine ⟨154321109250310490578945073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102880739500206993719296715 154321109250310490578945073)
          ·
            refine ⟨115740831937732867934208805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 154321109250310490578945073 115740831937732867934208805)
            ·
              refine ⟨21701405988324912737664151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 115740831937732867934208805 21701405988324912737664151)
              ·
                refine ⟨32552108982487369106496227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21701405988324912737664151 32552108982487369106496227)
                ·
                  refine ⟨48828163473731053659744341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32552108982487369106496227 48828163473731053659744341)
                  ·
                    refine ⟨572205040707785785075129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 48828163473731053659744341 572205040707785785075129)
                    ·
                      rfl

theorem cell23_3343096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 1, 1, 8].length) (baseStart_3343096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3343096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3343096 prefixEnd_3343096 := by exact prefixLift 3343096
  have htrace : WordTrace (prefixWord ++ tailWord_3343096) baseStart_3343096 baseEnd_3343096 := by
    simpa [prefixWord, tailWord_3343096, baseEnd_3343096] using wordTrace_append hprefix tailTrace_3343096
  have hstable : (prefixWord ++ tailWord_3343096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3343096).length < 2 ^ (prefixWord ++ tailWord_3343096).sum := by decide
  have hdescent : baseEnd_3343096 < baseStart_3343096 := by decide
  rcases family_descends (prefixWord ++ tailWord_3343096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3343150 : List Nat := [4, 1, 3, 2, 1, 1, 1, 1, 1, 4, 4]
def baseStart_3343150 : Nat := 118140960795 + 3343150 * 2 ^ 59
def prefixEnd_3343150 : Nat := 4983230072969 + 3 ^ 40 * 3343150 * 2
def baseEnd_3343150 : Nat := 1716642850078700143950139

theorem tailTrace_3343150 : CollatzResearch.WordTrace tailWord_3343150 prefixEnd_3343150 1716642850078700143950139 := by
  unfold tailWord_3343150
  simp only [CollatzResearch.WordTrace]
  refine ⟨15241837229793248676037363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81289798558897326272199269 15241837229793248676037363)
  ·
    refine ⟨22862755844689873014056045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15241837229793248676037363 22862755844689873014056045)
    ·
      refine ⟨8573533441758702380271017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22862755844689873014056045 8573533441758702380271017)
      ·
        refine ⟨6430150081319026785203263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8573533441758702380271017 6430150081319026785203263)
        ·
          refine ⟨9645225121978540177804895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6430150081319026785203263 9645225121978540177804895)
          ·
            refine ⟨14467837682967810266707343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9645225121978540177804895 14467837682967810266707343)
            ·
              refine ⟨21701756524451715400061015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14467837682967810266707343 21701756524451715400061015)
              ·
                refine ⟨32552634786677573100091523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21701756524451715400061015 32552634786677573100091523)
                ·
                  refine ⟨48828952180016359650137285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32552634786677573100091523 48828952180016359650137285)
                  ·
                    refine ⟨9155428533753067434400741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 48828952180016359650137285 9155428533753067434400741)
                    ·
                      refine ⟨1716642850078700143950139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9155428533753067434400741 1716642850078700143950139)
                      ·
                        rfl

theorem cell23_3343150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 1, 1, 4, 4].length) (baseStart_3343150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3343150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3343150 prefixEnd_3343150 := by exact prefixLift 3343150
  have htrace : WordTrace (prefixWord ++ tailWord_3343150) baseStart_3343150 baseEnd_3343150 := by
    simpa [prefixWord, tailWord_3343150, baseEnd_3343150] using wordTrace_append hprefix tailTrace_3343150
  have hstable : (prefixWord ++ tailWord_3343150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3343150).length < 2 ^ (prefixWord ++ tailWord_3343150).sum := by decide
  have hdescent : baseEnd_3343150 < baseStart_3343150 := by decide
  rcases family_descends (prefixWord ++ tailWord_3343150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3343173 : List Nat := [1, 3, 1, 1, 1, 2, 2, 5, 2, 5]
def baseStart_3343173 : Nat := 118140960795 + 3343173 * 2 ^ 59
def prefixEnd_3343173 : Nat := 4983230072969 + 3 ^ 40 * 3343173 * 2
def baseEnd_3343173 : Nat := 572218220044584517987511

theorem tailTrace_3343173 : CollatzResearch.WordTrace tailWord_3343173 prefixEnd_3343173 572218220044584517987511 := by
  unfold tailWord_3343173
  simp only [CollatzResearch.WordTrace]
  refine ⟨121935536717262664336386173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81290357811508442890924115 121935536717262664336386173)
  ·
    refine ⟨45725826268973499126144815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121935536717262664336386173 45725826268973499126144815)
    ·
      refine ⟨68588739403460248689217223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45725826268973499126144815 68588739403460248689217223)
      ·
        refine ⟨102883109105190373033825835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68588739403460248689217223 102883109105190373033825835)
        ·
          refine ⟨154324663657785559550738753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102883109105190373033825835 154324663657785559550738753)
          ·
            refine ⟨115743497743339169663054065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 154324663657785559550738753 115743497743339169663054065)
            ·
              refine ⟨86807623307504377247290549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 115743497743339169663054065 86807623307504377247290549)
              ·
                refine ⟨8138214685078535366933489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 86807623307504377247290549 8138214685078535366933489)
                ·
                  refine ⟨6103661013808901525200117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8138214685078535366933489 6103661013808901525200117)
                  ·
                    refine ⟨572218220044584517987511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6103661013808901525200117 572218220044584517987511)
                    ·
                      rfl

theorem cell23_3343173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 5, 2, 5].length) (baseStart_3343173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3343173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3343173 prefixEnd_3343173 := by exact prefixLift 3343173
  have htrace : WordTrace (prefixWord ++ tailWord_3343173) baseStart_3343173 baseEnd_3343173 := by
    simpa [prefixWord, tailWord_3343173, baseEnd_3343173] using wordTrace_append hprefix tailTrace_3343173
  have hstable : (prefixWord ++ tailWord_3343173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3343173).length < 2 ^ (prefixWord ++ tailWord_3343173).sum := by decide
  have hdescent : baseEnd_3343173 < baseStart_3343173 := by decide
  rcases family_descends (prefixWord ++ tailWord_3343173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3343188 : List Nat := [2, 4, 1, 1, 5, 1, 1, 2, 2, 2, 2]
def baseStart_3343188 : Nat := 118140960795 + 3343188 * 2 ^ 59
def prefixEnd_3343188 : Nat := 4983230072969 + 3 ^ 40 * 3343188 * 2
def baseEnd_3343188 : Nat := 1716662362343570995274965

theorem tailTrace_3343188 : CollatzResearch.WordTrace tailWord_3343188 prefixEnd_3343188 1716662362343570995274965 := by
  unfold tailWord_3343188
  simp only [CollatzResearch.WordTrace]
  refine ⟨60968041906104160949091109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81290722541472214598788145 60968041906104160949091109)
  ·
    refine ⟨11431507857394530177954583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60968041906104160949091109 11431507857394530177954583)
    ·
      refine ⟨17147261786091795266931875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11431507857394530177954583 17147261786091795266931875)
      ·
        refine ⟨25720892679137692900397813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17147261786091795266931875 25720892679137692900397813)
        ·
          refine ⟨2411333688669158709412295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 25720892679137692900397813 2411333688669158709412295)
          ·
            refine ⟨3617000533003738064118443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2411333688669158709412295 3617000533003738064118443)
            ·
              refine ⟨5425500799505607096177665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3617000533003738064118443 5425500799505607096177665)
              ·
                refine ⟨4069125599629205322133249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5425500799505607096177665 4069125599629205322133249)
                ·
                  refine ⟨3051844199721903991599937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4069125599629205322133249 3051844199721903991599937)
                  ·
                    refine ⟨2288883149791427993699953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3051844199721903991599937 2288883149791427993699953)
                    ·
                      refine ⟨1716662362343570995274965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2288883149791427993699953 1716662362343570995274965)
                      ·
                        rfl

theorem cell23_3343188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 1, 1, 2, 2, 2, 2].length) (baseStart_3343188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3343188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3343188 prefixEnd_3343188 := by exact prefixLift 3343188
  have htrace : WordTrace (prefixWord ++ tailWord_3343188) baseStart_3343188 baseEnd_3343188 := by
    simpa [prefixWord, tailWord_3343188, baseEnd_3343188] using wordTrace_append hprefix tailTrace_3343188
  have hstable : (prefixWord ++ tailWord_3343188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3343188).length < 2 ^ (prefixWord ++ tailWord_3343188).sum := by decide
  have hdescent : baseEnd_3343188 < baseStart_3343188 := by decide
  rcases family_descends (prefixWord ++ tailWord_3343188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3343287 : List Nat := [1, 1, 3, 1, 3, 1, 3, 3, 2, 3, 2]
def baseStart_3343287 : Nat := 118140960795 + 3343287 * 2 ^ 59
def prefixEnd_3343287 : Nat := 4983230072969 + 3 ^ 40 * 3343287 * 2
def baseEnd_3343287 : Nat := 1716713196928366107937009

theorem tailTrace_3343287 : CollatzResearch.WordTrace tailWord_3343287 prefixEnd_3343287 1716713196928366107937009 := by
  unfold tailWord_3343287
  simp only [CollatzResearch.WordTrace]
  refine ⟨121939694638849661806036115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81293129759233107870690743 121939694638849661806036115)
  ·
    refine ⟨182909541958274492709054173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121939694638849661806036115 182909541958274492709054173)
    ·
      refine ⟨68591078234352934765895315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 182909541958274492709054173 68591078234352934765895315)
      ·
        refine ⟨102886617351529402148842973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68591078234352934765895315 102886617351529402148842973)
        ·
          refine ⟨38582481506823525805816115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102886617351529402148842973 38582481506823525805816115)
          ·
            refine ⟨57873722260235288708724173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38582481506823525805816115 57873722260235288708724173)
            ·
              refine ⟨21702645847588233265771565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57873722260235288708724173 21702645847588233265771565)
              ·
                refine ⟨8138492192845587474664337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21702645847588233265771565 8138492192845587474664337)
                ·
                  refine ⟨6103869144634190605998253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8138492192845587474664337 6103869144634190605998253)
                  ·
                    refine ⟨2288950929237821477249345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6103869144634190605998253 2288950929237821477249345)
                    ·
                      refine ⟨1716713196928366107937009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2288950929237821477249345 1716713196928366107937009)
                      ·
                        rfl

theorem cell23_3343287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 3, 2, 3, 2].length) (baseStart_3343287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3343287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3343287 prefixEnd_3343287 := by exact prefixLift 3343287
  have htrace : WordTrace (prefixWord ++ tailWord_3343287) baseStart_3343287 baseEnd_3343287 := by
    simpa [prefixWord, tailWord_3343287, baseEnd_3343287] using wordTrace_append hprefix tailTrace_3343287
  have hstable : (prefixWord ++ tailWord_3343287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3343287).length < 2 ^ (prefixWord ++ tailWord_3343287).sum := by decide
  have hdescent : baseEnd_3343287 < baseStart_3343287 := by decide
  rcases family_descends (prefixWord ++ tailWord_3343287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3343311 : List Nat := [1, 1, 2, 1, 1, 6, 4, 2, 1, 1, 3]
def baseStart_3343311 : Nat := 118140960795 + 3343311 * 2 ^ 59
def prefixEnd_3343311 : Nat := 4983230072969 + 3 ^ 40 * 3343311 * 2
def baseEnd_3343311 : Nat := 1716725520464074014036899

theorem tailTrace_3343311 : CollatzResearch.WordTrace tailWord_3343311 prefixEnd_3343311 1716725520464074014036899 := by
  unfold tailWord_3343311
  simp only [CollatzResearch.WordTrace]
  refine ⟨121940569990762713904909787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81293713327175142603273191 121940569990762713904909787)
  ·
    refine ⟨182910854986144070857364681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121940569990762713904909787 182910854986144070857364681)
    ·
      refine ⟨137183141239608053143023511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182910854986144070857364681 137183141239608053143023511)
      ·
        refine ⟨205774711859412079714535267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137183141239608053143023511 205774711859412079714535267)
        ·
          refine ⟨308662067789118119571802901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 205774711859412079714535267 308662067789118119571802901)
          ·
            refine ⟨14468534427614911854928261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 308662067789118119571802901 14468534427614911854928261)
            ·
              refine ⟨2712850205177795972799049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14468534427614911854928261 2712850205177795972799049)
              ·
                refine ⟨2034637653883346979599287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2712850205177795972799049 2034637653883346979599287)
                ·
                  refine ⟨3051956480825020469398931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2034637653883346979599287 3051956480825020469398931)
                  ·
                    refine ⟨4577934721237530704098397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3051956480825020469398931 4577934721237530704098397)
                    ·
                      refine ⟨1716725520464074014036899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4577934721237530704098397 1716725520464074014036899)
                      ·
                        rfl

theorem cell23_3343311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 4, 2, 1, 1, 3].length) (baseStart_3343311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3343311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3343311 prefixEnd_3343311 := by exact prefixLift 3343311
  have htrace : WordTrace (prefixWord ++ tailWord_3343311) baseStart_3343311 baseEnd_3343311 := by
    simpa [prefixWord, tailWord_3343311, baseEnd_3343311] using wordTrace_append hprefix tailTrace_3343311
  have hstable : (prefixWord ++ tailWord_3343311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3343311).length < 2 ^ (prefixWord ++ tailWord_3343311).sum := by decide
  have hdescent : baseEnd_3343311 < baseStart_3343311 := by decide
  rcases family_descends (prefixWord ++ tailWord_3343311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3343327 : List Nat := [1, 1, 2, 3, 5, 1, 2, 1, 1, 6]
def baseStart_3343327 : Nat := 118140960795 + 3343327 * 2 ^ 59
def prefixEnd_3343327 : Nat := 4983230072969 + 3 ^ 40 * 3343327 * 2
def baseEnd_3343327 : Nat := 572244578718181983812275

theorem tailTrace_3343327 : CollatzResearch.WordTrace tailWord_3343327 prefixEnd_3343327 572244578718181983812275 := by
  unfold tailWord_3343327
  simp only [CollatzResearch.WordTrace]
  refine ⟨121941153558704748637492235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81294102372469832424994823 121941153558704748637492235)
  ·
    refine ⟨182911730338057122956238353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121941153558704748637492235 182911730338057122956238353)
    ·
      refine ⟨137183797753542842217178765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182911730338057122956238353 137183797753542842217178765)
      ·
        refine ⟨51443924157578565831442037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 137183797753542842217178765 51443924157578565831442037)
        ·
          refine ⟨4822867889772990546697691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 51443924157578565831442037 4822867889772990546697691)
          ·
            refine ⟨7234301834659485820046537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4822867889772990546697691 7234301834659485820046537)
            ·
              refine ⟨5425726375994614365034903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7234301834659485820046537 5425726375994614365034903)
              ·
                refine ⟨8138589563991921547552355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5425726375994614365034903 8138589563991921547552355)
                ·
                  refine ⟨12207884345987882321328533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8138589563991921547552355 12207884345987882321328533)
                  ·
                    refine ⟨572244578718181983812275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12207884345987882321328533 572244578718181983812275)
                    ·
                      rfl

theorem cell23_3343327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 2, 1, 1, 6].length) (baseStart_3343327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3343327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3343327 prefixEnd_3343327 := by exact prefixLift 3343327
  have htrace : WordTrace (prefixWord ++ tailWord_3343327) baseStart_3343327 baseEnd_3343327 := by
    simpa [prefixWord, tailWord_3343327, baseEnd_3343327] using wordTrace_append hprefix tailTrace_3343327
  have hstable : (prefixWord ++ tailWord_3343327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3343327).length < 2 ^ (prefixWord ++ tailWord_3343327).sum := by decide
  have hdescent : baseEnd_3343327 < baseStart_3343327 := by decide
  rcases family_descends (prefixWord ++ tailWord_3343327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3343377 : List Nat := [1, 2, 2, 1, 1, 2, 1, 3, 5, 3, 2]
def baseStart_3343377 : Nat := 118140960795 + 3343377 * 2 ^ 59
def prefixEnd_3343377 : Nat := 4983230072969 + 3 ^ 40 * 3343377 * 2
def baseEnd_3343377 : Nat := 1716759410187270755811595

theorem tailTrace_3343377 : CollatzResearch.WordTrace tailWord_3343377 prefixEnd_3343377 1716759410187270755811595 := by
  unfold tailWord_3343377
  simp only [CollatzResearch.WordTrace]
  refine ⟨121942977208523607176812385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81295318139015738117874923 121942977208523607176812385)
  ·
    refine ⟨91457232906392705382609289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121942977208523607176812385 91457232906392705382609289)
    ·
      refine ⟨68592924679794529036956967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91457232906392705382609289 68592924679794529036956967)
      ·
        refine ⟨102889387019691793555435451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68592924679794529036956967 102889387019691793555435451)
        ·
          refine ⟨154334080529537690333153177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102889387019691793555435451 154334080529537690333153177)
          ·
            refine ⟨115750560397153267749864883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 154334080529537690333153177 115750560397153267749864883)
            ·
              refine ⟨173625840595729901624797325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115750560397153267749864883 173625840595729901624797325)
              ·
                refine ⟨65109690223398713109298997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 173625840595729901624797325 65109690223398713109298997)
                ·
                  refine ⟨6104033458443629353996781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 65109690223398713109298997 6104033458443629353996781)
                  ·
                    refine ⟨2289012546916361007748793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6104033458443629353996781 2289012546916361007748793)
                    ·
                      refine ⟨1716759410187270755811595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2289012546916361007748793 1716759410187270755811595)
                      ·
                        rfl

theorem cell23_3343377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 3, 2].length) (baseStart_3343377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3343377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3343377 prefixEnd_3343377 := by exact prefixLift 3343377
  have htrace : WordTrace (prefixWord ++ tailWord_3343377) baseStart_3343377 baseEnd_3343377 := by
    simpa [prefixWord, tailWord_3343377, baseEnd_3343377] using wordTrace_append hprefix tailTrace_3343377
  have hstable : (prefixWord ++ tailWord_3343377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3343377).length < 2 ^ (prefixWord ++ tailWord_3343377).sum := by decide
  have hdescent : baseEnd_3343377 < baseStart_3343377 := by decide
  rcases family_descends (prefixWord ++ tailWord_3343377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3343378 : List Nat := [3, 2, 5, 1, 1, 2, 1, 1, 1, 6]
def baseStart_3343378 : Nat := 118140960795 + 3343378 * 2 ^ 59
def prefixEnd_3343378 : Nat := 4983230072969 + 3 ^ 40 * 3343378 * 2
def baseEnd_3343378 : Nat := 572253307889308417299697

theorem tailTrace_3343378 : CollatzResearch.WordTrace tailWord_3343378 prefixEnd_3343378 572253307889308417299697 := by
  unfold tailWord_3343378
  simp only [CollatzResearch.WordTrace]
  refine ⟨30485753420379996086899697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81295342454346656231732525 30485753420379996086899697)
  ·
    refine ⟨22864315065284997065174773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30485753420379996086899697 22864315065284997065174773)
    ·
      refine ⟨2143529537370468474860135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 22864315065284997065174773 2143529537370468474860135)
      ·
        refine ⟨3215294306055702712290203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2143529537370468474860135 3215294306055702712290203)
        ·
          refine ⟨4822941459083554068435305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3215294306055702712290203 4822941459083554068435305)
          ·
            refine ⟨3617206094312665551326479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4822941459083554068435305 3617206094312665551326479)
            ·
              refine ⟨5425809141468998326989719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3617206094312665551326479 5425809141468998326989719)
              ·
                refine ⟨8138713712203497490484579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5425809141468998326989719 8138713712203497490484579)
                ·
                  refine ⟨12208070568305246235726869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8138713712203497490484579 12208070568305246235726869)
                  ·
                    refine ⟨572253307889308417299697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12208070568305246235726869 572253307889308417299697)
                    ·
                      rfl

theorem cell23_3343378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 2, 1, 1, 1, 6].length) (baseStart_3343378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3343378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3343378 prefixEnd_3343378 := by exact prefixLift 3343378
  have htrace : WordTrace (prefixWord ++ tailWord_3343378) baseStart_3343378 baseEnd_3343378 := by
    simpa [prefixWord, tailWord_3343378, baseEnd_3343378] using wordTrace_append hprefix tailTrace_3343378
  have hstable : (prefixWord ++ tailWord_3343378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3343378).length < 2 ^ (prefixWord ++ tailWord_3343378).sum := by decide
  have hdescent : baseEnd_3343378 < baseStart_3343378 := by decide
  rcases family_descends (prefixWord ++ tailWord_3343378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3343384 : List Nat := [2, 1, 2, 3, 2, 4, 1, 1, 1, 3, 3]
def baseStart_3343384 : Nat := 118140960795 + 3343384 * 2 ^ 59
def prefixEnd_3343384 : Nat := 4983230072969 + 3 ^ 40 * 3343384 * 2
def baseEnd_3343384 : Nat := 1716763004551852228424063

theorem tailTrace_3343384 : CollatzResearch.WordTrace tailWord_3343384 prefixEnd_3343384 1716763004551852228424063 := by
  unfold tailWord_3343384
  simp only [CollatzResearch.WordTrace]
  refine ⟨60971616259749123686158603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81295488346332164914878137 60971616259749123686158603)
  ·
    refine ⟨91457424389623685529237905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60971616259749123686158603 91457424389623685529237905)
    ·
      refine ⟨68593068292217764146928429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91457424389623685529237905 68593068292217764146928429)
      ·
        refine ⟨25722400609581661555098161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68593068292217764146928429 25722400609581661555098161)
        ·
          refine ⟨19291800457186246166323621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25722400609581661555098161 19291800457186246166323621)
          ·
            refine ⟨3617212585722421156185679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19291800457186246166323621 3617212585722421156185679)
            ·
              refine ⟨5425818878583631734278519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3617212585722421156185679 5425818878583631734278519)
              ·
                refine ⟨8138728317875447601417779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5425818878583631734278519 8138728317875447601417779)
                ·
                  refine ⟨12208092476813171402126669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8138728317875447601417779 12208092476813171402126669)
                  ·
                    refine ⟨4578034678804939275797501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12208092476813171402126669 4578034678804939275797501)
                    ·
                      refine ⟨1716763004551852228424063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4578034678804939275797501 1716763004551852228424063)
                      ·
                        rfl

theorem cell23_3343384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 4, 1, 1, 1, 3, 3].length) (baseStart_3343384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3343384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3343384 prefixEnd_3343384 := by exact prefixLift 3343384
  have htrace : WordTrace (prefixWord ++ tailWord_3343384) baseStart_3343384 baseEnd_3343384 := by
    simpa [prefixWord, tailWord_3343384, baseEnd_3343384] using wordTrace_append hprefix tailTrace_3343384
  have hstable : (prefixWord ++ tailWord_3343384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3343384).length < 2 ^ (prefixWord ++ tailWord_3343384).sum := by decide
  have hdescent : baseEnd_3343384 < baseStart_3343384 := by decide
  rcases family_descends (prefixWord ++ tailWord_3343384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3343402 : List Nat := [3, 1, 4, 1, 4, 1, 1, 3, 1, 2, 2]
def baseStart_3343402 : Nat := 118140960795 + 3343402 * 2 ^ 59
def prefixEnd_3343402 : Nat := 4983230072969 + 3 ^ 40 * 3343402 * 2
def baseEnd_3343402 : Nat := 1716772247203633157998981

theorem tailTrace_3343402 : CollatzResearch.WordTrace tailWord_3343402 prefixEnd_3343402 1716772247203633157998981 := by
  unfold tailWord_3343402
  simp only [CollatzResearch.WordTrace]
  refine ⟨30485972258358259111618115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81295926022288690964314973 30485972258358259111618115)
  ·
    refine ⟨45728958387537388667427173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30485972258358259111618115 45728958387537388667427173)
    ·
      refine ⟨8574179697663260375142595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45728958387537388667427173 8574179697663260375142595)
      ·
        refine ⟨12861269546494890562713893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8574179697663260375142595 12861269546494890562713893)
        ·
          refine ⟨2411488039967791980508855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12861269546494890562713893 2411488039967791980508855)
          ·
            refine ⟨3617232059951687970763283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2411488039967791980508855 3617232059951687970763283)
            ·
              refine ⟨5425848089927531956144925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3617232059951687970763283 5425848089927531956144925)
              ·
                refine ⟨2034693033722824483554347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5425848089927531956144925 2034693033722824483554347)
                ·
                  refine ⟨3052039550584236725331521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2034693033722824483554347 3052039550584236725331521)
                  ·
                    refine ⟨2289029662938177543998641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3052039550584236725331521 2289029662938177543998641)
                    ·
                      refine ⟨1716772247203633157998981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2289029662938177543998641 1716772247203633157998981)
                      ·
                        rfl

theorem cell23_3343402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 1, 1, 3, 1, 2, 2].length) (baseStart_3343402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3343402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3343402 prefixEnd_3343402 := by exact prefixLift 3343402
  have htrace : WordTrace (prefixWord ++ tailWord_3343402) baseStart_3343402 baseEnd_3343402 := by
    simpa [prefixWord, tailWord_3343402, baseEnd_3343402] using wordTrace_append hprefix tailTrace_3343402
  have hstable : (prefixWord ++ tailWord_3343402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3343402).length < 2 ^ (prefixWord ++ tailWord_3343402).sum := by decide
  have hdescent : baseEnd_3343402 < baseStart_3343402 := by decide
  rcases family_descends (prefixWord ++ tailWord_3343402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3343424 : List Nat := [2, 1, 1, 2, 2, 3, 1, 3, 4, 2, 2]
def baseStart_3343424 : Nat := 118140960795 + 3343424 * 2 ^ 59
def prefixEnd_3343424 : Nat := 4983230072969 + 3 ^ 40 * 3343424 * 2
def baseEnd_3343424 : Nat := 1716783543778032071923879

theorem tailTrace_3343424 : CollatzResearch.WordTrace tailWord_3343424 prefixEnd_3343424 1716783543778032071923879 := by
  unfold tailWord_3343424
  simp only [CollatzResearch.WordTrace]
  refine ⟨60972345719676667101886663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81296460959568889469182217 60972345719676667101886663)
  ·
    refine ⟨91458518579515000652829995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60972345719676667101886663 91458518579515000652829995)
    ·
      refine ⟨137187777869272500979244993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91458518579515000652829995 137187777869272500979244993)
      ·
        refine ⟨102890833401954375734433745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137187777869272500979244993 102890833401954375734433745)
        ·
          refine ⟨77168125051465781800825309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102890833401954375734433745 77168125051465781800825309)
          ·
            refine ⟨28938046894299668175309491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77168125051465781800825309 28938046894299668175309491)
            ·
              refine ⟨43407070341449502262964237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28938046894299668175309491 43407070341449502262964237)
              ·
                refine ⟨16277651378043563348611589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43407070341449502262964237 16277651378043563348611589)
                ·
                  refine ⟨3052059633383168127864673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16277651378043563348611589 3052059633383168127864673)
                  ·
                    refine ⟨2289044725037376095898505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3052059633383168127864673 2289044725037376095898505)
                    ·
                      refine ⟨1716783543778032071923879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2289044725037376095898505 1716783543778032071923879)
                      ·
                        rfl

theorem cell23_3343424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 3, 4, 2, 2].length) (baseStart_3343424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3343424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3343424 prefixEnd_3343424 := by exact prefixLift 3343424
  have htrace : WordTrace (prefixWord ++ tailWord_3343424) baseStart_3343424 baseEnd_3343424 := by
    simpa [prefixWord, tailWord_3343424, baseEnd_3343424] using wordTrace_append hprefix tailTrace_3343424
  have hstable : (prefixWord ++ tailWord_3343424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3343424).length < 2 ^ (prefixWord ++ tailWord_3343424).sum := by decide
  have hdescent : baseEnd_3343424 < baseStart_3343424 := by decide
  rcases family_descends (prefixWord ++ tailWord_3343424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3343467 : List Nat := [1, 1, 1, 1, 2, 2, 1, 1, 6, 5, 2]
def baseStart_3343467 : Nat := 118140960795 + 3343467 * 2 ^ 59
def prefixEnd_3343467 : Nat := 4983230072969 + 3 ^ 40 * 3343467 * 2
def baseEnd_3343467 : Nat := 1716805623446175403686181

theorem tailTrace_3343467 : CollatzResearch.WordTrace tailWord_3343467 prefixEnd_3343467 1716805623446175403686181 := by
  unfold tailWord_3343467
  simp only [CollatzResearch.WordTrace]
  refine ⟨121946259778197552547588655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81297506518798368365059103 121946259778197552547588655)
  ·
    refine ⟨182919389667296328821382983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121946259778197552547588655 182919389667296328821382983)
    ·
      refine ⟨274379084500944493232074475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182919389667296328821382983 274379084500944493232074475)
      ·
        refine ⟨411568626751416739848111713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 274379084500944493232074475 411568626751416739848111713)
        ·
          refine ⟨308676470063562554886083785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 411568626751416739848111713 308676470063562554886083785)
          ·
            refine ⟨231507352547671916164562839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 308676470063562554886083785 231507352547671916164562839)
            ·
              refine ⟨347261028821507874246844259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 231507352547671916164562839 347261028821507874246844259)
              ·
                refine ⟨520891543232261811370266389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 347261028821507874246844259 520891543232261811370266389)
                ·
                  refine ⟨24416791089012272407981237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 520891543232261811370266389 24416791089012272407981237)
                  ·
                    refine ⟨2289074164594900538248241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 24416791089012272407981237 2289074164594900538248241)
                    ·
                      refine ⟨1716805623446175403686181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2289074164594900538248241 1716805623446175403686181)
                      ·
                        rfl

theorem cell23_3343467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 6, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 6, 5, 2].length) (baseStart_3343467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3343467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3343467 prefixEnd_3343467 := by exact prefixLift 3343467
  have htrace : WordTrace (prefixWord ++ tailWord_3343467) baseStart_3343467 baseEnd_3343467 := by
    simpa [prefixWord, tailWord_3343467, baseEnd_3343467] using wordTrace_append hprefix tailTrace_3343467
  have hstable : (prefixWord ++ tailWord_3343467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3343467).length < 2 ^ (prefixWord ++ tailWord_3343467).sum := by decide
  have hdescent : baseEnd_3343467 < baseStart_3343467 := by decide
  rcases family_descends (prefixWord ++ tailWord_3343467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3343507 : List Nat := [1, 1, 1, 2, 1, 2, 5, 1, 5, 4]
def baseStart_3343507 : Nat := 118140960795 + 3343507 * 2 ^ 59
def prefixEnd_3343507 : Nat := 4983230072969 + 3 ^ 40 * 3343507 * 2
def baseEnd_3343507 : Nat := 572275387557451749061999

theorem tailTrace_3343507 : CollatzResearch.WordTrace tailWord_3343507 prefixEnd_3343507 572275387557451749061999 := by
  unfold tailWord_3343507
  simp only [CollatzResearch.WordTrace]
  refine ⟨121947718698052639379044775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81298479132035092919363183 121947718698052639379044775)
  ·
    refine ⟨182921578047078959068567163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121947718698052639379044775 182921578047078959068567163)
    ·
      refine ⟨274382367070618438602850745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182921578047078959068567163 274382367070618438602850745)
      ·
        refine ⟨205786775302963828952138059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 274382367070618438602850745 205786775302963828952138059)
        ·
          refine ⟨308680162954445743428207089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 205786775302963828952138059 308680162954445743428207089)
          ·
            refine ⟨231510122215834307571155317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 308680162954445743428207089 231510122215834307571155317)
            ·
              refine ⟨21704073957734466334795811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 231510122215834307571155317 21704073957734466334795811)
              ·
                refine ⟨32556110936601699502193717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21704073957734466334795811 32556110936601699502193717)
                ·
                  refine ⟨3052135400306409328330661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 32556110936601699502193717 3052135400306409328330661)
                  ·
                    refine ⟨572275387557451749061999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3052135400306409328330661 572275387557451749061999)
                    ·
                      rfl

theorem cell23_3343507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 1, 5, 4].length) (baseStart_3343507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3343507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3343507 prefixEnd_3343507 := by exact prefixLift 3343507
  have htrace : WordTrace (prefixWord ++ tailWord_3343507) baseStart_3343507 baseEnd_3343507 := by
    simpa [prefixWord, tailWord_3343507, baseEnd_3343507] using wordTrace_append hprefix tailTrace_3343507
  have hstable : (prefixWord ++ tailWord_3343507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3343507).length < 2 ^ (prefixWord ++ tailWord_3343507).sum := by decide
  have hdescent : baseEnd_3343507 < baseStart_3343507 := by decide
  rcases family_descends (prefixWord ++ tailWord_3343507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3343514 : List Nat := [3, 1, 1, 5, 1, 2, 1, 1, 1, 3, 4]
def baseStart_3343514 : Nat := 118140960795 + 3343514 * 2 ^ 59
def prefixEnd_3343514 : Nat := 4983230072969 + 3 ^ 40 * 3343514 * 2
def baseEnd_3343514 : Nat := 1716829757036936719798465

theorem tailTrace_3343514 : CollatzResearch.WordTrace tailWord_3343514 prefixEnd_3343514 1716829757036936719798465 := by
  unfold tailWord_3343514
  simp only [CollatzResearch.WordTrace]
  refine ⟨30486993502256819893637399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81298649339351519716366397 30486993502256819893637399)
  ·
    refine ⟨45730490253385229840456099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30486993502256819893637399 45730490253385229840456099)
    ·
      refine ⟨68595735380077844760684149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45730490253385229840456099 68595735380077844760684149)
      ·
        refine ⟨6430850191882297946314139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 68595735380077844760684149 6430850191882297946314139)
        ·
          refine ⟨9646275287823446919471209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6430850191882297946314139 9646275287823446919471209)
          ·
            refine ⟨7234706465867585189603407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9646275287823446919471209 7234706465867585189603407)
            ·
              refine ⟨10852059698801377784405111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7234706465867585189603407 10852059698801377784405111)
              ·
                refine ⟨16278089548202066676607667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10852059698801377784405111 16278089548202066676607667)
                ·
                  refine ⟨24417134322303100014911501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16278089548202066676607667 24417134322303100014911501)
                  ·
                    refine ⟨9156425370863662505591813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24417134322303100014911501 9156425370863662505591813)
                    ·
                      refine ⟨1716829757036936719798465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9156425370863662505591813 1716829757036936719798465)
                      ·
                        rfl

theorem cell23_3343514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 1, 1, 1, 3, 4].length) (baseStart_3343514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3343514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3343514 prefixEnd_3343514 := by exact prefixLift 3343514
  have htrace : WordTrace (prefixWord ++ tailWord_3343514) baseStart_3343514 baseEnd_3343514 := by
    simpa [prefixWord, tailWord_3343514, baseEnd_3343514] using wordTrace_append hprefix tailTrace_3343514
  have hstable : (prefixWord ++ tailWord_3343514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3343514).length < 2 ^ (prefixWord ++ tailWord_3343514).sum := by decide
  have hdescent : baseEnd_3343514 < baseStart_3343514 := by decide
  rcases family_descends (prefixWord ++ tailWord_3343514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3343584 : List Nat := [2, 1, 1, 3, 1, 4, 2, 3, 1, 5]
def baseStart_3343584 : Nat := 118140960795 + 3343584 * 2 ^ 59
def prefixEnd_3343584 : Nat := 4983230072969 + 3 ^ 40 * 3343584 * 2
def baseEnd_3343584 : Nat := 572288566894250481974381

theorem tailTrace_3343584 : CollatzResearch.WordTrace tailWord_3343584 prefixEnd_3343584 572288566894250481974381 := by
  unfold tailWord_3343584
  simp only [CollatzResearch.WordTrace]
  refine ⟨60975263559386840764798903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81300351412515787686398537 60975263559386840764798903)
  ·
    refine ⟨91462895339080261147198355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60975263559386840764798903 91462895339080261147198355)
    ·
      refine ⟨137194343008620391720797533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91462895339080261147198355 137194343008620391720797533)
      ·
        refine ⟨51447878628232646895299075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 137194343008620391720797533 51447878628232646895299075)
        ·
          refine ⟨77171817942348970342948613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51447878628232646895299075 77171817942348970342948613)
          ·
            refine ⟨14469715864190431939302865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 77171817942348970342948613 14469715864190431939302865)
            ·
              refine ⟨10852286898142823954477149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14469715864190431939302865 10852286898142823954477149)
              ·
                refine ⟨4069607586803558982928931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10852286898142823954477149 4069607586803558982928931)
                ·
                  refine ⟨6104411380205338474393397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4069607586803558982928931 6104411380205338474393397)
                  ·
                    refine ⟨572288566894250481974381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6104411380205338474393397 572288566894250481974381)
                    ·
                      rfl

theorem cell23_3343584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 2, 3, 1, 5].length) (baseStart_3343584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3343584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3343584 prefixEnd_3343584 := by exact prefixLift 3343584
  have htrace : WordTrace (prefixWord ++ tailWord_3343584) baseStart_3343584 baseEnd_3343584 := by
    simpa [prefixWord, tailWord_3343584, baseEnd_3343584] using wordTrace_append hprefix tailTrace_3343584
  have hstable : (prefixWord ++ tailWord_3343584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3343584).length < 2 ^ (prefixWord ++ tailWord_3343584).sum := by decide
  have hdescent : baseEnd_3343584 < baseStart_3343584 := by decide
  rcases family_descends (prefixWord ++ tailWord_3343584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3343598 : List Nat := [4, 1, 2, 1, 1, 1, 2, 6, 1, 1, 3]
def baseStart_3343598 : Nat := 118140960795 + 3343598 * 2 ^ 59
def prefixEnd_3343598 : Nat := 4983230072969 + 3 ^ 40 * 3343598 * 2
def baseEnd_3343598 : Nat := 1716872889411914391148079

theorem tailTrace_3343598 : CollatzResearch.WordTrace tailWord_3343598 prefixEnd_3343598 1716872889411914391148079 := by
  unfold tailWord_3343598
  simp only [CollatzResearch.WordTrace]
  refine ⟨15243879717590370240075931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81300691827148641280404965 15243879717590370240075931)
  ·
    refine ⟨22865819576385555360113897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15243879717590370240075931 22865819576385555360113897)
    ·
      refine ⟨17149364682289166520085423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22865819576385555360113897 17149364682289166520085423)
      ·
        refine ⟨25724047023433749780128135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17149364682289166520085423 25724047023433749780128135)
        ·
          refine ⟨38586070535150624670192203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25724047023433749780128135 38586070535150624670192203)
          ·
            refine ⟨57879105802725937005288305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38586070535150624670192203 57879105802725937005288305)
            ·
              refine ⟨43409329352044452753966229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57879105802725937005288305 43409329352044452753966229)
              ·
                refine ⟨2034812313377083722842167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 43409329352044452753966229 2034812313377083722842167)
                ·
                  refine ⟨3052218470065625584263251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2034812313377083722842167 3052218470065625584263251)
                  ·
                    refine ⟨4578327705098438376394877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3052218470065625584263251 4578327705098438376394877)
                    ·
                      refine ⟨1716872889411914391148079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4578327705098438376394877 1716872889411914391148079)
                      ·
                        rfl

theorem cell23_3343598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 6, 1, 1, 3].length) (baseStart_3343598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3343598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3343598 prefixEnd_3343598 := by exact prefixLift 3343598
  have htrace : WordTrace (prefixWord ++ tailWord_3343598) baseStart_3343598 baseEnd_3343598 := by
    simpa [prefixWord, tailWord_3343598, baseEnd_3343598] using wordTrace_append hprefix tailTrace_3343598
  have hstable : (prefixWord ++ tailWord_3343598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3343598).length < 2 ^ (prefixWord ++ tailWord_3343598).sum := by decide
  have hdescent : baseEnd_3343598 < baseStart_3343598 := by decide
  rcases family_descends (prefixWord ++ tailWord_3343598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3343621 : List Nat := [1, 3, 1, 1, 2, 1, 4, 1, 5, 2, 2]
def baseStart_3343621 : Nat := 118140960795 + 3343621 * 2 ^ 59
def prefixEnd_3343621 : Nat := 4983230072969 + 3 ^ 40 * 3343621 * 2
def baseEnd_3343621 : Nat := 1716884699466967801160473

theorem tailTrace_3343621 : CollatzResearch.WordTrace tailWord_3343621 prefixEnd_3343621 1716884699466967801160473 := by
  unfold tailWord_3343621
  simp only [CollatzResearch.WordTrace]
  refine ⟨121951876619639636848694717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81301251079759757899129811 121951876619639636848694717)
  ·
    refine ⟨45731953732364863818260519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121951876619639636848694717 45731953732364863818260519)
    ·
      refine ⟨68597930598547295727390779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45731953732364863818260519 68597930598547295727390779)
      ·
        refine ⟨102896895897820943591086169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68597930598547295727390779 102896895897820943591086169)
        ·
          refine ⟨77172671923365707693314627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102896895897820943591086169 77172671923365707693314627)
          ·
            refine ⟨115759007885048561539971941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77172671923365707693314627 115759007885048561539971941)
            ·
              refine ⟨21704813978446605288744739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 115759007885048561539971941 21704813978446605288744739)
              ·
                refine ⟨32557220967669907933117109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21704813978446605288744739 32557220967669907933117109)
                ·
                  refine ⟨3052239465719053868729729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 32557220967669907933117109 3052239465719053868729729)
                  ·
                    refine ⟨2289179599289290401547297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3052239465719053868729729 2289179599289290401547297)
                    ·
                      refine ⟨1716884699466967801160473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2289179599289290401547297 1716884699466967801160473)
                      ·
                        rfl

theorem cell23_3343621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 1, 5, 2, 2].length) (baseStart_3343621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3343621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3343621 prefixEnd_3343621 := by exact prefixLift 3343621
  have htrace : WordTrace (prefixWord ++ tailWord_3343621) baseStart_3343621 baseEnd_3343621 := by
    simpa [prefixWord, tailWord_3343621, baseEnd_3343621] using wordTrace_append hprefix tailTrace_3343621
  have hstable : (prefixWord ++ tailWord_3343621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3343621).length < 2 ^ (prefixWord ++ tailWord_3343621).sum := by decide
  have hdescent : baseEnd_3343621 < baseStart_3343621 := by decide
  rcases family_descends (prefixWord ++ tailWord_3343621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3343627 : List Nat := [1, 1, 1, 1, 5, 3, 2, 9]
def baseStart_3343627 : Nat := 118140960795 + 3343627 * 2 ^ 59
def prefixEnd_3343627 : Nat := 4983230072969 + 3 ^ 40 * 3343627 * 2
def baseEnd_3343627 : Nat := 63588436309292399173535

theorem tailTrace_3343627 : CollatzResearch.WordTrace tailWord_3343627 prefixEnd_3343627 63588436309292399173535 := by
  unfold tailWord_3343627
  simp only [CollatzResearch.WordTrace]
  refine ⟨121952095457617899873413135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81301396971745266582275423 121952095457617899873413135)
  ·
    refine ⟨182928143186426849810119703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121952095457617899873413135 182928143186426849810119703)
    ·
      refine ⟨274392214779640274715179555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182928143186426849810119703 274392214779640274715179555)
      ·
        refine ⟨411588322169460412072769333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 274392214779640274715179555 411588322169460412072769333)
        ·
          refine ⟨38586405203386913631822125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 411588322169460412072769333 38586405203386913631822125)
          ·
            refine ⟨14469901951270092611933297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38586405203386913631822125 14469901951270092611933297)
            ·
              refine ⟨10852426463452569458949973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14469901951270092611933297 10852426463452569458949973)
              ·
                refine ⟨63588436309292399173535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 10852426463452569458949973 63588436309292399173535)
                ·
                  rfl

theorem cell23_3343627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 2, 9].length) (baseStart_3343627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3343627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3343627 prefixEnd_3343627 := by exact prefixLift 3343627
  have htrace : WordTrace (prefixWord ++ tailWord_3343627) baseStart_3343627 baseEnd_3343627 := by
    simpa [prefixWord, tailWord_3343627, baseEnd_3343627] using wordTrace_append hprefix tailTrace_3343627
  have hstable : (prefixWord ++ tailWord_3343627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3343627).length < 2 ^ (prefixWord ++ tailWord_3343627).sum := by decide
  have hdescent : baseEnd_3343627 < baseStart_3343627 := by decide
  rcases family_descends (prefixWord ++ tailWord_3343627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3343648 : List Nat := [2, 1, 1, 5, 3, 1, 2, 2, 2, 4]
def baseStart_3343648 : Nat := 118140960795 + 3343648 * 2 ^ 59
def prefixEnd_3343648 : Nat := 4983230072969 + 3 ^ 40 * 3343648 * 2
def baseEnd_3343648 : Nat := 572299521148213065174283

theorem tailTrace_3343648 : CollatzResearch.WordTrace tailWord_3343648 prefixEnd_3343648 572299521148213065174283 := by
  unfold tailWord_3343648
  simp only [CollatzResearch.WordTrace]
  refine ⟨60976430695270910229963799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81301907593694546973285065 60976430695270910229963799)
  ·
    refine ⟨91464646042906365344945699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60976430695270910229963799 91464646042906365344945699)
    ·
      refine ⟨137196969064359548017418549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91464646042906365344945699 137196969064359548017418549)
      ·
        refine ⟨12862215849783707626632989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 137196969064359548017418549 12862215849783707626632989)
        ·
          refine ⟨4823330943668890359987371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12862215849783707626632989 4823330943668890359987371)
          ·
            refine ⟨7234996415503335539981057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4823330943668890359987371 7234996415503335539981057)
            ·
              refine ⟨5426247311627501654985793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7234996415503335539981057 5426247311627501654985793)
              ·
                refine ⟨4069685483720626241239345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5426247311627501654985793 4069685483720626241239345)
                ·
                  refine ⟨3052264112790469680929509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4069685483720626241239345 3052264112790469680929509)
                  ·
                    refine ⟨572299521148213065174283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3052264112790469680929509 572299521148213065174283)
                    ·
                      rfl

theorem cell23_3343648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 2, 2, 2, 4].length) (baseStart_3343648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3343648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3343648 prefixEnd_3343648 := by exact prefixLift 3343648
  have htrace : WordTrace (prefixWord ++ tailWord_3343648) baseStart_3343648 baseEnd_3343648 := by
    simpa [prefixWord, tailWord_3343648, baseEnd_3343648] using wordTrace_append hprefix tailTrace_3343648
  have hstable : (prefixWord ++ tailWord_3343648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3343648).length < 2 ^ (prefixWord ++ tailWord_3343648).sum := by decide
  have hdescent : baseEnd_3343648 < baseStart_3343648 := by decide
  rcases family_descends (prefixWord ++ tailWord_3343648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3343661 : List Nat := [1, 5, 3, 1, 1, 1, 3, 8]
def baseStart_3343661 : Nat := 118140960795 + 3343661 * 2 ^ 59
def prefixEnd_3343661 : Nat := 4983230072969 + 3 ^ 40 * 3343661 * 2
def baseEnd_3343661 : Nat := 63589082914561023876307

theorem tailTrace_3343661 : CollatzResearch.WordTrace tailWord_3343661 prefixEnd_3343661 63589082914561023876307 := by
  unfold tailWord_3343661
  simp only [CollatzResearch.WordTrace]
  refine ⟨121953335539494723680150837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81302223692996482453433891 121953335539494723680150837)
  ·
    refine ⟨11433125206827630345014141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 121953335539494723680150837 11433125206827630345014141)
    ·
      refine ⟨4287421952560361379380303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11433125206827630345014141 4287421952560361379380303)
      ·
        refine ⟨6431132928840542069070455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4287421952560361379380303 6431132928840542069070455)
        ·
          refine ⟨9646699393260813103605683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6431132928840542069070455 9646699393260813103605683)
          ·
            refine ⟨14470049089891219655408525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9646699393260813103605683 14470049089891219655408525)
            ·
              refine ⟨5426268408709207370778197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14470049089891219655408525 5426268408709207370778197)
              ·
                refine ⟨63589082914561023876307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5426268408709207370778197 63589082914561023876307)
                ·
                  rfl

theorem cell23_3343661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 3, 8].length) (baseStart_3343661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3343661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3343661 prefixEnd_3343661 := by exact prefixLift 3343661
  have htrace : WordTrace (prefixWord ++ tailWord_3343661) baseStart_3343661 baseEnd_3343661 := by
    simpa [prefixWord, tailWord_3343661, baseEnd_3343661] using wordTrace_append hprefix tailTrace_3343661
  have hstable : (prefixWord ++ tailWord_3343661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3343661).length < 2 ^ (prefixWord ++ tailWord_3343661).sum := by decide
  have hdescent : baseEnd_3343661 < baseStart_3343661 := by decide
  rcases family_descends (prefixWord ++ tailWord_3343661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3343722 : List Nat := [3, 1, 3, 3, 2, 1, 3, 1, 2, 1, 3]
def baseStart_3343722 : Nat := 118140960795 + 3343722 * 2 ^ 59
def prefixEnd_3343722 : Nat := 4983230072969 + 3 ^ 40 * 3343722 * 2
def baseEnd_3343722 : Nat := 1716936561013071905997509

theorem tailTrace_3343722 : CollatzResearch.WordTrace tailWord_3343722 prefixEnd_3343722 1716936561013071905997509 := by
  unfold tailWord_3343722
  simp only [CollatzResearch.WordTrace]
  refine ⟨30488890098068432774530355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81303706928182487398747613 30488890098068432774530355)
  ·
    refine ⟨45733335147102649161795533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30488890098068432774530355 45733335147102649161795533)
    ·
      refine ⟨17150000680163493435673325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45733335147102649161795533 17150000680163493435673325)
      ·
        refine ⟨6431250255061310038377497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17150000680163493435673325 6431250255061310038377497)
        ·
          refine ⟨4823437691295982528783123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6431250255061310038377497 4823437691295982528783123)
          ·
            refine ⟨7235156536943973793174685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4823437691295982528783123 7235156536943973793174685)
            ·
              refine ⟨2713183701353990172440507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7235156536943973793174685 2713183701353990172440507)
              ·
                refine ⟨4069775552030985258660761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2713183701353990172440507 4069775552030985258660761)
                ·
                  refine ⟨3052331664023238943995571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4069775552030985258660761 3052331664023238943995571)
                  ·
                    refine ⟨4578497496034858415993357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3052331664023238943995571 4578497496034858415993357)
                    ·
                      refine ⟨1716936561013071905997509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4578497496034858415993357 1716936561013071905997509)
                      ·
                        rfl

theorem cell23_3343722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 3, 1, 2, 1, 3].length) (baseStart_3343722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3343722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3343722 prefixEnd_3343722 := by exact prefixLift 3343722
  have htrace : WordTrace (prefixWord ++ tailWord_3343722) baseStart_3343722 baseEnd_3343722 := by
    simpa [prefixWord, tailWord_3343722, baseEnd_3343722] using wordTrace_append hprefix tailTrace_3343722
  have hstable : (prefixWord ++ tailWord_3343722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3343722).length < 2 ^ (prefixWord ++ tailWord_3343722).sum := by decide
  have hdescent : baseEnd_3343722 < baseStart_3343722 := by decide
  rcases family_descends (prefixWord ++ tailWord_3343722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3343744 : List Nat := [2, 1, 1, 2, 1, 2, 1, 4, 1, 5, 3]
def baseStart_3343744 : Nat := 118140960795 + 3343744 * 2 ^ 59
def prefixEnd_3343744 : Nat := 4983230072969 + 3 ^ 40 * 3343744 * 2
def baseEnd_3343744 : Nat := 1716947857587470819922407

theorem tailTrace_3343744 : CollatzResearch.WordTrace tailWord_3343744 prefixEnd_3343744 1716947857587470819922407 := by
  unfold tailWord_3343744
  simp only [CollatzResearch.WordTrace]
  refine ⟨60978181399097014427711143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81304241865462685903614857 60978181399097014427711143)
  ·
    refine ⟨91467272098645521641566715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60978181399097014427711143 91467272098645521641566715)
    ·
      refine ⟨137200908147968282462350073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91467272098645521641566715 137200908147968282462350073)
      ·
        refine ⟨102900681110976211846762555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137200908147968282462350073 102900681110976211846762555)
        ·
          refine ⟨154351021666464317770143833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102900681110976211846762555 154351021666464317770143833)
          ·
            refine ⟨115763266249848238327607875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 154351021666464317770143833 115763266249848238327607875)
            ·
              refine ⟨173644899374772357491411813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115763266249848238327607875 173644899374772357491411813)
              ·
                refine ⟨32558418632769817029639715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 173644899374772357491411813 32558418632769817029639715)
                ·
                  refine ⟨48837627949154725544459573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32558418632769817029639715 48837627949154725544459573)
                  ·
                    refine ⟨4578527620233255519793085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 48837627949154725544459573 4578527620233255519793085)
                    ·
                      refine ⟨1716947857587470819922407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4578527620233255519793085 1716947857587470819922407)
                      ·
                        rfl

theorem cell23_3343744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 4, 1, 5, 3].length) (baseStart_3343744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3343744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3343744 prefixEnd_3343744 := by exact prefixLift 3343744
  have htrace : WordTrace (prefixWord ++ tailWord_3343744) baseStart_3343744 baseEnd_3343744 := by
    simpa [prefixWord, tailWord_3343744, baseEnd_3343744] using wordTrace_append hprefix tailTrace_3343744
  have hstable : (prefixWord ++ tailWord_3343744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3343744).length < 2 ^ (prefixWord ++ tailWord_3343744).sum := by decide
  have hdescent : baseEnd_3343744 < baseStart_3343744 := by decide
  rcases family_descends (prefixWord ++ tailWord_3343744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3343768 : List Nat := [2, 1, 2, 5, 2, 2, 1, 1, 7]
def baseStart_3343768 : Nat := 118140960795 + 3343768 * 2 ^ 59
def prefixEnd_3343768 : Nat := 4983230072969 + 3 ^ 40 * 3343768 * 2
def baseEnd_3343768 : Nat := 190773353458130969558033

theorem tailTrace_3343768 : CollatzResearch.WordTrace tailWord_3343768 prefixEnd_3343768 190773353458130969558033 := by
  unfold tailWord_3343768
  simp only [CollatzResearch.WordTrace]
  refine ⟨60978619075053540477147979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81304825433404720636197305 60978619075053540477147979)
  ·
    refine ⟨91467928612580310715721969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60978619075053540477147979 91467928612580310715721969)
    ·
      refine ⟨68600946459435233036791477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91467928612580310715721969 68600946459435233036791477)
      ·
        refine ⟨6431338730572053097199201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 68600946459435233036791477 6431338730572053097199201)
        ·
          refine ⟨4823504047929039822899401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6431338730572053097199201 4823504047929039822899401)
          ·
            refine ⟨3617628035946779867174551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4823504047929039822899401 3617628035946779867174551)
            ·
              refine ⟨5426442053920169800761827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3617628035946779867174551 5426442053920169800761827)
              ·
                refine ⟨8139663080880254701142741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5426442053920169800761827 8139663080880254701142741)
                ·
                  refine ⟨190773353458130969558033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8139663080880254701142741 190773353458130969558033)
                  ·
                    rfl

theorem cell23_3343768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 2, 1, 1, 7].length) (baseStart_3343768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3343768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3343768 prefixEnd_3343768 := by exact prefixLift 3343768
  have htrace : WordTrace (prefixWord ++ tailWord_3343768) baseStart_3343768 baseEnd_3343768 := by
    simpa [prefixWord, tailWord_3343768, baseEnd_3343768] using wordTrace_append hprefix tailTrace_3343768
  have hstable : (prefixWord ++ tailWord_3343768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3343768).length < 2 ^ (prefixWord ++ tailWord_3343768).sum := by decide
  have hdescent : baseEnd_3343768 < baseStart_3343768 := by decide
  rcases family_descends (prefixWord ++ tailWord_3343768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3343841 : List Nat := [1, 2, 3, 1, 2, 3, 2, 3, 6]
def baseStart_3343841 : Nat := 118140960795 + 3343841 * 2 ^ 59
def prefixEnd_3343841 : Nat := 4983230072969 + 3 ^ 40 * 3343841 * 2
def baseEnd_3343841 : Nat := 190777518356772993378829

theorem tailTrace_3343841 : CollatzResearch.WordTrace tailWord_3343841 prefixEnd_3343841 190777518356772993378829 := by
  unfold tailWord_3343841
  simp only [CollatzResearch.WordTrace]
  refine ⟨121959900678842614421703377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81306600452561742947802251 121959900678842614421703377)
  ·
    refine ⟨91469925509131960816277533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121959900678842614421703377 91469925509131960816277533)
    ·
      refine ⟨34301222065924485306104075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91469925509131960816277533 34301222065924485306104075)
      ·
        refine ⟨51451833098886727959156113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34301222065924485306104075 51451833098886727959156113)
        ·
          refine ⟨38588874824165045969367085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51451833098886727959156113 38588874824165045969367085)
          ·
            refine ⟨14470828059061892238512657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38588874824165045969367085 14470828059061892238512657)
            ·
              refine ⟨10853121044296419178884493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14470828059061892238512657 10853121044296419178884493)
              ·
                refine ⟨4069920391611157192081685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10853121044296419178884493 4069920391611157192081685)
                ·
                  refine ⟨190777518356772993378829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4069920391611157192081685 190777518356772993378829)
                  ·
                    rfl

theorem cell23_3343841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 2, 3, 6].length) (baseStart_3343841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3343841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3343841 prefixEnd_3343841 := by exact prefixLift 3343841
  have htrace : WordTrace (prefixWord ++ tailWord_3343841) baseStart_3343841 baseEnd_3343841 := by
    simpa [prefixWord, tailWord_3343841, baseEnd_3343841] using wordTrace_append hprefix tailTrace_3343841
  have hstable : (prefixWord ++ tailWord_3343841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3343841).length < 2 ^ (prefixWord ++ tailWord_3343841).sum := by decide
  have hdescent : baseEnd_3343841 < baseStart_3343841 := by decide
  rcases family_descends (prefixWord ++ tailWord_3343841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3343862 : List Nat := [5, 1, 1, 1, 2, 3, 2, 3, 1, 4]
def baseStart_3343862 : Nat := 118140960795 + 3343862 * 2 ^ 59
def prefixEnd_3343862 : Nat := 4983230072969 + 3 ^ 40 * 3343862 * 2
def baseEnd_3343862 : Nat := 572336149434900452748955

theorem tailTrace_3343862 : CollatzResearch.WordTrace tailWord_3343862 prefixEnd_3343862 572336149434900452748955 := by
  unfold tailWord_3343862
  simp only [CollatzResearch.WordTrace]
  refine ⟨7622541663235408438013615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 81307111074511023338811893 7622541663235408438013615)
  ·
    refine ⟨11433812494853112657020423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7622541663235408438013615 11433812494853112657020423)
    ·
      refine ⟨17150718742279668985530635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11433812494853112657020423 17150718742279668985530635)
      ·
        refine ⟨25726078113419503478295953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17150718742279668985530635 25726078113419503478295953)
        ·
          refine ⟨19294558585064627608721965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25726078113419503478295953 19294558585064627608721965)
          ·
            refine ⟨7235459469399235353270737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19294558585064627608721965 7235459469399235353270737)
            ·
              refine ⟨5426594602049426514953053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7235459469399235353270737 5426594602049426514953053)
              ·
                refine ⟨2034972975768534943107395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5426594602049426514953053 2034972975768534943107395)
                ·
                  refine ⟨3052459463652802414661093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2034972975768534943107395 3052459463652802414661093)
                  ·
                    refine ⟨572336149434900452748955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3052459463652802414661093 572336149434900452748955)
                    ·
                      rfl

theorem cell23_3343862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 2, 3, 1, 4].length) (baseStart_3343862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3343862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3343862 prefixEnd_3343862 := by exact prefixLift 3343862
  have htrace : WordTrace (prefixWord ++ tailWord_3343862) baseStart_3343862 baseEnd_3343862 := by
    simpa [prefixWord, tailWord_3343862, baseEnd_3343862] using wordTrace_append hprefix tailTrace_3343862
  have hstable : (prefixWord ++ tailWord_3343862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3343862).length < 2 ^ (prefixWord ++ tailWord_3343862).sum := by decide
  have hdescent : baseEnd_3343862 < baseStart_3343862 := by decide
  rcases family_descends (prefixWord ++ tailWord_3343862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3343892 : List Nat := [2, 4, 3, 1, 2, 1, 3, 1, 6]
def baseStart_3343892 : Nat := 118140960795 + 3343892 * 2 ^ 59
def prefixEnd_3343892 : Nat := 4983230072969 + 3 ^ 40 * 3343892 * 2
def baseEnd_3343892 : Nat := 190780428080481804541303

theorem tailTrace_3343892 : CollatzResearch.WordTrace tailWord_3343892 prefixEnd_3343892 190780428080481804541303 := by
  unfold tailWord_3343892
  simp only [CollatzResearch.WordTrace]
  refine ⟨60980880400828925065904965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81307840534438566754539953 60980880400828925065904965)
  ·
    refine ⟨11433915075155423449857181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60980880400828925065904965 11433915075155423449857181)
    ·
      refine ⟨4287718153183283793696443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11433915075155423449857181 4287718153183283793696443)
      ·
        refine ⟨6431577229774925690544665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4287718153183283793696443 6431577229774925690544665)
        ·
          refine ⟨4823682922331194267908499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6431577229774925690544665 4823682922331194267908499)
          ·
            refine ⟨7235524383496791401862749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4823682922331194267908499 7235524383496791401862749)
            ·
              refine ⟨2713321643811296775698531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7235524383496791401862749 2713321643811296775698531)
              ·
                refine ⟨4069982465716945163547797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2713321643811296775698531 4069982465716945163547797)
                ·
                  refine ⟨190780428080481804541303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4069982465716945163547797 190780428080481804541303)
                  ·
                    rfl

theorem cell23_3343892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 3, 1, 6].length) (baseStart_3343892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3343892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3343892 prefixEnd_3343892 := by exact prefixLift 3343892
  have htrace : WordTrace (prefixWord ++ tailWord_3343892) baseStart_3343892 baseEnd_3343892 := by
    simpa [prefixWord, tailWord_3343892, baseEnd_3343892] using wordTrace_append hprefix tailTrace_3343892
  have hstable : (prefixWord ++ tailWord_3343892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3343892).length < 2 ^ (prefixWord ++ tailWord_3343892).sum := by decide
  have hdescent : baseEnd_3343892 < baseStart_3343892 := by decide
  rcases family_descends (prefixWord ++ tailWord_3343892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3343921 : List Nat := [1, 2, 2, 3, 1, 1, 1, 3, 3, 2, 4]
def baseStart_3343921 : Nat := 118140960795 + 3343921 * 2 ^ 59
def prefixEnd_3343921 : Nat := 4983230072969 + 3 ^ 40 * 3343921 * 2
def baseEnd_3343921 : Nat := 1717038743663316627409093

theorem tailTrace_3343921 : CollatzResearch.WordTrace tailWord_3343921 prefixEnd_3343921 1717038743663316627409093 := by
  unfold tailWord_3343921
  simp only [CollatzResearch.WordTrace]
  refine ⟨121962818518552788084615617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81308545679035192056410411 121962818518552788084615617)
  ·
    refine ⟨91472113888914591063461713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121962818518552788084615617 91472113888914591063461713)
    ·
      refine ⟨68604085416685943297596285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91472113888914591063461713 68604085416685943297596285)
      ·
        refine ⟨25726532031257228736598607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68604085416685943297596285 25726532031257228736598607)
        ·
          refine ⟨38589798046885843104897911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25726532031257228736598607 38589798046885843104897911)
          ·
            refine ⟨57884697070328764657346867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38589798046885843104897911 57884697070328764657346867)
            ·
              refine ⟨86827045605493146986020301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57884697070328764657346867 86827045605493146986020301)
              ·
                refine ⟨32560142102059930119757613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 86827045605493146986020301 32560142102059930119757613)
                ·
                  refine ⟨12210053288272473794909105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32560142102059930119757613 12210053288272473794909105)
                  ·
                    refine ⟨9157539966204355346181829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12210053288272473794909105 9157539966204355346181829)
                    ·
                      refine ⟨1717038743663316627409093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9157539966204355346181829 1717038743663316627409093)
                      ·
                        rfl

theorem cell23_3343921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 3, 3, 2, 4].length) (baseStart_3343921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3343921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3343921 prefixEnd_3343921 := by exact prefixLift 3343921
  have htrace : WordTrace (prefixWord ++ tailWord_3343921) baseStart_3343921 baseEnd_3343921 := by
    simpa [prefixWord, tailWord_3343921, baseEnd_3343921] using wordTrace_append hprefix tailTrace_3343921
  have hstable : (prefixWord ++ tailWord_3343921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3343921).length < 2 ^ (prefixWord ++ tailWord_3343921).sum := by decide
  have hdescent : baseEnd_3343921 < baseStart_3343921 := by decide
  rcases family_descends (prefixWord ++ tailWord_3343921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3343928 : List Nat := [2, 1, 2, 1, 4, 3, 2, 1, 1, 1, 5]
def baseStart_3343928 : Nat := 118140960795 + 3343928 * 2 ^ 59
def prefixEnd_3343928 : Nat := 4983230072969 + 3 ^ 40 * 3343928 * 2
def baseEnd_3343928 : Nat := 1717042338027898100021561

theorem tailTrace_3343928 : CollatzResearch.WordTrace tailWord_3343928 prefixEnd_3343928 1717042338027898100021561 := by
  unfold tailWord_3343928
  simp only [CollatzResearch.WordTrace]
  refine ⟨60981536914763714140060219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81308715886351618853413625 60981536914763714140060219)
  ·
    refine ⟨91472305372145571210090329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60981536914763714140060219 91472305372145571210090329)
    ·
      refine ⟨68604229029109178407567747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91472305372145571210090329 68604229029109178407567747)
      ·
        refine ⟨102906343543663767611351621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68604229029109178407567747 102906343543663767611351621)
        ·
          refine ⟨19294939414436956427128429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 102906343543663767611351621 19294939414436956427128429)
          ·
            refine ⟨7235602280413858660173161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19294939414436956427128429 7235602280413858660173161)
            ·
              refine ⟨5426701710310393995129871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7235602280413858660173161 5426701710310393995129871)
              ·
                refine ⟨8140052565465590992694807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5426701710310393995129871 8140052565465590992694807)
                ·
                  refine ⟨12210078848198386489042211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8140052565465590992694807 12210078848198386489042211)
                  ·
                    refine ⟨18315118272297579733563317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12210078848198386489042211 18315118272297579733563317)
                    ·
                      refine ⟨1717042338027898100021561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18315118272297579733563317 1717042338027898100021561)
                      ·
                        rfl

theorem cell23_3343928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 2, 1, 1, 1, 5].length) (baseStart_3343928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3343928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3343928 prefixEnd_3343928 := by exact prefixLift 3343928
  have htrace : WordTrace (prefixWord ++ tailWord_3343928) baseStart_3343928 baseEnd_3343928 := by
    simpa [prefixWord, tailWord_3343928, baseEnd_3343928] using wordTrace_append hprefix tailTrace_3343928
  have hstable : (prefixWord ++ tailWord_3343928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3343928).length < 2 ^ (prefixWord ++ tailWord_3343928).sum := by decide
  have hdescent : baseEnd_3343928 < baseStart_3343928 := by decide
  rcases family_descends (prefixWord ++ tailWord_3343928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3343985 : List Nat := [1, 2, 2, 2, 1, 1, 1, 7, 1, 3, 2]
def baseStart_3343985 : Nat := 118140960795 + 3343985 * 2 ^ 59
def prefixEnd_3343985 : Nat := 4983230072969 + 3 ^ 40 * 3343985 * 2
def baseEnd_3343985 : Nat := 1717071606425204377008799

theorem tailTrace_3343985 : CollatzResearch.WordTrace tailWord_3343985 prefixEnd_3343985 1717071606425204377008799 := by
  unfold tailWord_3343985
  simp only [CollatzResearch.WordTrace]
  refine ⟨121965152790320927014945409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81310101860213951343296939 121965152790320927014945409)
  ·
    refine ⟨91473864592740695261209057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121965152790320927014945409 91473864592740695261209057)
    ·
      refine ⟨68605398444555521445906793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91473864592740695261209057 68605398444555521445906793)
      ·
        refine ⟨51454048833416641084430095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68605398444555521445906793 51454048833416641084430095)
        ·
          refine ⟨77181073250124961626645143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51454048833416641084430095 77181073250124961626645143)
          ·
            refine ⟨115771609875187442439967715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77181073250124961626645143 115771609875187442439967715)
            ·
              refine ⟨173657414812781163659951573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115771609875187442439967715 173657414812781163659951573)
              ·
                refine ⟨4070095659674558523280115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 173657414812781163659951573 4070095659674558523280115)
                ·
                  refine ⟨6105143489511837784920173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4070095659674558523280115 6105143489511837784920173)
                  ·
                    refine ⟨2289428808566939169345065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6105143489511837784920173 2289428808566939169345065)
                    ·
                      refine ⟨1717071606425204377008799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2289428808566939169345065 1717071606425204377008799)
                      ·
                        rfl

theorem cell23_3343985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 7, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 7, 1, 3, 2].length) (baseStart_3343985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3343985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3343985 prefixEnd_3343985 := by exact prefixLift 3343985
  have htrace : WordTrace (prefixWord ++ tailWord_3343985) baseStart_3343985 baseEnd_3343985 := by
    simpa [prefixWord, tailWord_3343985, baseEnd_3343985] using wordTrace_append hprefix tailTrace_3343985
  have hstable : (prefixWord ++ tailWord_3343985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3343985).length < 2 ^ (prefixWord ++ tailWord_3343985).sum := by decide
  have hdescent : baseEnd_3343985 < baseStart_3343985 := by decide
  rcases family_descends (prefixWord ++ tailWord_3343985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3343991 : List Nat := [1, 1, 3, 1, 1, 3, 1, 4, 2, 6]
def baseStart_3343991 : Nat := 118140960795 + 3343991 * 2 ^ 59
def prefixEnd_3343991 : Nat := 4983230072969 + 3 ^ 40 * 3343991 * 2
def baseEnd_3343991 : Nat := 572358229103043784511257

theorem tailTrace_3343991 : CollatzResearch.WordTrace tailWord_3343991 prefixEnd_3343991 572358229103043784511257 := by
  unfold tailWord_3343991
  simp only [CollatzResearch.WordTrace]
  refine ⟨121965371628299190039663827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81310247752199460026442551 121965371628299190039663827)
  ·
    refine ⟨182948057442448785059495741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121965371628299190039663827 182948057442448785059495741)
    ·
      refine ⟨68605521540918294397310903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 182948057442448785059495741 68605521540918294397310903)
      ·
        refine ⟨102908282311377441595966355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68605521540918294397310903 102908282311377441595966355)
        ·
          refine ⟨154362423467066162393949533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102908282311377441595966355 154362423467066162393949533)
          ·
            refine ⟨57885908800149810897731075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 154362423467066162393949533 57885908800149810897731075)
            ·
              refine ⟨86828863200224716346596613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57885908800149810897731075 86828863200224716346596613)
              ·
                refine ⟨16280411850042134314986865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 86828863200224716346596613 16280411850042134314986865)
                ·
                  refine ⟨12210308887531600736240149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16280411850042134314986865 12210308887531600736240149)
                  ·
                    refine ⟨572358229103043784511257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12210308887531600736240149 572358229103043784511257)
                    ·
                      rfl

theorem cell23_3343991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 4, 2, 6].length) (baseStart_3343991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3343991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3343991 prefixEnd_3343991 := by exact prefixLift 3343991
  have htrace : WordTrace (prefixWord ++ tailWord_3343991) baseStart_3343991 baseEnd_3343991 := by
    simpa [prefixWord, tailWord_3343991, baseEnd_3343991] using wordTrace_append hprefix tailTrace_3343991
  have hstable : (prefixWord ++ tailWord_3343991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3343991).length < 2 ^ (prefixWord ++ tailWord_3343991).sum := by decide
  have hdescent : baseEnd_3343991 < baseStart_3343991 := by decide
  rcases family_descends (prefixWord ++ tailWord_3343991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3344048 : List Nat := [2, 1, 1, 1, 2, 1, 5, 2, 2, 3, 3]
def baseStart_3344048 : Nat := 118140960795 + 3344048 * 2 ^ 59
def prefixEnd_3344048 : Nat := 4983230072969 + 3 ^ 40 * 3344048 * 2
def baseEnd_3344048 : Nat := 1717103955706437630521009

theorem tailTrace_3344048 : CollatzResearch.WordTrace tailWord_3344048 prefixEnd_3344048 1717103955706437630521009 := by
  unfold tailWord_3344048
  simp only [CollatzResearch.WordTrace]
  refine ⟨60983725294546344387244399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81311633726061792516325865 60983725294546344387244399)
  ·
    refine ⟨91475587941819516580866599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60983725294546344387244399 91475587941819516580866599)
    ·
      refine ⟨137213381912729274871299899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91475587941819516580866599 137213381912729274871299899)
      ·
        refine ⟨205820072869093912306949849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137213381912729274871299899 205820072869093912306949849)
        ·
          refine ⟨154365054651820434230212387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 205820072869093912306949849 154365054651820434230212387)
          ·
            refine ⟨231547581977730651345318581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154365054651820434230212387 231547581977730651345318581)
            ·
              refine ⟨21707585810412248563623617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 231547581977730651345318581 21707585810412248563623617)
              ·
                refine ⟨16280689357809186422717713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21707585810412248563623617 16280689357809186422717713)
                ·
                  refine ⟨12210517018356889817038285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16280689357809186422717713 12210517018356889817038285)
                  ·
                    refine ⟨4578943881883833681389357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12210517018356889817038285 4578943881883833681389357)
                    ·
                      refine ⟨1717103955706437630521009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4578943881883833681389357 1717103955706437630521009)
                      ·
                        rfl

theorem cell23_3344048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 2, 2, 3, 3].length) (baseStart_3344048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3344048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3344048 prefixEnd_3344048 := by exact prefixLift 3344048
  have htrace : WordTrace (prefixWord ++ tailWord_3344048) baseStart_3344048 baseEnd_3344048 := by
    simpa [prefixWord, tailWord_3344048, baseEnd_3344048] using wordTrace_append hprefix tailTrace_3344048
  have hstable : (prefixWord ++ tailWord_3344048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3344048).length < 2 ^ (prefixWord ++ tailWord_3344048).sum := by decide
  have hdescent : baseEnd_3344048 < baseStart_3344048 := by decide
  rcases family_descends (prefixWord ++ tailWord_3344048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3344055 : List Nat := [1, 1, 3, 1, 5, 1, 2, 4, 5]
def baseStart_3344055 : Nat := 118140960795 + 3344055 * 2 ^ 59
def prefixEnd_3344055 : Nat := 4983230072969 + 3 ^ 40 * 3344055 * 2
def baseEnd_3344055 : Nat := 190789727785668789237053

theorem tailTrace_3344055 : CollatzResearch.WordTrace tailWord_3344055 prefixEnd_3344055 190789727785668789237053 := by
  unfold tailWord_3344055
  simp only [CollatzResearch.WordTrace]
  refine ⟨121967705900067328969993619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81311803933378219313329079 121967705900067328969993619)
  ·
    refine ⟨182951558850100993454990429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121967705900067328969993619 182951558850100993454990429)
    ·
      refine ⟨68606834568787872545621411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 182951558850100993454990429 68606834568787872545621411)
      ·
        refine ⟨102910251853181808818432117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68606834568787872545621411 102910251853181808818432117)
        ·
          refine ⟨9647836111235794576728011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 102910251853181808818432117 9647836111235794576728011)
          ·
            refine ⟨14471754166853691865092017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9647836111235794576728011 14471754166853691865092017)
            ·
              refine ⟨10853815625140268898819013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14471754166853691865092017 10853815625140268898819013)
              ·
                refine ⟨2035090429713800418528565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10853815625140268898819013 2035090429713800418528565)
                ·
                  refine ⟨190789727785668789237053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2035090429713800418528565 190789727785668789237053)
                  ·
                    rfl

theorem cell23_3344055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 2, 4, 5].length) (baseStart_3344055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3344055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3344055 prefixEnd_3344055 := by exact prefixLift 3344055
  have htrace : WordTrace (prefixWord ++ tailWord_3344055) baseStart_3344055 baseEnd_3344055 := by
    simpa [prefixWord, tailWord_3344055, baseEnd_3344055] using wordTrace_append hprefix tailTrace_3344055
  have hstable : (prefixWord ++ tailWord_3344055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3344055).length < 2 ^ (prefixWord ++ tailWord_3344055).sum := by decide
  have hdescent : baseEnd_3344055 < baseStart_3344055 := by decide
  rcases family_descends (prefixWord ++ tailWord_3344055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3344068 : List Nat := [2, 3, 3, 1, 1, 1, 1, 1, 3, 7]
def baseStart_3344068 : Nat := 118140960795 + 3344068 * 2 ^ 59
def prefixEnd_3344068 : Nat := 4983230072969 + 3 ^ 40 * 3344068 * 2
def baseEnd_3344068 : Nat := 572371408439842517423639

theorem tailTrace_3344068 : CollatzResearch.WordTrace tailWord_3344068 prefixEnd_3344068 572371408439842517423639 := by
  unfold tailWord_3344068
  simp only [CollatzResearch.WordTrace]
  refine ⟨60984090024510116095108429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81312120032680154793477905 60984090024510116095108429)
  ·
    refine ⟨22869033759191293535665661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60984090024510116095108429 22869033759191293535665661)
    ·
      refine ⟨8575887659696735075874623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22869033759191293535665661 8575887659696735075874623)
      ·
        refine ⟨12863831489545102613811935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8575887659696735075874623 12863831489545102613811935)
        ·
          refine ⟨19295747234317653920717903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12863831489545102613811935 19295747234317653920717903)
          ·
            refine ⟨28943620851476480881076855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19295747234317653920717903 28943620851476480881076855)
            ·
              refine ⟨43415431277214721321615283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28943620851476480881076855 43415431277214721321615283)
              ·
                refine ⟨65123146915822081982422925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43415431277214721321615283 65123146915822081982422925)
                ·
                  refine ⟨24421180093433280743408597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 65123146915822081982422925 24421180093433280743408597)
                  ·
                    refine ⟨572371408439842517423639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24421180093433280743408597 572371408439842517423639)
                    ·
                      rfl

theorem cell23_3344068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 1, 3, 7].length) (baseStart_3344068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3344068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3344068 prefixEnd_3344068 := by exact prefixLift 3344068
  have htrace : WordTrace (prefixWord ++ tailWord_3344068) baseStart_3344068 baseEnd_3344068 := by
    simpa [prefixWord, tailWord_3344068, baseEnd_3344068] using wordTrace_append hprefix tailTrace_3344068
  have hstable : (prefixWord ++ tailWord_3344068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3344068).length < 2 ^ (prefixWord ++ tailWord_3344068).sum := by decide
  have hdescent : baseEnd_3344068 < baseStart_3344068 := by decide
  rcases family_descends (prefixWord ++ tailWord_3344068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3344088 : List Nat := [2, 1, 2, 2, 3, 1, 1, 3, 1, 3, 4]
def baseStart_3344088 : Nat := 118140960795 + 3344088 * 2 ^ 59
def prefixEnd_3344088 : Nat := 4983230072969 + 3 ^ 40 * 3344088 * 2
def baseEnd_3344088 : Nat := 1717124494932617474020825

theorem tailTrace_3344088 : CollatzResearch.WordTrace tailWord_3344088 prefixEnd_3344088 1717124494932617474020825 := by
  unfold tailWord_3344088
  simp only [CollatzResearch.WordTrace]
  refine ⟨60984454754473887802972459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81312606339298517070629945 60984454754473887802972459)
  ·
    refine ⟨91476682131710831704458689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60984454754473887802972459 91476682131710831704458689)
    ·
      refine ⟨68607511598783123778344017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91476682131710831704458689 68607511598783123778344017)
      ·
        refine ⟨51455633699087342833758013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68607511598783123778344017 51455633699087342833758013)
        ·
          refine ⟨19295862637157753562659255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51455633699087342833758013 19295862637157753562659255)
          ·
            refine ⟨28943793955736630343988883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19295862637157753562659255 28943793955736630343988883)
            ·
              refine ⟨43415690933604945515983325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28943793955736630343988883 43415690933604945515983325)
              ·
                refine ⟨16280884100101854568493747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43415690933604945515983325 16280884100101854568493747)
                ·
                  refine ⟨24421326150152781852740621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16280884100101854568493747 24421326150152781852740621)
                  ·
                    refine ⟨9157997306307293194777733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24421326150152781852740621 9157997306307293194777733)
                    ·
                      refine ⟨1717124494932617474020825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9157997306307293194777733 1717124494932617474020825)
                      ·
                        rfl

theorem cell23_3344088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 3, 1, 3, 4].length) (baseStart_3344088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3344088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3344088 prefixEnd_3344088 := by exact prefixLift 3344088
  have htrace : WordTrace (prefixWord ++ tailWord_3344088) baseStart_3344088 baseEnd_3344088 := by
    simpa [prefixWord, tailWord_3344088, baseEnd_3344088] using wordTrace_append hprefix tailTrace_3344088
  have hstable : (prefixWord ++ tailWord_3344088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3344088).length < 2 ^ (prefixWord ++ tailWord_3344088).sum := by decide
  have hdescent : baseEnd_3344088 < baseStart_3344088 := by decide
  rcases family_descends (prefixWord ++ tailWord_3344088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3344091 : List Nat := [1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 11]
def baseStart_3344091 : Nat := 118140960795 + 3344091 * 2 ^ 59
def prefixEnd_3344091 : Nat := 4983230072969 + 3 ^ 40 * 3344091 * 2
def baseEnd_3344091 : Nat := 1717126035374580962283311

theorem tailTrace_3344091 : CollatzResearch.WordTrace tailWord_3344091 prefixEnd_3344091 1717126035374580962283311 := by
  unfold tailWord_3344091
  simp only [CollatzResearch.WordTrace]
  refine ⟨121969018927936907118304127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81312679285291271412202751 121969018927936907118304127)
  ·
    refine ⟨182953528391905360677456191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121969018927936907118304127 182953528391905360677456191)
    ·
      refine ⟨274430292587858041016184287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182953528391905360677456191 274430292587858041016184287)
      ·
        refine ⟨411645438881787061524276431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 274430292587858041016184287 411645438881787061524276431)
        ·
          refine ⟨617468158322680592286414647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 411645438881787061524276431 617468158322680592286414647)
          ·
            refine ⟨926202237484020888429621971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 617468158322680592286414647 926202237484020888429621971)
            ·
              refine ⟨1389303356226031332644432957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 926202237484020888429621971 1389303356226031332644432957)
              ·
                refine ⟨520988758584761749741662359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1389303356226031332644432957 520988758584761749741662359)
                ·
                  refine ⟨781483137877142624612493539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 520988758584761749741662359 781483137877142624612493539)
                  ·
                    refine ⟨1172224706815713936918740309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 781483137877142624612493539 1172224706815713936918740309)
                    ·
                      refine ⟨1717126035374580962283311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 11 1172224706815713936918740309 1717126035374580962283311)
                      ·
                        rfl

theorem cell23_3344091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 11].length) (baseStart_3344091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3344091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3344091 prefixEnd_3344091 := by exact prefixLift 3344091
  have htrace : WordTrace (prefixWord ++ tailWord_3344091) baseStart_3344091 baseEnd_3344091 := by
    simpa [prefixWord, tailWord_3344091, baseEnd_3344091] using wordTrace_append hprefix tailTrace_3344091
  have hstable : (prefixWord ++ tailWord_3344091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3344091).length < 2 ^ (prefixWord ++ tailWord_3344091).sum := by decide
  have hdescent : baseEnd_3344091 < baseStart_3344091 := by decide
  rcases family_descends (prefixWord ++ tailWord_3344091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3344115 : List Nat := [1, 1, 1, 2, 2, 3, 5, 1, 3, 4]
def baseStart_3344115 : Nat := 118140960795 + 3344115 * 2 ^ 59
def prefixEnd_3344115 : Nat := 4983230072969 + 3 ^ 40 * 3344115 * 2
def baseEnd_3344115 : Nat := 572379452970096289461067

theorem tailTrace_3344115 : CollatzResearch.WordTrace tailWord_3344115 prefixEnd_3344115 572379452970096289461067 := by
  unfold tailWord_3344115
  simp only [CollatzResearch.WordTrace]
  refine ⟨121969894279849959217177799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81313262853233306144785199 121969894279849959217177799)
  ·
    refine ⟨182954841419774938825766699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121969894279849959217177799 182954841419774938825766699)
    ·
      refine ⟨274432262129662408238650049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182954841419774938825766699 274432262129662408238650049)
      ·
        refine ⟨205824196597246806178987537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 274432262129662408238650049 205824196597246806178987537)
        ·
          refine ⟨154368147447935104634240653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 205824196597246806178987537 154368147447935104634240653)
          ·
            refine ⟨57888055292975664237840245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 154368147447935104634240653 57888055292975664237840245)
            ·
              refine ⟨5427005183716468522297523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 57888055292975664237840245 5427005183716468522297523)
              ·
                refine ⟨8140507775574702783446285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5427005183716468522297523 8140507775574702783446285)
                ·
                  refine ⟨3052690415840513543792357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8140507775574702783446285 3052690415840513543792357)
                  ·
                    refine ⟨572379452970096289461067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3052690415840513543792357 572379452970096289461067)
                    ·
                      rfl

theorem cell23_3344115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 5, 1, 3, 4].length) (baseStart_3344115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3344115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3344115 prefixEnd_3344115 := by exact prefixLift 3344115
  have htrace : WordTrace (prefixWord ++ tailWord_3344115) baseStart_3344115 baseEnd_3344115 := by
    simpa [prefixWord, tailWord_3344115, baseEnd_3344115] using wordTrace_append hprefix tailTrace_3344115
  have hstable : (prefixWord ++ tailWord_3344115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3344115).length < 2 ^ (prefixWord ++ tailWord_3344115).sum := by decide
  have hdescent : baseEnd_3344115 < baseStart_3344115 := by decide
  rcases family_descends (prefixWord ++ tailWord_3344115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3344128 : List Nat := [2, 1, 1, 2, 1, 1, 2, 7, 6]
def baseStart_3344128 : Nat := 118140960795 + 3344128 * 2 ^ 59
def prefixEnd_3344128 : Nat := 4983230072969 + 3 ^ 40 * 3344128 * 2
def baseEnd_3344128 : Nat := 190793892684310813057849

theorem tailTrace_3344128 : CollatzResearch.WordTrace tailWord_3344128 prefixEnd_3344128 190793892684310813057849 := by
  unfold tailWord_3344128
  simp only [CollatzResearch.WordTrace]
  refine ⟨60985184214401431218700519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81313578952535241624934025 60985184214401431218700519)
  ·
    refine ⟨91477776321602146828050779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60985184214401431218700519 91477776321602146828050779)
    ·
      refine ⟨137216664482403220242076169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91477776321602146828050779 137216664482403220242076169)
      ·
        refine ⟨102912498361802415181557127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137216664482403220242076169 102912498361802415181557127)
        ·
          refine ⟨154368747542703622772335691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102912498361802415181557127 154368747542703622772335691)
          ·
            refine ⟨231553121314055434158503537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154368747542703622772335691 231553121314055434158503537)
            ·
              refine ⟨173664840985541575618877653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 231553121314055434158503537 173664840985541575618877653)
              ·
                refine ⟨4070269710598630678567445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 173664840985541575618877653 4070269710598630678567445)
                ·
                  refine ⟨190793892684310813057849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4070269710598630678567445 190793892684310813057849)
                  ·
                    rfl

theorem cell23_3344128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 7, 6].length) (baseStart_3344128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3344128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3344128 prefixEnd_3344128 := by exact prefixLift 3344128
  have htrace : WordTrace (prefixWord ++ tailWord_3344128) baseStart_3344128 baseEnd_3344128 := by
    simpa [prefixWord, tailWord_3344128, baseEnd_3344128] using wordTrace_append hprefix tailTrace_3344128
  have hstable : (prefixWord ++ tailWord_3344128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3344128).length < 2 ^ (prefixWord ++ tailWord_3344128).sum := by decide
  have hdescent : baseEnd_3344128 < baseStart_3344128 := by decide
  rcases family_descends (prefixWord ++ tailWord_3344128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3344155 : List Nat := [1, 1, 1, 1, 1, 1, 4, 4, 5, 1, 3]
def baseStart_3344155 : Nat := 118140960795 + 3344155 * 2 ^ 59
def prefixEnd_3344155 : Nat := 4983230072969 + 3 ^ 40 * 3344155 * 2
def baseEnd_3344155 : Nat := 1717158898136468711883017

theorem tailTrace_3344155 : CollatzResearch.WordTrace tailWord_3344155 prefixEnd_3344155 1717158898136468711883017 := by
  unfold tailWord_3344155
  simp only [CollatzResearch.WordTrace]
  refine ⟨121971353199705046048633919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81314235466470030699089279 121971353199705046048633919)
  ·
    refine ⟨182957029799557569072950879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121971353199705046048633919 182957029799557569072950879)
    ·
      refine ⟨274435544699336353609426319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182957029799557569072950879 274435544699336353609426319)
      ·
        refine ⟨411653317049004530414139479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 274435544699336353609426319 411653317049004530414139479)
        ·
          refine ⟨617479975573506795621209219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 411653317049004530414139479 617479975573506795621209219)
          ·
            refine ⟨926219963360260193431813829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 617479975573506795621209219 926219963360260193431813829)
            ·
              refine ⟨173666243130048786268465093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 926219963360260193431813829 173666243130048786268465093)
              ·
                refine ⟨32562420586884147425337205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 173666243130048786268465093 32562420586884147425337205)
                ·
                  refine ⟨3052726930020388821125363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 32562420586884147425337205 3052726930020388821125363)
                  ·
                    refine ⟨4579090395030583231688045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3052726930020388821125363 4579090395030583231688045)
                    ·
                      refine ⟨1717158898136468711883017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4579090395030583231688045 1717158898136468711883017)
                      ·
                        rfl

theorem cell23_3344155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 4, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 4, 5, 1, 3].length) (baseStart_3344155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3344155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3344155 prefixEnd_3344155 := by exact prefixLift 3344155
  have htrace : WordTrace (prefixWord ++ tailWord_3344155) baseStart_3344155 baseEnd_3344155 := by
    simpa [prefixWord, tailWord_3344155, baseEnd_3344155] using wordTrace_append hprefix tailTrace_3344155
  have hstable : (prefixWord ++ tailWord_3344155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3344155).length < 2 ^ (prefixWord ++ tailWord_3344155).sum := by decide
  have hdescent : baseEnd_3344155 < baseStart_3344155 := by decide
  rcases family_descends (prefixWord ++ tailWord_3344155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3344189 : List Nat := [1, 4, 1, 4, 1, 2, 1, 2, 3, 1, 3]
def baseStart_3344189 : Nat := 118140960795 + 3344189 * 2 ^ 59
def prefixEnd_3344189 : Nat := 4983230072969 + 3 ^ 40 * 3344189 * 2
def baseEnd_3344189 : Nat := 1717176356478721578857861

theorem tailTrace_3344189 : CollatzResearch.WordTrace tailWord_3344189 prefixEnd_3344189 1717176356478721578857861 := by
  unfold tailWord_3344189
  simp only [CollatzResearch.WordTrace]
  refine ⟨121972593281581869855371621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81315062187721246570247747 121972593281581869855371621)
  ·
    refine ⟨22869861240296600597882179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 121972593281581869855371621 22869861240296600597882179)
    ·
      refine ⟨34304791860444900896823269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22869861240296600597882179 34304791860444900896823269)
      ·
        refine ⟨6432148473833418918154363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34304791860444900896823269 6432148473833418918154363)
        ·
          refine ⟨9648222710750128377231545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6432148473833418918154363 9648222710750128377231545)
          ·
            refine ⟨7236167033062596282923659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9648222710750128377231545 7236167033062596282923659)
            ·
              refine ⟨10854250549593894424385489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7236167033062596282923659 10854250549593894424385489)
              ·
                refine ⟨8140687912195420818289117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10854250549593894424385489 8140687912195420818289117)
                ·
                  refine ⟨3052757967073282806858419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8140687912195420818289117 3052757967073282806858419)
                  ·
                    refine ⟨4579136950609924210287629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3052757967073282806858419 4579136950609924210287629)
                    ·
                      refine ⟨1717176356478721578857861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4579136950609924210287629 1717176356478721578857861)
                      ·
                        rfl

theorem cell23_3344189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 1, 2, 3, 1, 3].length) (baseStart_3344189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3344189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3344189 prefixEnd_3344189 := by exact prefixLift 3344189
  have htrace : WordTrace (prefixWord ++ tailWord_3344189) baseStart_3344189 baseEnd_3344189 := by
    simpa [prefixWord, tailWord_3344189, baseEnd_3344189] using wordTrace_append hprefix tailTrace_3344189
  have hstable : (prefixWord ++ tailWord_3344189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3344189).length < 2 ^ (prefixWord ++ tailWord_3344189).sum := by decide
  have hdescent : baseEnd_3344189 < baseStart_3344189 := by decide
  rcases family_descends (prefixWord ++ tailWord_3344189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3344195 : List Nat := [1, 1, 1, 3, 1, 5, 2, 1, 3, 1, 4]
def baseStart_3344195 : Nat := 118140960795 + 3344195 * 2 ^ 59
def prefixEnd_3344195 : Nat := 4983230072969 + 3 ^ 40 * 3344195 * 2
def baseEnd_3344195 : Nat := 1717179437362648555382833

theorem tailTrace_3344195 : CollatzResearch.WordTrace tailWord_3344195 prefixEnd_3344195 1717179437362648555382833 := by
  unfold tailWord_3344195
  simp only [CollatzResearch.WordTrace]
  refine ⟨121972812119560132880090039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81315208079706755253393359 121972812119560132880090039)
  ·
    refine ⟨182959218179340199320135059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121972812119560132880090039 182959218179340199320135059)
    ·
      refine ⟨274438827269010298980202589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182959218179340199320135059 274438827269010298980202589)
      ·
        refine ⟨102914560225878862117575971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 274438827269010298980202589 102914560225878862117575971)
        ·
          refine ⟨154371840338818293176363957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102914560225878862117575971 154371840338818293176363957)
          ·
            refine ⟨14472360031764214985284121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 154371840338818293176363957 14472360031764214985284121)
            ·
              refine ⟨10854270023823161238963091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14472360031764214985284121 10854270023823161238963091)
              ·
                refine ⟨16281405035734741858444637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10854270023823161238963091 16281405035734741858444637)
                ·
                  refine ⟨6105526888400528196916739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16281405035734741858444637 6105526888400528196916739)
                  ·
                    refine ⟨9158290332600792295375109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6105526888400528196916739 9158290332600792295375109)
                    ·
                      refine ⟨1717179437362648555382833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9158290332600792295375109 1717179437362648555382833)
                      ·
                        rfl

theorem cell23_3344195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 2, 1, 3, 1, 4].length) (baseStart_3344195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3344195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3344195 prefixEnd_3344195 := by exact prefixLift 3344195
  have htrace : WordTrace (prefixWord ++ tailWord_3344195) baseStart_3344195 baseEnd_3344195 := by
    simpa [prefixWord, tailWord_3344195, baseEnd_3344195] using wordTrace_append hprefix tailTrace_3344195
  have hstable : (prefixWord ++ tailWord_3344195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3344195).length < 2 ^ (prefixWord ++ tailWord_3344195).sum := by decide
  have hdescent : baseEnd_3344195 < baseStart_3344195 := by decide
  rcases family_descends (prefixWord ++ tailWord_3344195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3344208 : List Nat := [2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 6]
def baseStart_3344208 : Nat := 118140960795 + 3344208 * 2 ^ 59
def prefixEnd_3344208 : Nat := 4983230072969 + 3 ^ 40 * 3344208 * 2
def baseEnd_3344208 : Nat := 1717186112611157004520273

theorem tailTrace_3344208 : CollatzResearch.WordTrace tailWord_3344208 prefixEnd_3344208 1717186112611157004520273 := by
  unfold tailWord_3344208
  simp only [CollatzResearch.WordTrace]
  refine ⟨60986643134256518050156639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81315524179008690733542185 60986643134256518050156639)
  ·
    refine ⟨91479964701384777075234959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60986643134256518050156639 91479964701384777075234959)
    ·
      refine ⟨137219947052077165612852439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91479964701384777075234959 137219947052077165612852439)
      ·
        refine ⟨205829920578115748419278659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137219947052077165612852439 205829920578115748419278659)
        ·
          refine ⟨308744880867173622628917989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 205829920578115748419278659 308744880867173622628917989)
          ·
            refine ⟨57889665162595054242922123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 308744880867173622628917989 57889665162595054242922123)
            ·
              refine ⟨86834497743892581364383185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57889665162595054242922123 86834497743892581364383185)
              ·
                refine ⟨65125873307919436023287389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86834497743892581364383185 65125873307919436023287389)
                ·
                  refine ⟨24422202490469788508732771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 65125873307919436023287389 24422202490469788508732771)
                  ·
                    refine ⟨36633303735704682763099157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24422202490469788508732771 36633303735704682763099157)
                    ·
                      refine ⟨1717186112611157004520273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 36633303735704682763099157 1717186112611157004520273)
                      ·
                        rfl

theorem cell23_3344208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 6].length) (baseStart_3344208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3344208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3344208 prefixEnd_3344208 := by exact prefixLift 3344208
  have htrace : WordTrace (prefixWord ++ tailWord_3344208) baseStart_3344208 baseEnd_3344208 := by
    simpa [prefixWord, tailWord_3344208, baseEnd_3344208] using wordTrace_append hprefix tailTrace_3344208
  have hstable : (prefixWord ++ tailWord_3344208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3344208).length < 2 ^ (prefixWord ++ tailWord_3344208).sum := by decide
  have hdescent : baseEnd_3344208 < baseStart_3344208 := by decide
  rcases family_descends (prefixWord ++ tailWord_3344208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3344209 : List Nat := [1, 2, 2, 1, 5, 3, 2, 1, 1, 5]
def baseStart_3344209 : Nat := 118140960795 + 3344209 * 2 ^ 59
def prefixEnd_3344209 : Nat := 4983230072969 + 3 ^ 40 * 3344209 * 2
def baseEnd_3344209 : Nat := 572395542030603833535923

theorem tailTrace_3344209 : CollatzResearch.WordTrace tailWord_3344209 prefixEnd_3344209 572395542030603833535923 := by
  unfold tailWord_3344209
  simp only [CollatzResearch.WordTrace]
  refine ⟨121973322741509413271099681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81315548494339608847399787 121973322741509413271099681)
  ·
    refine ⟨91479992056132059953324761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121973322741509413271099681 91479992056132059953324761)
    ·
      refine ⟨68609994042099044964993571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91479992056132059953324761 68609994042099044964993571)
      ·
        refine ⟨102914991063148567447490357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68609994042099044964993571 102914991063148567447490357)
        ·
          refine ⟨9648280412170178198202221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 102914991063148567447490357 9648280412170178198202221)
          ·
            refine ⟨3618105154563816824325833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9648280412170178198202221 3618105154563816824325833)
            ·
              refine ⟨2713578865922862618244375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3618105154563816824325833 2713578865922862618244375)
              ·
                refine ⟨4070368298884293927366563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2713578865922862618244375 4070368298884293927366563)
                ·
                  refine ⟨6105552448326440891049845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4070368298884293927366563 6105552448326440891049845)
                  ·
                    refine ⟨572395542030603833535923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6105552448326440891049845 572395542030603833535923)
                    ·
                      rfl

theorem cell23_3344209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 3, 2, 1, 1, 5].length) (baseStart_3344209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3344209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3344209 prefixEnd_3344209 := by exact prefixLift 3344209
  have htrace : WordTrace (prefixWord ++ tailWord_3344209) baseStart_3344209 baseEnd_3344209 := by
    simpa [prefixWord, tailWord_3344209, baseEnd_3344209] using wordTrace_append hprefix tailTrace_3344209
  have hstable : (prefixWord ++ tailWord_3344209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3344209).length < 2 ^ (prefixWord ++ tailWord_3344209).sum := by decide
  have hdescent : baseEnd_3344209 < baseStart_3344209 := by decide
  rcases family_descends (prefixWord ++ tailWord_3344209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3344218 : List Nat := [3, 1, 1, 2, 1, 3, 12]
def baseStart_3344218 : Nat := 118140960795 + 3344218 * 2 ^ 59
def prefixEnd_3344218 : Nat := 4983230072969 + 3 ^ 40 * 3344218 * 2
def baseEnd_3344218 : Nat := 21199891943428419325867

theorem tailTrace_3344218 : CollatzResearch.WordTrace tailWord_3344218 prefixEnd_3344218 21199891943428419325867 := by
  unfold tailWord_3344218
  simp only [CollatzResearch.WordTrace]
  refine ⟨30493412749619201952044327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81315767332317871872118205 30493412749619201952044327)
  ·
    refine ⟨45740119124428802928066491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30493412749619201952044327 45740119124428802928066491)
    ·
      refine ⟨68610178686643204392099737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45740119124428802928066491 68610178686643204392099737)
      ·
        refine ⟨51457634014982403294074803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68610178686643204392099737 51457634014982403294074803)
        ·
          refine ⟨77186451022473604941112205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51457634014982403294074803 77186451022473604941112205)
          ·
            refine ⟨28944919133427601852917077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77186451022473604941112205 28944919133427601852917077)
            ·
              refine ⟨21199891943428419325867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 28944919133427601852917077 21199891943428419325867)
              ·
                rfl

theorem cell23_3344218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 12].length) (baseStart_3344218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3344218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3344218 prefixEnd_3344218 := by exact prefixLift 3344218
  have htrace : WordTrace (prefixWord ++ tailWord_3344218) baseStart_3344218 baseEnd_3344218 := by
    simpa [prefixWord, tailWord_3344218, baseEnd_3344218] using wordTrace_append hprefix tailTrace_3344218
  have hstable : (prefixWord ++ tailWord_3344218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3344218).length < 2 ^ (prefixWord ++ tailWord_3344218).sum := by decide
  have hdescent : baseEnd_3344218 < baseStart_3344218 := by decide
  rcases family_descends (prefixWord ++ tailWord_3344218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3344246 : List Nat := [5, 1, 1, 3, 2, 1, 2, 2, 1, 1, 4]
def baseStart_3344246 : Nat := 118140960795 + 3344246 * 2 ^ 59
def prefixEnd_3344246 : Nat := 4983230072969 + 3 ^ 40 * 3344246 * 2
def baseEnd_3344246 : Nat := 1717205624876027855845099

theorem tailTrace_3344246 : CollatzResearch.WordTrace tailWord_3344246 prefixEnd_3344246 1717205624876027855845099 := by
  unfold tailWord_3344246
  simp only [CollatzResearch.WordTrace]
  refine ⟨7623417015148460536887287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 81316448161583579060131061 7623417015148460536887287)
  ·
    refine ⟨11435125522722690805330931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7623417015148460536887287 11435125522722690805330931)
    ·
      refine ⟨17152688284084036207996397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11435125522722690805330931 17152688284084036207996397)
      ·
        refine ⟨6432258106531513577998649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17152688284084036207996397 6432258106531513577998649)
        ·
          refine ⟨4824193579898635183498987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6432258106531513577998649 4824193579898635183498987)
          ·
            refine ⟨7236290369847952775248481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4824193579898635183498987 7236290369847952775248481)
            ·
              refine ⟨5427217777385964581436361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7236290369847952775248481 5427217777385964581436361)
              ·
                refine ⟨4070413333039473436077271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5427217777385964581436361 4070413333039473436077271)
                ·
                  refine ⟨6105619999559210154115907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4070413333039473436077271 6105619999559210154115907)
                  ·
                    refine ⟨9158429999338815231173861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6105619999559210154115907 9158429999338815231173861)
                    ·
                      refine ⟨1717205624876027855845099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9158429999338815231173861 1717205624876027855845099)
                      ·
                        rfl

theorem cell23_3344246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 2, 2, 1, 1, 4].length) (baseStart_3344246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3344246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3344246 prefixEnd_3344246 := by exact prefixLift 3344246
  have htrace : WordTrace (prefixWord ++ tailWord_3344246) baseStart_3344246 baseEnd_3344246 := by
    simpa [prefixWord, tailWord_3344246, baseEnd_3344246] using wordTrace_append hprefix tailTrace_3344246
  have hstable : (prefixWord ++ tailWord_3344246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3344246).length < 2 ^ (prefixWord ++ tailWord_3344246).sum := by decide
  have hdescent : baseEnd_3344246 < baseStart_3344246 := by decide
  rcases family_descends (prefixWord ++ tailWord_3344246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3344248 : List Nat := [2, 1, 2, 1, 1, 1, 1, 2, 3, 9]
def baseStart_3344248 : Nat := 118140960795 + 3344248 * 2 ^ 59
def prefixEnd_3344248 : Nat := 4983230072969 + 3 ^ 40 * 3344248 * 2
def baseEnd_3344248 : Nat := 572402217279112282673363

theorem tailTrace_3344248 : CollatzResearch.WordTrace tailWord_3344248 prefixEnd_3344248 572402217279112282673363 := by
  unfold tailWord_3344248
  simp only [CollatzResearch.WordTrace]
  refine ⟨60987372594184061465884699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81316496792245415287846265 60987372594184061465884699)
  ·
    refine ⟨91481058891276092198827049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60987372594184061465884699 91481058891276092198827049)
    ·
      refine ⟨68610794168457069149120287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91481058891276092198827049 68610794168457069149120287)
      ·
        refine ⟨102916191252685603723680431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68610794168457069149120287 102916191252685603723680431)
        ·
          refine ⟨154374286879028405585520647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102916191252685603723680431 154374286879028405585520647)
          ·
            refine ⟨231561430318542608378280971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154374286879028405585520647 231561430318542608378280971)
            ·
              refine ⟨347342145477813912567421457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 231561430318542608378280971 347342145477813912567421457)
              ·
                refine ⟨260506609108360434425566093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 347342145477813912567421457 260506609108360434425566093)
                ·
                  refine ⟨97689978415635162909587285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 260506609108360434425566093 97689978415635162909587285)
                  ·
                    refine ⟨572402217279112282673363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 97689978415635162909587285 572402217279112282673363)
                    ·
                      rfl

theorem cell23_3344248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 3, 9].length) (baseStart_3344248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3344248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3344248 prefixEnd_3344248 := by exact prefixLift 3344248
  have htrace : WordTrace (prefixWord ++ tailWord_3344248) baseStart_3344248 baseEnd_3344248 := by
    simpa [prefixWord, tailWord_3344248, baseEnd_3344248] using wordTrace_append hprefix tailTrace_3344248
  have hstable : (prefixWord ++ tailWord_3344248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3344248).length < 2 ^ (prefixWord ++ tailWord_3344248).sum := by decide
  have hdescent : baseEnd_3344248 < baseStart_3344248 := by decide
  rcases family_descends (prefixWord ++ tailWord_3344248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3344280 : List Nat := [2, 1, 2, 6, 2, 1, 1, 1, 3, 2, 2]
def baseStart_3344280 : Nat := 118140960795 + 3344280 * 2 ^ 59
def prefixEnd_3344280 : Nat := 4983230072969 + 3 ^ 40 * 3344280 * 2
def baseEnd_3344280 : Nat := 1717223083218280722819943

theorem tailTrace_3344280 : CollatzResearch.WordTrace tailWord_3344280 prefixEnd_3344280 1717223083218280722819943 := by
  unfold tailWord_3344280
  simp only [CollatzResearch.WordTrace]
  refine ⟨60987956162126096198467147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81317274882834794931289529 60987956162126096198467147)
  ·
    refine ⟨91481934243189144297700721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60987956162126096198467147 91481934243189144297700721)
    ·
      refine ⟨68611450682391858223275541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91481934243189144297700721 68611450682391858223275541)
      ·
        refine ⟨3216161750737118354216041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 68611450682391858223275541 3216161750737118354216041)
        ·
          refine ⟨2412121313052838765662031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3216161750737118354216041 2412121313052838765662031)
          ·
            refine ⟨3618181969579258148493047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2412121313052838765662031 3618181969579258148493047)
            ·
              refine ⟨5427272954368887222739571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3618181969579258148493047 5427272954368887222739571)
              ·
                refine ⟨8140909431553330834109357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5427272954368887222739571 8140909431553330834109357)
                ·
                  refine ⟨3052841036832499062791009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8140909431553330834109357 3052841036832499062791009)
                  ·
                    refine ⟨2289630777624374297093257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3052841036832499062791009 2289630777624374297093257)
                    ·
                      refine ⟨1717223083218280722819943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2289630777624374297093257 1717223083218280722819943)
                      ·
                        rfl

theorem cell23_3344280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 1, 1, 1, 3, 2, 2].length) (baseStart_3344280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3344280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3344280 prefixEnd_3344280 := by exact prefixLift 3344280
  have htrace : WordTrace (prefixWord ++ tailWord_3344280) baseStart_3344280 baseEnd_3344280 := by
    simpa [prefixWord, tailWord_3344280, baseEnd_3344280] using wordTrace_append hprefix tailTrace_3344280
  have hstable : (prefixWord ++ tailWord_3344280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3344280).length < 2 ^ (prefixWord ++ tailWord_3344280).sum := by decide
  have hdescent : baseEnd_3344280 < baseStart_3344280 := by decide
  rcases family_descends (prefixWord ++ tailWord_3344280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3344349 : List Nat := [1, 4, 3, 1, 3, 1, 1, 1, 2, 2, 4]
def baseStart_3344349 : Nat := 118140960795 + 3344349 * 2 ^ 59
def prefixEnd_3344349 : Nat := 4983230072969 + 3 ^ 40 * 3344349 * 2
def baseEnd_3344349 : Nat := 1717258513383440952857125

theorem tailTrace_3344349 : CollatzResearch.WordTrace tailWord_3344349 prefixEnd_3344349 1717258513383440952857125 := by
  unfold tailWord_3344349
  simp only [CollatzResearch.WordTrace]
  refine ⟨121978428961002217181196101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81318952640668144787464067 121978428961002217181196101)
  ·
    refine ⟨22870955430187915721474269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 121978428961002217181196101 22870955430187915721474269)
    ·
      refine ⟨8576608286320468395552851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22870955430187915721474269 8576608286320468395552851)
      ·
        refine ⟨12864912429480702593329277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8576608286320468395552851 12864912429480702593329277)
        ·
          refine ⟨4824342161055263472498479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12864912429480702593329277 4824342161055263472498479)
          ·
            refine ⟨7236513241582895208747719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4824342161055263472498479 7236513241582895208747719)
            ·
              refine ⟨10854769862374342813121579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7236513241582895208747719 10854769862374342813121579)
              ·
                refine ⟨16282154793561514219682369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10854769862374342813121579 16282154793561514219682369)
                ·
                  refine ⟨12211616095171135664761777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16282154793561514219682369 12211616095171135664761777)
                  ·
                    refine ⟨9158712071378351748571333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12211616095171135664761777 9158712071378351748571333)
                    ·
                      refine ⟨1717258513383440952857125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9158712071378351748571333 1717258513383440952857125)
                      ·
                        rfl

theorem cell23_3344349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 1, 1, 2, 2, 4].length) (baseStart_3344349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3344349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3344349 prefixEnd_3344349 := by exact prefixLift 3344349
  have htrace : WordTrace (prefixWord ++ tailWord_3344349) baseStart_3344349 baseEnd_3344349 := by
    simpa [prefixWord, tailWord_3344349, baseEnd_3344349] using wordTrace_append hprefix tailTrace_3344349
  have hstable : (prefixWord ++ tailWord_3344349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3344349).length < 2 ^ (prefixWord ++ tailWord_3344349).sum := by decide
  have hdescent : baseEnd_3344349 < baseStart_3344349 := by decide
  rcases family_descends (prefixWord ++ tailWord_3344349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3344392 : List Nat := [2, 1, 3, 2, 1, 2, 2, 1, 4, 1, 4]
def baseStart_3344392 : Nat := 118140960795 + 3344392 * 2 ^ 59
def prefixEnd_3344392 : Nat := 4983230072969 + 3 ^ 40 * 3344392 * 2
def baseEnd_3344392 : Nat := 1717280593051584284619427

theorem tailTrace_3344392 : CollatzResearch.WordTrace tailWord_3344392 prefixEnd_3344392 1717280593051584284619427 := by
  unfold tailWord_3344392
  simp only [CollatzResearch.WordTrace]
  refine ⟨60989998649923217762505715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81319998199897623683340953 60989998649923217762505715)
  ·
    refine ⟨91484997974884826643758573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60989998649923217762505715 91484997974884826643758573)
    ·
      refine ⟨34306874240581809991409465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91484997974884826643758573 34306874240581809991409465)
      ·
        refine ⟨25730155680436357493557099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34306874240581809991409465 25730155680436357493557099)
        ·
          refine ⟨38595233520654536240335649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25730155680436357493557099 38595233520654536240335649)
          ·
            refine ⟨28946425140490902180251737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38595233520654536240335649 28946425140490902180251737)
            ·
              refine ⟨21709818855368176635188803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28946425140490902180251737 21709818855368176635188803)
              ·
                refine ⟨32564728283052264952783205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21709818855368176635188803 32564728283052264952783205)
                ·
                  refine ⟨6105886553072299678646851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32564728283052264952783205 6105886553072299678646851)
                  ·
                    refine ⟨9158829829608449517970277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6105886553072299678646851 9158829829608449517970277)
                    ·
                      refine ⟨1717280593051584284619427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9158829829608449517970277 1717280593051584284619427)
                      ·
                        rfl

theorem cell23_3344392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 1, 4, 1, 4].length) (baseStart_3344392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3344392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3344392 prefixEnd_3344392 := by exact prefixLift 3344392
  have htrace : WordTrace (prefixWord ++ tailWord_3344392) baseStart_3344392 baseEnd_3344392 := by
    simpa [prefixWord, tailWord_3344392, baseEnd_3344392] using wordTrace_append hprefix tailTrace_3344392
  have hstable : (prefixWord ++ tailWord_3344392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3344392).length < 2 ^ (prefixWord ++ tailWord_3344392).sum := by decide
  have hdescent : baseEnd_3344392 < baseStart_3344392 := by decide
  rcases family_descends (prefixWord ++ tailWord_3344392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3344492 : List Nat := [2, 2, 1, 1, 3, 3, 1, 1, 3, 6]
def baseStart_3344492 : Nat := 118140960795 + 3344492 * 2 ^ 59
def prefixEnd_3344492 : Nat := 4983230072969 + 3 ^ 40 * 3344492 * 2
def baseEnd_3344492 : Nat := 572443980372344631122989

theorem tailTrace_3344492 : CollatzResearch.WordTrace tailWord_3344492 prefixEnd_3344492 572443980372344631122989 := by
  unfold tailWord_3344492
  simp only [CollatzResearch.WordTrace]
  refine ⟨60991822299742076301825865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81322429732989435069101153 60991822299742076301825865)
  ·
    refine ⟨45743866724806557226369399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60991822299742076301825865 45743866724806557226369399)
    ·
      refine ⟨68615800087209835839554099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45743866724806557226369399 68615800087209835839554099)
      ·
        refine ⟨102923700130814753759331149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68615800087209835839554099 102923700130814753759331149)
        ·
          refine ⟨38596387549055532659749181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102923700130814753759331149 38596387549055532659749181)
          ·
            refine ⟨14473645330895824747405943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38596387549055532659749181 14473645330895824747405943)
            ·
              refine ⟨21710467996343737121108915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14473645330895824747405943 21710467996343737121108915)
              ·
                refine ⟨32565701994515605681663373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21710467996343737121108915 32565701994515605681663373)
                ·
                  refine ⟨12212138247943352130623765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32565701994515605681663373 12212138247943352130623765)
                  ·
                    refine ⟨572443980372344631122989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12212138247943352130623765 572443980372344631122989)
                    ·
                      rfl

theorem cell23_3344492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 6].length) (baseStart_3344492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3344492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3344492 prefixEnd_3344492 := by exact prefixLift 3344492
  have htrace : WordTrace (prefixWord ++ tailWord_3344492) baseStart_3344492 baseEnd_3344492 := by
    simpa [prefixWord, tailWord_3344492, baseEnd_3344492] using wordTrace_append hprefix tailTrace_3344492
  have hstable : (prefixWord ++ tailWord_3344492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3344492).length < 2 ^ (prefixWord ++ tailWord_3344492).sum := by decide
  have hdescent : baseEnd_3344492 < baseStart_3344492 := by decide
  rcases family_descends (prefixWord ++ tailWord_3344492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3344493 : List Nat := [1, 5, 1, 1, 2, 1, 2, 5, 1, 1, 3]
def baseStart_3344493 : Nat := 118140960795 + 3344493 * 2 ^ 59
def prefixEnd_3344493 : Nat := 4983230072969 + 3 ^ 40 * 3344493 * 2
def baseEnd_3344493 : Nat := 1717332454597688389456463

theorem tailTrace_3344493 : CollatzResearch.WordTrace tailWord_3344493 prefixEnd_3344493 1717332454597688389456463 := by
  unfold tailWord_3344493
  simp only [CollatzResearch.WordTrace]
  refine ⟨121983681072480529774438133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81322454048320353182958755 121983681072480529774438133)
  ·
    refine ⟨11435970100545049666353575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 121983681072480529774438133 11435970100545049666353575)
    ·
      refine ⟨17153955150817574499530363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11435970100545049666353575 17153955150817574499530363)
      ·
        refine ⟨25730932726226361749295545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17153955150817574499530363 25730932726226361749295545)
        ·
          refine ⟨19298199544669771311971659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25730932726226361749295545 19298199544669771311971659)
          ·
            refine ⟨28947299317004656967957489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19298199544669771311971659 28947299317004656967957489)
            ·
              refine ⟨21710474487753492725968117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28947299317004656967957489 21710474487753492725968117)
              ·
                refine ⟨2035356983226889943059511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21710474487753492725968117 2035356983226889943059511)
                ·
                  refine ⟨3053035474840334914589267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2035356983226889943059511 3053035474840334914589267)
                  ·
                    refine ⟨4579553212260502371883901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3053035474840334914589267 4579553212260502371883901)
                    ·
                      refine ⟨1717332454597688389456463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4579553212260502371883901 1717332454597688389456463)
                      ·
                        rfl

theorem cell23_3344493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 5, 1, 1, 3].length) (baseStart_3344493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3344493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3344493 prefixEnd_3344493 := by exact prefixLift 3344493
  have htrace : WordTrace (prefixWord ++ tailWord_3344493) baseStart_3344493 baseEnd_3344493 := by
    simpa [prefixWord, tailWord_3344493, baseEnd_3344493] using wordTrace_append hprefix tailTrace_3344493
  have hstable : (prefixWord ++ tailWord_3344493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3344493).length < 2 ^ (prefixWord ++ tailWord_3344493).sum := by decide
  have hdescent : baseEnd_3344493 < baseStart_3344493 := by decide
  rcases family_descends (prefixWord ++ tailWord_3344493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3344496 : List Nat := [2, 1, 1, 1, 5, 3, 3, 1, 1, 5]
def baseStart_3344496 : Nat := 118140960795 + 3344496 * 2 ^ 59
def prefixEnd_3344496 : Nat := 4983230072969 + 3 ^ 40 * 3344496 * 2
def baseEnd_3344496 : Nat := 572444665013217292572983

theorem tailTrace_3344496 : CollatzResearch.WordTrace tailWord_3344496 prefixEnd_3344496 572444665013217292572983 := by
  unfold tailWord_3344496
  simp only [CollatzResearch.WordTrace]
  refine ⟨60991895245734830643398671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81322526994313107524531561 60991895245734830643398671)
  ·
    refine ⟨91487842868602245965098007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60991895245734830643398671 91487842868602245965098007)
    ·
      refine ⟨137231764302903368947647011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91487842868602245965098007 137231764302903368947647011)
      ·
        refine ⟨205847646454355053421470517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137231764302903368947647011 205847646454355053421470517)
        ·
          refine ⟨19298216855095786258262861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 205847646454355053421470517 19298216855095786258262861)
          ·
            refine ⟨7236831320660919846848573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19298216855095786258262861 7236831320660919846848573)
            ·
              refine ⟨2713811745247844942568215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7236831320660919846848573 2713811745247844942568215)
              ·
                refine ⟨4070717617871767413852323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2713811745247844942568215 4070717617871767413852323)
                ·
                  refine ⟨6106076426807651120778485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4070717617871767413852323 6106076426807651120778485)
                  ·
                    refine ⟨572444665013217292572983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6106076426807651120778485 572444665013217292572983)
                    ·
                      rfl

theorem cell23_3344496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 3, 1, 1, 5].length) (baseStart_3344496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3344496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3344496 prefixEnd_3344496 := by exact prefixLift 3344496
  have htrace : WordTrace (prefixWord ++ tailWord_3344496) baseStart_3344496 baseEnd_3344496 := by
    simpa [prefixWord, tailWord_3344496, baseEnd_3344496] using wordTrace_append hprefix tailTrace_3344496
  have hstable : (prefixWord ++ tailWord_3344496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3344496).length < 2 ^ (prefixWord ++ tailWord_3344496).sum := by decide
  have hdescent : baseEnd_3344496 < baseStart_3344496 := by decide
  rcases family_descends (prefixWord ++ tailWord_3344496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3344512 : List Nat := [2, 1, 1, 2, 1, 3, 1, 1, 5, 2, 4]
def baseStart_3344512 : Nat := 118140960795 + 3344512 * 2 ^ 59
def prefixEnd_3344512 : Nat := 4983230072969 + 3 ^ 40 * 3344512 * 2
def baseEnd_3344512 : Nat := 1717342210730123815118875

theorem tailTrace_3344512 : CollatzResearch.WordTrace tailWord_3344512 prefixEnd_3344512 1717342210730123815118875 := by
  unfold tailWord_3344512
  simp only [CollatzResearch.WordTrace]
  refine ⟨60992187029705848009689895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81322916039607797346253193 60992187029705848009689895)
  ·
    refine ⟨91488280544558772014534843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60992187029705848009689895 91488280544558772014534843)
    ·
      refine ⟨137232420816838158021802265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91488280544558772014534843 137232420816838158021802265)
      ·
        refine ⟨102924315612628618516351699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137232420816838158021802265 102924315612628618516351699)
        ·
          refine ⟨154386473418942927774527549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102924315612628618516351699 154386473418942927774527549)
          ·
            refine ⟨57894927532103597915447831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 154386473418942927774527549 57894927532103597915447831)
            ·
              refine ⟨86842391298155396873171747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57894927532103597915447831 86842391298155396873171747)
              ·
                refine ⟨130263586947233095309757621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86842391298155396873171747 130263586947233095309757621)
                ·
                  refine ⟨12212211276303102685289777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 130263586947233095309757621 12212211276303102685289777)
                  ·
                    refine ⟨9159158457227327013967333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12212211276303102685289777 9159158457227327013967333)
                    ·
                      refine ⟨1717342210730123815118875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9159158457227327013967333 1717342210730123815118875)
                      ·
                        rfl

theorem cell23_3344512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 1, 5, 2, 4].length) (baseStart_3344512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3344512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3344512 prefixEnd_3344512 := by exact prefixLift 3344512
  have htrace : WordTrace (prefixWord ++ tailWord_3344512) baseStart_3344512 baseEnd_3344512 := by
    simpa [prefixWord, tailWord_3344512, baseEnd_3344512] using wordTrace_append hprefix tailTrace_3344512
  have hstable : (prefixWord ++ tailWord_3344512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3344512).length < 2 ^ (prefixWord ++ tailWord_3344512).sum := by decide
  have hdescent : baseEnd_3344512 < baseStart_3344512 := by decide
  rcases family_descends (prefixWord ++ tailWord_3344512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3344519 : List Nat := [1, 1, 4, 2, 1, 1, 3, 2, 3, 2, 3]
def baseStart_3344519 : Nat := 118140960795 + 3344519 * 2 ^ 59
def prefixEnd_3344519 : Nat := 4983230072969 + 3 ^ 40 * 3344519 * 2
def baseEnd_3344519 : Nat := 1717345805094705287731343

theorem tailTrace_3344519 : CollatzResearch.WordTrace tailWord_3344519 prefixEnd_3344519 1717345805094705287731343 := by
  unfold tailWord_3344519
  simp only [CollatzResearch.WordTrace]
  refine ⟨121984629370386336214884611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81323086246924224143256407 121984629370386336214884611)
  ·
    refine ⟨182976944055579504322326917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121984629370386336214884611 182976944055579504322326917)
    ·
      refine ⟨34308177010421157060436297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 182976944055579504322326917 34308177010421157060436297)
      ·
        refine ⟨25731132757815867795327223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34308177010421157060436297 25731132757815867795327223)
        ·
          refine ⟨38596699136723801692990835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25731132757815867795327223 38596699136723801692990835)
          ·
            refine ⟨57895048705085702539486253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38596699136723801692990835 57895048705085702539486253)
            ·
              refine ⟨21710643264407138452307345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57895048705085702539486253 21710643264407138452307345)
              ·
                refine ⟨16282982448305353839230509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21710643264407138452307345 16282982448305353839230509)
                ·
                  refine ⟨6106118418114507689711441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16282982448305353839230509 6106118418114507689711441)
                  ·
                    refine ⟨4579588813585880767283581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6106118418114507689711441 4579588813585880767283581)
                    ·
                      refine ⟨1717345805094705287731343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4579588813585880767283581 1717345805094705287731343)
                      ·
                        rfl

theorem cell23_3344519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 2, 3, 2, 3].length) (baseStart_3344519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3344519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3344519 prefixEnd_3344519 := by exact prefixLift 3344519
  have htrace : WordTrace (prefixWord ++ tailWord_3344519) baseStart_3344519 baseEnd_3344519 := by
    simpa [prefixWord, tailWord_3344519, baseEnd_3344519] using wordTrace_append hprefix tailTrace_3344519
  have hstable : (prefixWord ++ tailWord_3344519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3344519).length < 2 ^ (prefixWord ++ tailWord_3344519).sum := by decide
  have hdescent : baseEnd_3344519 < baseStart_3344519 := by decide
  rcases family_descends (prefixWord ++ tailWord_3344519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3344526 : List Nat := [4, 1, 1, 3, 3, 1, 2, 1, 1, 6]
def baseStart_3344526 : Nat := 118140960795 + 3344526 * 2 ^ 59
def prefixEnd_3344526 : Nat := 4983230072969 + 3 ^ 40 * 3344526 * 2
def baseEnd_3344526 : Nat := 572449799819762253447937

theorem tailTrace_3344526 : CollatzResearch.WordTrace tailWord_3344526 prefixEnd_3344526 572449799819762253447937 := by
  unfold tailWord_3344526
  simp only [CollatzResearch.WordTrace]
  refine ⟨15248110585170122051298679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81323256454240650940259621 15248110585170122051298679)
  ·
    refine ⟨22872165877755183076948019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15248110585170122051298679 22872165877755183076948019)
    ·
      refine ⟨34308248816632774615422029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22872165877755183076948019 34308248816632774615422029)
      ·
        refine ⟨12865593306237290480783261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34308248816632774615422029 12865593306237290480783261)
        ·
          refine ⟨4824597489838983930293723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12865593306237290480783261 4824597489838983930293723)
          ·
            refine ⟨7236896234758475895440585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4824597489838983930293723 7236896234758475895440585)
            ·
              refine ⟨5427672176068856921580439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7236896234758475895440585 5427672176068856921580439)
              ·
                refine ⟨8141508264103285382370659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5427672176068856921580439 8141508264103285382370659)
                ·
                  refine ⟨12212262396154928073555989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8141508264103285382370659 12212262396154928073555989)
                  ·
                    refine ⟨572449799819762253447937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12212262396154928073555989 572449799819762253447937)
                    ·
                      rfl

theorem cell23_3344526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 2, 1, 1, 6].length) (baseStart_3344526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3344526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3344526 prefixEnd_3344526 := by exact prefixLift 3344526
  have htrace : WordTrace (prefixWord ++ tailWord_3344526) baseStart_3344526 baseEnd_3344526 := by
    simpa [prefixWord, tailWord_3344526, baseEnd_3344526] using wordTrace_append hprefix tailTrace_3344526
  have hstable : (prefixWord ++ tailWord_3344526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3344526).length < 2 ^ (prefixWord ++ tailWord_3344526).sum := by decide
  have hdescent : baseEnd_3344526 < baseStart_3344526 := by decide
  rcases family_descends (prefixWord ++ tailWord_3344526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3344546 : List Nat := [3, 3, 1, 3, 1, 1, 2, 2, 1, 2, 4]
def baseStart_3344546 : Nat := 118140960795 + 3344546 * 2 ^ 59
def prefixEnd_3344546 : Nat := 4983230072969 + 3 ^ 40 * 3344546 * 2
def baseEnd_3344546 : Nat := 1717359669072376682093719

theorem tailTrace_3344546 : CollatzResearch.WordTrace tailWord_3344546 prefixEnd_3344546 1717359669072376682093719 := by
  unfold tailWord_3344546
  simp only [CollatzResearch.WordTrace]
  refine ⟨30496403535322129956529373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81323742760859013217411661 30496403535322129956529373)
  ·
    refine ⟨11436151325745798733698515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30496403535322129956529373 11436151325745798733698515)
    ·
      refine ⟨17154226988618698100547773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11436151325745798733698515 17154226988618698100547773)
      ·
        refine ⟨6432835120732011787705415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17154226988618698100547773 6432835120732011787705415)
        ·
          refine ⟨9649252681098017681558123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6432835120732011787705415 9649252681098017681558123)
          ·
            refine ⟨14473879021647026522337185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9649252681098017681558123 14473879021647026522337185)
            ·
              refine ⟨10855409266235269891752889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14473879021647026522337185 10855409266235269891752889)
              ·
                refine ⟨8141556949676452418814667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10855409266235269891752889 8141556949676452418814667)
                ·
                  refine ⟨12212335424514678628222001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8141556949676452418814667 12212335424514678628222001)
                  ·
                    refine ⟨9159251568386008971166501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12212335424514678628222001 9159251568386008971166501)
                    ·
                      refine ⟨1717359669072376682093719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9159251568386008971166501 1717359669072376682093719)
                      ·
                        rfl

theorem cell23_3344546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 2, 2, 1, 2, 4].length) (baseStart_3344546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3344546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3344546 prefixEnd_3344546 := by exact prefixLift 3344546
  have htrace : WordTrace (prefixWord ++ tailWord_3344546) baseStart_3344546 baseEnd_3344546 := by
    simpa [prefixWord, tailWord_3344546, baseEnd_3344546] using wordTrace_append hprefix tailTrace_3344546
  have hstable : (prefixWord ++ tailWord_3344546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3344546).length < 2 ^ (prefixWord ++ tailWord_3344546).sum := by decide
  have hdescent : baseEnd_3344546 < baseStart_3344546 := by decide
  rcases family_descends (prefixWord ++ tailWord_3344546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3344549 : List Nat := [1, 3, 1, 2, 1, 3, 1, 4, 1, 3, 3]
def baseStart_3344549 : Nat := 118140960795 + 3344549 * 2 ^ 59
def prefixEnd_3344549 : Nat := 4983230072969 + 3 ^ 40 * 3344549 * 2
def baseEnd_3344549 : Nat := 1717361209514340170356205

theorem tailTrace_3344549 : CollatzResearch.WordTrace tailWord_3344549 prefixEnd_3344549 1717361209514340170356205 := by
  unfold tailWord_3344549
  simp only [CollatzResearch.WordTrace]
  refine ⟨121985723560277651338476701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81323815706851767558984467 121985723560277651338476701)
  ·
    refine ⟨45744646335104119251928763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121985723560277651338476701 45744646335104119251928763)
    ·
      refine ⟨68616969502656178877893145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45744646335104119251928763 68616969502656178877893145)
      ·
        refine ⟨51462727126992134158419859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68616969502656178877893145 51462727126992134158419859)
        ·
          refine ⟨77194090690488201237629789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51462727126992134158419859 77194090690488201237629789)
          ·
            refine ⟨28947784008933075464111171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77194090690488201237629789 28947784008933075464111171)
            ·
              refine ⟨43421676013399613196166757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28947784008933075464111171 43421676013399613196166757)
              ·
                refine ⟨8141564252512427474281267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43421676013399613196166757 8141564252512427474281267)
                ·
                  refine ⟨12212346378768641211421901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8141564252512427474281267 12212346378768641211421901)
                  ·
                    refine ⟨4579629892038240454283213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12212346378768641211421901 4579629892038240454283213)
                    ·
                      refine ⟨1717361209514340170356205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4579629892038240454283213 1717361209514340170356205)
                      ·
                        rfl

theorem cell23_3344549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 4, 1, 3, 3].length) (baseStart_3344549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3344549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3344549 prefixEnd_3344549 := by exact prefixLift 3344549
  have htrace : WordTrace (prefixWord ++ tailWord_3344549) baseStart_3344549 baseEnd_3344549 := by
    simpa [prefixWord, tailWord_3344549, baseEnd_3344549] using wordTrace_append hprefix tailTrace_3344549
  have hstable : (prefixWord ++ tailWord_3344549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3344549).length < 2 ^ (prefixWord ++ tailWord_3344549).sum := by decide
  have hdescent : baseEnd_3344549 < baseStart_3344549 := by decide
  rcases family_descends (prefixWord ++ tailWord_3344549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3344592 : List Nat := [2, 1, 1, 1, 1, 2, 1, 1, 5, 3, 5]
def baseStart_3344592 : Nat := 118140960795 + 3344592 * 2 ^ 59
def prefixEnd_3344592 : Nat := 4983230072969 + 3 ^ 40 * 3344592 * 2
def baseEnd_3344592 : Nat := 1717383289182483502118507

theorem tailTrace_3344592 : CollatzResearch.WordTrace tailWord_3344592 prefixEnd_3344592 1717383289182483502118507 := by
  unfold tailWord_3344592
  simp only [CollatzResearch.WordTrace]
  refine ⟨60993645949560934841146015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81324861266081246454861353 60993645949560934841146015)
  ·
    refine ⟨91490468924341402261719023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60993645949560934841146015 91490468924341402261719023)
    ·
      refine ⟨137235703386512103392578535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91490468924341402261719023 137235703386512103392578535)
      ·
        refine ⟨205853555079768155088867803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137235703386512103392578535 205853555079768155088867803)
        ·
          refine ⟨308780332619652232633301705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 205853555079768155088867803 308780332619652232633301705)
          ·
            refine ⟨231585249464739174474976279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 308780332619652232633301705 231585249464739174474976279)
            ·
              refine ⟨347377874197108761712464419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 231585249464739174474976279 347377874197108761712464419)
              ·
                refine ⟨521066811295663142568696629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 347377874197108761712464419 521066811295663142568696629)
                ·
                  refine ⟨48850013558968419615815309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 521066811295663142568696629 48850013558968419615815309)
                  ·
                    refine ⟨18318755084613157355930741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 48850013558968419615815309 18318755084613157355930741)
                    ·
                      refine ⟨1717383289182483502118507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18318755084613157355930741 1717383289182483502118507)
                      ·
                        rfl

theorem cell23_3344592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 5, 3, 5].length) (baseStart_3344592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3344592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3344592 prefixEnd_3344592 := by exact prefixLift 3344592
  have htrace : WordTrace (prefixWord ++ tailWord_3344592) baseStart_3344592 baseEnd_3344592 := by
    simpa [prefixWord, tailWord_3344592, baseEnd_3344592] using wordTrace_append hprefix tailTrace_3344592
  have hstable : (prefixWord ++ tailWord_3344592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3344592).length < 2 ^ (prefixWord ++ tailWord_3344592).sum := by decide
  have hdescent : baseEnd_3344592 < baseStart_3344592 := by decide
  rcases family_descends (prefixWord ++ tailWord_3344592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3344609 : List Nat := [1, 2, 3, 1, 3, 1, 3, 1, 2, 1, 5]
def baseStart_3344609 : Nat := 118140960795 + 3344609 * 2 ^ 59
def prefixEnd_3344609 : Nat := 4983230072969 + 3 ^ 40 * 3344609 * 2
def baseEnd_3344609 : Nat := 1717392018353609935605929

theorem tailTrace_3344609 : CollatzResearch.WordTrace tailWord_3344609 prefixEnd_3344609 1717392018353609935605929 := by
  unfold tailWord_3344609
  simp only [CollatzResearch.WordTrace]
  refine ⟨121987911940060281585660881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81325274626706854390440587 121987911940060281585660881)
  ·
    refine ⟨91490933955045211189245661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121987911940060281585660881 91490933955045211189245661)
    ·
      refine ⟨34309100233141954195967123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91490933955045211189245661 34309100233141954195967123)
      ·
        refine ⟨51463650349712931293950685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34309100233141954195967123 51463650349712931293950685)
        ·
          refine ⟨19298868881142349235231507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51463650349712931293950685 19298868881142349235231507)
          ·
            refine ⟨28948303321713523852847261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19298868881142349235231507 28948303321713523852847261)
            ·
              refine ⟨10855613745642571444817723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28948303321713523852847261 10855613745642571444817723)
              ·
                refine ⟨16283420618463857167226585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10855613745642571444817723 16283420618463857167226585)
                ·
                  refine ⟨12212565463847892875419939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16283420618463857167226585 12212565463847892875419939)
                  ·
                    refine ⟨18318848195771839313129909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12212565463847892875419939 18318848195771839313129909)
                    ·
                      refine ⟨1717392018353609935605929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18318848195771839313129909 1717392018353609935605929)
                      ·
                        rfl

theorem cell23_3344609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 3, 1, 2, 1, 5].length) (baseStart_3344609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3344609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3344609 prefixEnd_3344609 := by exact prefixLift 3344609
  have htrace : WordTrace (prefixWord ++ tailWord_3344609) baseStart_3344609 baseEnd_3344609 := by
    simpa [prefixWord, tailWord_3344609, baseEnd_3344609] using wordTrace_append hprefix tailTrace_3344609
  have hstable : (prefixWord ++ tailWord_3344609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3344609).length < 2 ^ (prefixWord ++ tailWord_3344609).sum := by decide
  have hdescent : baseEnd_3344609 < baseStart_3344609 := by decide
  rcases family_descends (prefixWord ++ tailWord_3344609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3344623 : List Nat := [1, 1, 2, 1, 6, 1, 2, 1, 4, 2, 2]
def baseStart_3344623 : Nat := 118140960795 + 3344623 * 2 ^ 59
def prefixEnd_3344623 : Nat := 4983230072969 + 3 ^ 40 * 3344623 * 2
def baseEnd_3344623 : Nat := 1717399207082772880830865

theorem tailTrace_3344623 : CollatzResearch.WordTrace tailWord_3344623 prefixEnd_3344623 1717399207082772880830865 := by
  unfold tailWord_3344623
  simp only [CollatzResearch.WordTrace]
  refine ⟨121988422562009561976670523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81325615041339707984447015 121988422562009561976670523)
  ·
    refine ⟨182982633843014342965005785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121988422562009561976670523 182982633843014342965005785)
    ·
      refine ⟨137236975382260757223754339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182982633843014342965005785 137236975382260757223754339)
      ·
        refine ⟨205855463073391135835631509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137236975382260757223754339 205855463073391135835631509)
        ·
          refine ⟨9649474831565209492295227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 205855463073391135835631509 9649474831565209492295227)
          ·
            refine ⟨14474212247347814238442841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9649474831565209492295227 14474212247347814238442841)
            ·
              refine ⟨10855659185510860678832131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14474212247347814238442841 10855659185510860678832131)
              ·
                refine ⟨16283488778266291018248197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10855659185510860678832131 16283488778266291018248197)
                ·
                  refine ⟨3053154145924929565921537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16283488778266291018248197 3053154145924929565921537)
                  ·
                    refine ⟨2289865609443697174441153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3053154145924929565921537 2289865609443697174441153)
                    ·
                      refine ⟨1717399207082772880830865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2289865609443697174441153 1717399207082772880830865)
                      ·
                        rfl

theorem cell23_3344623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 2, 1, 4, 2, 2].length) (baseStart_3344623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3344623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3344623 prefixEnd_3344623 := by exact prefixLift 3344623
  have htrace : WordTrace (prefixWord ++ tailWord_3344623) baseStart_3344623 baseEnd_3344623 := by
    simpa [prefixWord, tailWord_3344623, baseEnd_3344623] using wordTrace_append hprefix tailTrace_3344623
  have hstable : (prefixWord ++ tailWord_3344623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3344623).length < 2 ^ (prefixWord ++ tailWord_3344623).sum := by decide
  have hdescent : baseEnd_3344623 < baseStart_3344623 := by decide
  rcases family_descends (prefixWord ++ tailWord_3344623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3344639 : List Nat := [1, 1, 2, 2, 1, 4, 2, 1, 1, 5, 3]
def baseStart_3344639 : Nat := 118140960795 + 3344639 * 2 ^ 59
def prefixEnd_3344639 : Nat := 4983230072969 + 3 ^ 40 * 3344639 * 2
def baseEnd_3344639 : Nat := 1717407422773244818230791

theorem tailTrace_3344639 : CollatzResearch.WordTrace tailWord_3344639 prefixEnd_3344639 1717407422773244818230791 := by
  unfold tailWord_3344639
  simp only [CollatzResearch.WordTrace]
  refine ⟨121989006129951596709252971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81326004086634397806168647 121989006129951596709252971)
  ·
    refine ⟨182983509194927395063879457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121989006129951596709252971 182983509194927395063879457)
    ·
      refine ⟨137237631896195546297909593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182983509194927395063879457 137237631896195546297909593)
      ·
        refine ⟨102928223922146659723432195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137237631896195546297909593 102928223922146659723432195)
        ·
          refine ⟨154392335883219989585148293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102928223922146659723432195 154392335883219989585148293)
          ·
            refine ⟨28948562978103748047215305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 154392335883219989585148293 28948562978103748047215305)
            ·
              refine ⟨21711422233577811035411479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28948562978103748047215305 21711422233577811035411479)
              ·
                refine ⟨32567133350366716553117219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21711422233577811035411479 32567133350366716553117219)
                ·
                  refine ⟨48850700025550074829675829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32567133350366716553117219 48850700025550074829675829)
                  ·
                    refine ⟨4579753127395319515282109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 48850700025550074829675829 4579753127395319515282109)
                    ·
                      refine ⟨1717407422773244818230791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4579753127395319515282109 1717407422773244818230791)
                      ·
                        rfl

theorem cell23_3344639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 1, 1, 5, 3].length) (baseStart_3344639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3344639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3344639 prefixEnd_3344639 := by exact prefixLift 3344639
  have htrace : WordTrace (prefixWord ++ tailWord_3344639) baseStart_3344639 baseEnd_3344639 := by
    simpa [prefixWord, tailWord_3344639, baseEnd_3344639] using wordTrace_append hprefix tailTrace_3344639
  have hstable : (prefixWord ++ tailWord_3344639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3344639).length < 2 ^ (prefixWord ++ tailWord_3344639).sum := by decide
  have hdescent : baseEnd_3344639 < baseStart_3344639 := by decide
  rcases family_descends (prefixWord ++ tailWord_3344639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3344640 : List Nat := [2, 1, 1, 2, 1, 1, 8, 1, 2, 2, 2]
def baseStart_3344640 : Nat := 118140960795 + 3344640 * 2 ^ 59
def prefixEnd_3344640 : Nat := 4983230072969 + 3 ^ 40 * 3344640 * 2
def baseEnd_3344640 : Nat := 1717407936253899314318287

theorem tailTrace_3344640 : CollatzResearch.WordTrace tailWord_3344640 prefixEnd_3344640 1717407936253899314318287 := by
  unfold tailWord_3344640
  simp only [CollatzResearch.WordTrace]
  refine ⟨60994521301473986940019687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81326028401965315920026249 60994521301473986940019687)
  ·
    refine ⟨91491781952210980410029531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60994521301473986940019687 91491781952210980410029531)
    ·
      refine ⟨137237672928316470615044297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91491781952210980410029531 137237672928316470615044297)
      ·
        refine ⟨102928254696237352961283223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137237672928316470615044297 102928254696237352961283223)
        ·
          refine ⟨154392382044356029441924835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102928254696237352961283223 154392382044356029441924835)
          ·
            refine ⟨231588573066534044162887253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154392382044356029441924835 231588573066534044162887253)
            ·
              refine ⟨2713928590623445830033835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 231588573066534044162887253 2713928590623445830033835)
              ·
                refine ⟨4070892885935168745050753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2713928590623445830033835 4070892885935168745050753)
                ·
                  refine ⟨3053169664451376558788065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4070892885935168745050753 3053169664451376558788065)
                  ·
                    refine ⟨2289877248338532419091049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3053169664451376558788065 2289877248338532419091049)
                    ·
                      refine ⟨1717407936253899314318287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2289877248338532419091049 1717407936253899314318287)
                      ·
                        rfl

theorem cell23_3344640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 8, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 8, 1, 2, 2, 2].length) (baseStart_3344640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3344640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3344640 prefixEnd_3344640 := by exact prefixLift 3344640
  have htrace : WordTrace (prefixWord ++ tailWord_3344640) baseStart_3344640 baseEnd_3344640 := by
    simpa [prefixWord, tailWord_3344640, baseEnd_3344640] using wordTrace_append hprefix tailTrace_3344640
  have hstable : (prefixWord ++ tailWord_3344640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3344640).length < 2 ^ (prefixWord ++ tailWord_3344640).sum := by decide
  have hdescent : baseEnd_3344640 < baseStart_3344640 := by decide
  rcases family_descends (prefixWord ++ tailWord_3344640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3344676 : List Nat := [2, 3, 1, 3, 1, 2, 2, 2, 2, 5]
def baseStart_3344676 : Nat := 118140960795 + 3344676 * 2 ^ 59
def prefixEnd_3344676 : Nat := 4983230072969 + 3 ^ 40 * 3344676 * 2
def baseEnd_3344676 : Nat := 572475473852487057822707

theorem tailTrace_3344676 : CollatzResearch.WordTrace tailWord_3344676 prefixEnd_3344676 572475473852487057822707 := by
  unfold tailWord_3344676
  simp only [CollatzResearch.WordTrace]
  refine ⟨60995177815408776014174941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81326903753878368018899921 60995177815408776014174941)
  ·
    refine ⟨22873191680778291005315603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60995177815408776014174941 22873191680778291005315603)
    ·
      refine ⟨34309787521167436507973405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22873191680778291005315603 34309787521167436507973405)
      ·
        refine ⟨12866170320437788690490027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34309787521167436507973405 12866170320437788690490027)
        ·
          refine ⟨19299255480656683035735041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12866170320437788690490027 19299255480656683035735041)
          ·
            refine ⟨14474441610492512276801281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19299255480656683035735041 14474441610492512276801281)
            ·
              refine ⟨10855831207869384207600961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14474441610492512276801281 10855831207869384207600961)
              ·
                refine ⟨8141873405902038155700721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10855831207869384207600961 8141873405902038155700721)
                ·
                  refine ⟨6106405054426528616775541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8141873405902038155700721 6106405054426528616775541)
                  ·
                    refine ⟨572475473852487057822707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6106405054426528616775541 572475473852487057822707)
                    ·
                      rfl

theorem cell23_3344676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 2, 2, 2, 5].length) (baseStart_3344676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3344676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3344676 prefixEnd_3344676 := by exact prefixLift 3344676
  have htrace : WordTrace (prefixWord ++ tailWord_3344676) baseStart_3344676 baseEnd_3344676 := by
    simpa [prefixWord, tailWord_3344676, baseEnd_3344676] using wordTrace_append hprefix tailTrace_3344676
  have hstable : (prefixWord ++ tailWord_3344676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3344676).length < 2 ^ (prefixWord ++ tailWord_3344676).sum := by decide
  have hdescent : baseEnd_3344676 < baseStart_3344676 := by decide
  rcases family_descends (prefixWord ++ tailWord_3344676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3344696 : List Nat := [2, 1, 2, 1, 3, 1, 3, 1, 1, 6, 2]
def baseStart_3344696 : Nat := 118140960795 + 3344696 * 2 ^ 59
def prefixEnd_3344696 : Nat := 4983230072969 + 3 ^ 40 * 3344696 * 2
def baseEnd_3344696 : Nat := 1717436691170551095218029

theorem tailTrace_3344696 : CollatzResearch.WordTrace tailWord_3344696 prefixEnd_3344696 1717436691170551095218029 := by
  unfold tailWord_3344696
  simp only [CollatzResearch.WordTrace]
  refine ⟨60995542545372547722038971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81327390060496730296051961 60995542545372547722038971)
  ·
    refine ⟨91493313818058821583058457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60995542545372547722038971 91493313818058821583058457)
    ·
      refine ⟨68619985363544116187293843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91493313818058821583058457 68619985363544116187293843)
      ·
        refine ⟨102929978045316174280940765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68619985363544116187293843 102929978045316174280940765)
        ·
          refine ⟨38598741766993565355352787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102929978045316174280940765 38598741766993565355352787)
          ·
            refine ⟨57898112650490348033029181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38598741766993565355352787 57898112650490348033029181)
            ·
              refine ⟨21711792243933880512385943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57898112650490348033029181 21711792243933880512385943)
              ·
                refine ⟨32567688365900820768578915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21711792243933880512385943 32567688365900820768578915)
                ·
                  refine ⟨48851532548851231152868373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32567688365900820768578915 48851532548851231152868373)
                  ·
                    refine ⟨2289915588227401460290705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 48851532548851231152868373 2289915588227401460290705)
                    ·
                      refine ⟨1717436691170551095218029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2289915588227401460290705 1717436691170551095218029)
                      ·
                        rfl

theorem cell23_3344696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 1, 1, 6, 2].length) (baseStart_3344696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3344696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3344696 prefixEnd_3344696 := by exact prefixLift 3344696
  have htrace : WordTrace (prefixWord ++ tailWord_3344696) baseStart_3344696 baseEnd_3344696 := by
    simpa [prefixWord, tailWord_3344696, baseEnd_3344696] using wordTrace_append hprefix tailTrace_3344696
  have hstable : (prefixWord ++ tailWord_3344696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3344696).length < 2 ^ (prefixWord ++ tailWord_3344696).sum := by decide
  have hdescent : baseEnd_3344696 < baseStart_3344696 := by decide
  rcases family_descends (prefixWord ++ tailWord_3344696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3344716 : List Nat := [2, 2, 1, 3, 2, 1, 3, 1, 1, 4, 3]
def baseStart_3344716 : Nat := 118140960795 + 3344716 * 2 ^ 59
def prefixEnd_3344716 : Nat := 4983230072969 + 3 ^ 40 * 3344716 * 2
def baseEnd_3344716 : Nat := 1717446960783641016967937

theorem tailTrace_3344716 : CollatzResearch.WordTrace tailWord_3344716 prefixEnd_3344716 1717446960783641016967937 := by
  unfold tailWord_3344716
  simp only [CollatzResearch.WordTrace]
  refine ⟨60995907275336319429903001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81327876367115092573204001 60995907275336319429903001)
  ·
    refine ⟨45746930456502239572427251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60995907275336319429903001 45746930456502239572427251)
    ·
      refine ⟨68620395684753359358640877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45746930456502239572427251 68620395684753359358640877)
      ·
        refine ⟨25732648381782509759490329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68620395684753359358640877 25732648381782509759490329)
        ·
          refine ⟨19299486286336882319617747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25732648381782509759490329 19299486286336882319617747)
          ·
            refine ⟨28949229429505323479426621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19299486286336882319617747 28949229429505323479426621)
            ·
              refine ⟨10855961036064496304784983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28949229429505323479426621 10855961036064496304784983)
              ·
                refine ⟨16283941554096744457177475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10855961036064496304784983 16283941554096744457177475)
                ·
                  refine ⟨24425912331145116685766213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16283941554096744457177475 24425912331145116685766213)
                  ·
                    refine ⟨4579858562089709378581165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24425912331145116685766213 4579858562089709378581165)
                    ·
                      refine ⟨1717446960783641016967937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4579858562089709378581165 1717446960783641016967937)
                      ·
                        rfl

theorem cell23_3344716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 3, 1, 1, 4, 3].length) (baseStart_3344716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3344716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3344716 prefixEnd_3344716 := by exact prefixLift 3344716
  have htrace : WordTrace (prefixWord ++ tailWord_3344716) baseStart_3344716 baseEnd_3344716 := by
    simpa [prefixWord, tailWord_3344716, baseEnd_3344716] using wordTrace_append hprefix tailTrace_3344716
  have hstable : (prefixWord ++ tailWord_3344716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3344716).length < 2 ^ (prefixWord ++ tailWord_3344716).sum := by decide
  have hdescent : baseEnd_3344716 < baseStart_3344716 := by decide
  rcases family_descends (prefixWord ++ tailWord_3344716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3344736 : List Nat := [2, 1, 1, 3, 5, 1, 1, 1, 8]
def baseStart_3344736 : Nat := 118140960795 + 3344736 * 2 ^ 59
def prefixEnd_3344736 : Nat := 4983230072969 + 3 ^ 40 * 3344736 * 2
def baseEnd_3344736 : Nat := 190828581155192326524205

theorem tailTrace_3344736 : CollatzResearch.WordTrace tailWord_3344736 prefixEnd_3344736 190828581155192326524205 := by
  unfold tailWord_3344736
  simp only [CollatzResearch.WordTrace]
  refine ⟨60996272005300091137767031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81328362673733454850356041 60996272005300091137767031)
  ·
    refine ⟨91494408007950136706650547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60996272005300091137767031 91494408007950136706650547)
    ·
      refine ⟨137241612011925205059975821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91494408007950136706650547 137241612011925205059975821)
      ·
        refine ⟨51465604504471951897490933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 137241612011925205059975821 51465604504471951897490933)
        ·
          refine ⟨4824900422294245490389775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 51465604504471951897490933 4824900422294245490389775)
          ·
            refine ⟨7237350633441368235584663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4824900422294245490389775 7237350633441368235584663)
            ·
              refine ⟨10856025950162052353376995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7237350633441368235584663 10856025950162052353376995)
              ·
                refine ⟨16284038925243078530065493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10856025950162052353376995 16284038925243078530065493)
                ·
                  refine ⟨190828581155192326524205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 16284038925243078530065493 190828581155192326524205)
                  ·
                    rfl

theorem cell23_3344736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 1, 1, 8].length) (baseStart_3344736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3344736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3344736 prefixEnd_3344736 := by exact prefixLift 3344736
  have htrace : WordTrace (prefixWord ++ tailWord_3344736) baseStart_3344736 baseEnd_3344736 := by
    simpa [prefixWord, tailWord_3344736, baseEnd_3344736] using wordTrace_append hprefix tailTrace_3344736
  have hstable : (prefixWord ++ tailWord_3344736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3344736).length < 2 ^ (prefixWord ++ tailWord_3344736).sum := by decide
  have hdescent : baseEnd_3344736 < baseStart_3344736 := by decide
  rcases family_descends (prefixWord ++ tailWord_3344736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3344739 : List Nat := [1, 1, 1, 5, 2, 1, 1, 1, 1, 1, 8]
def baseStart_3344739 : Nat := 118140960795 + 3344739 * 2 ^ 59
def prefixEnd_3344739 : Nat := 4983230072969 + 3 ^ 40 * 3344739 * 2
def baseEnd_3344739 : Nat := 1717458770838694426980331

theorem tailTrace_3344739 : CollatzResearch.WordTrace tailWord_3344739 prefixEnd_3344739 1717458770838694426980331 := by
  unfold tailWord_3344739
  simp only [CollatzResearch.WordTrace]
  refine ⟨121992653429589313787893271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81328435619726209191928847 121992653429589313787893271)
  ·
    refine ⟨182988980144383970681839907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121992653429589313787893271 182988980144383970681839907)
    ·
      refine ⟨274483470216575956022759861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182988980144383970681839907 274483470216575956022759861)
      ·
        refine ⟨25732825332803995877133737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 274483470216575956022759861 25732825332803995877133737)
        ·
          refine ⟨19299618999602996907850303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25732825332803995877133737 19299618999602996907850303)
          ·
            refine ⟨28949428499404495361775455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19299618999602996907850303 28949428499404495361775455)
            ·
              refine ⟨43424142749106743042663183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28949428499404495361775455 43424142749106743042663183)
              ·
                refine ⟨65136214123660114563994775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43424142749106743042663183 65136214123660114563994775)
                ·
                  refine ⟨97704321185490171845992163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65136214123660114563994775 97704321185490171845992163)
                  ·
                    refine ⟨146556481778235257768988245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 97704321185490171845992163 146556481778235257768988245)
                    ·
                      refine ⟨1717458770838694426980331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 146556481778235257768988245 1717458770838694426980331)
                      ·
                        rfl

theorem cell23_3344739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 1, 1, 1, 8].length) (baseStart_3344739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3344739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3344739 prefixEnd_3344739 := by exact prefixLift 3344739
  have htrace : WordTrace (prefixWord ++ tailWord_3344739) baseStart_3344739 baseEnd_3344739 := by
    simpa [prefixWord, tailWord_3344739, baseEnd_3344739] using wordTrace_append hprefix tailTrace_3344739
  have hstable : (prefixWord ++ tailWord_3344739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3344739).length < 2 ^ (prefixWord ++ tailWord_3344739).sum := by decide
  have hdescent : baseEnd_3344739 < baseStart_3344739 := by decide
  rcases family_descends (prefixWord ++ tailWord_3344739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3344763 : List Nat := [1, 1, 1, 1, 1, 7, 2, 2, 3, 1, 3]
def baseStart_3344763 : Nat := 118140960795 + 3344763 * 2 ^ 59
def prefixEnd_3344763 : Nat := 4983230072969 + 3 ^ 40 * 3344763 * 2
def baseEnd_3344763 : Nat := 1717471094374402333080221

theorem tailTrace_3344763 : CollatzResearch.WordTrace tailWord_3344763 prefixEnd_3344763 1717471094374402333080221 := by
  unfold tailWord_3344763
  simp only [CollatzResearch.WordTrace]
  refine ⟨121993528781502365886766943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81329019187668243924511295 121993528781502365886766943)
  ·
    refine ⟨182990293172253548830150415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121993528781502365886766943 182990293172253548830150415)
    ·
      refine ⟨274485439758380323245225623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182990293172253548830150415 274485439758380323245225623)
      ·
        refine ⟨411728159637570484867838435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 274485439758380323245225623 411728159637570484867838435)
        ·
          refine ⟨617592239456355727301757653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 411728159637570484867838435 617592239456355727301757653)
          ·
            refine ⟨14474818112258337358634945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 617592239456355727301757653 14474818112258337358634945)
            ·
              refine ⟨10856113584193753018976209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14474818112258337358634945 10856113584193753018976209)
              ·
                refine ⟨8142085188145314764232157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10856113584193753018976209 8142085188145314764232157)
                ·
                  refine ⟨3053281945554493036587059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8142085188145314764232157 3053281945554493036587059)
                  ·
                    refine ⟨4579922918331739554880589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3053281945554493036587059 4579922918331739554880589)
                    ·
                      refine ⟨1717471094374402333080221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4579922918331739554880589 1717471094374402333080221)
                      ·
                        rfl

theorem cell23_3344763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 2, 2, 3, 1, 3].length) (baseStart_3344763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3344763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3344763 prefixEnd_3344763 := by exact prefixLift 3344763
  have htrace : WordTrace (prefixWord ++ tailWord_3344763) baseStart_3344763 baseEnd_3344763 := by
    simpa [prefixWord, tailWord_3344763, baseEnd_3344763] using wordTrace_append hprefix tailTrace_3344763
  have hstable : (prefixWord ++ tailWord_3344763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3344763).length < 2 ^ (prefixWord ++ tailWord_3344763).sum := by decide
  have hdescent : baseEnd_3344763 < baseStart_3344763 := by decide
  rcases family_descends (prefixWord ++ tailWord_3344763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3344773 : List Nat := [1, 3, 1, 1, 3, 1, 1, 5, 2, 3, 2]
def baseStart_3344773 : Nat := 118140960795 + 3344773 * 2 ^ 59
def prefixEnd_3344773 : Nat := 4983230072969 + 3 ^ 40 * 3344773 * 2
def baseEnd_3344773 : Nat := 1717476229180947293955175

theorem tailTrace_3344773 : CollatzResearch.WordTrace tailWord_3344773 prefixEnd_3344773 1717476229180947293955175 := by
  unfold tailWord_3344773
  simp only [CollatzResearch.WordTrace]
  refine ⟨121993893511466137594630973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81329262340977425063087315 121993893511466137594630973)
  ·
    refine ⟨45747710066799801597986615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121993893511466137594630973 45747710066799801597986615)
    ·
      refine ⟨68621565100199702396979923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45747710066799801597986615 68621565100199702396979923)
      ·
        refine ⟨102932347650299553595469885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68621565100199702396979923 102932347650299553595469885)
        ·
          refine ⟨38599630368862332598301207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102932347650299553595469885 38599630368862332598301207)
          ·
            refine ⟨57899445553293498897451811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38599630368862332598301207 57899445553293498897451811)
            ·
              refine ⟨86849168329940248346177717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57899445553293498897451811 86849168329940248346177717)
              ·
                refine ⟨8142109530931898282454161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 86849168329940248346177717 8142109530931898282454161)
                ·
                  refine ⟨6106582148198923711840621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8142109530931898282454161 6106582148198923711840621)
                  ·
                    refine ⟨2289968305574596391940233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6106582148198923711840621 2289968305574596391940233)
                    ·
                      refine ⟨1717476229180947293955175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2289968305574596391940233 1717476229180947293955175)
                      ·
                        rfl

theorem cell23_3344773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 5, 2, 3, 2].length) (baseStart_3344773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3344773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3344773 prefixEnd_3344773 := by exact prefixLift 3344773
  have htrace : WordTrace (prefixWord ++ tailWord_3344773) baseStart_3344773 baseEnd_3344773 := by
    simpa [prefixWord, tailWord_3344773, baseEnd_3344773] using wordTrace_append hprefix tailTrace_3344773
  have hstable : (prefixWord ++ tailWord_3344773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3344773).length < 2 ^ (prefixWord ++ tailWord_3344773).sum := by decide
  have hdescent : baseEnd_3344773 < baseStart_3344773 := by decide
  rcases family_descends (prefixWord ++ tailWord_3344773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3344797 : List Nat := [1, 4, 2, 1, 4, 2, 1, 1, 3, 1, 3]
def baseStart_3344797 : Nat := 118140960795 + 3344797 * 2 ^ 59
def prefixEnd_3344797 : Nat := 4983230072969 + 3 ^ 40 * 3344797 * 2
def baseEnd_3344797 : Nat := 1717488552716655200055065

theorem tailTrace_3344797 : CollatzResearch.WordTrace tailWord_3344797 prefixEnd_3344797 1717488552716655200055065 := by
  unfold tailWord_3344797
  simp only [CollatzResearch.WordTrace]
  refine ⟨121994768863379189693504645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81329845908919459795669763 121994768863379189693504645)
  ·
    refine ⟨22874019161883598067532121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 121994768863379189693504645 22874019161883598067532121)
    ·
      refine ⟨17155514371412698550649091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22874019161883598067532121 17155514371412698550649091)
      ·
        refine ⟨25733271557119047825973637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17155514371412698550649091 25733271557119047825973637)
        ·
          refine ⟨4824988416959821467370057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25733271557119047825973637 4824988416959821467370057)
          ·
            refine ⟨3618741312719866100527543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4824988416959821467370057 3618741312719866100527543)
            ·
              refine ⟨5428111969079799150791315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3618741312719866100527543 5428111969079799150791315)
              ·
                refine ⟨8142167953619698726186973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5428111969079799150791315 8142167953619698726186973)
                ·
                  refine ⟨3053312982607387022320115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8142167953619698726186973 3053312982607387022320115)
                  ·
                    refine ⟨4579969473911080533480173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3053312982607387022320115 4579969473911080533480173)
                    ·
                      refine ⟨1717488552716655200055065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4579969473911080533480173 1717488552716655200055065)
                      ·
                        rfl

theorem cell23_3344797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 2, 1, 1, 3, 1, 3].length) (baseStart_3344797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3344797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3344797 prefixEnd_3344797 := by exact prefixLift 3344797
  have htrace : WordTrace (prefixWord ++ tailWord_3344797) baseStart_3344797 baseEnd_3344797 := by
    simpa [prefixWord, tailWord_3344797, baseEnd_3344797] using wordTrace_append hprefix tailTrace_3344797
  have hstable : (prefixWord ++ tailWord_3344797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3344797).length < 2 ^ (prefixWord ++ tailWord_3344797).sum := by decide
  have hdescent : baseEnd_3344797 < baseStart_3344797 := by decide
  rcases family_descends (prefixWord ++ tailWord_3344797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3344823 : List Nat := [1, 1, 3, 1, 3, 4, 1, 1, 3, 2, 3]
def baseStart_3344823 : Nat := 118140960795 + 3344823 * 2 ^ 59
def prefixEnd_3344823 : Nat := 4983230072969 + 3 ^ 40 * 3344823 * 2
def baseEnd_3344823 : Nat := 1717501903213672098329945

theorem tailTrace_3344823 : CollatzResearch.WordTrace tailWord_3344823 prefixEnd_3344823 1717501903213672098329945 := by
  unfold tailWord_3344823
  simp only [CollatzResearch.WordTrace]
  refine ⟨121995717161284996133951123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81330478107523330755967415 121995717161284996133951123)
  ·
    refine ⟨182993575741927494200926685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121995717161284996133951123 182993575741927494200926685)
    ·
      refine ⟨68622590903222810325347507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 182993575741927494200926685 68622590903222810325347507)
      ·
        refine ⟨102933886354834215488021261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68622590903222810325347507 102933886354834215488021261)
        ·
          refine ⟨38600207383062830808007973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102933886354834215488021261 38600207383062830808007973)
          ·
            refine ⟨7237538884324280776501495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38600207383062830808007973 7237538884324280776501495)
            ·
              refine ⟨10856308326486421164752243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7237538884324280776501495 10856308326486421164752243)
              ·
                refine ⟨16284462489729631747128365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10856308326486421164752243 16284462489729631747128365)
                ·
                  refine ⟨6106673433648611905173137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16284462489729631747128365 6106673433648611905173137)
                  ·
                    refine ⟨4580005075236458928879853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6106673433648611905173137 4580005075236458928879853)
                    ·
                      refine ⟨1717501903213672098329945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4580005075236458928879853 1717501903213672098329945)
                      ·
                        rfl

theorem cell23_3344823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 1, 1, 3, 2, 3].length) (baseStart_3344823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3344823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3344823 prefixEnd_3344823 := by exact prefixLift 3344823
  have htrace : WordTrace (prefixWord ++ tailWord_3344823) baseStart_3344823 baseEnd_3344823 := by
    simpa [prefixWord, tailWord_3344823, baseEnd_3344823] using wordTrace_append hprefix tailTrace_3344823
  have hstable : (prefixWord ++ tailWord_3344823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3344823).length < 2 ^ (prefixWord ++ tailWord_3344823).sum := by decide
  have hdescent : baseEnd_3344823 < baseStart_3344823 := by decide
  rcases family_descends (prefixWord ++ tailWord_3344823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3344876 : List Nat := [2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 4]
def baseStart_3344876 : Nat := 118140960795 + 3344876 * 2 ^ 59
def prefixEnd_3344876 : Nat := 4983230072969 + 3 ^ 40 * 3344876 * 2
def baseEnd_3344876 : Nat := 1717529117688360390967201

theorem tailTrace_3344876 : CollatzResearch.WordTrace tailWord_3344876 prefixEnd_3344876 1717529117688360390967201 := by
  unfold tailWord_3344876
  simp only [CollatzResearch.WordTrace]
  refine ⟨60998825115046493092815241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81331766820061990790420321 60998825115046493092815241)
  ·
    refine ⟨45749118836284869819611431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60998825115046493092815241 45749118836284869819611431)
    ·
      refine ⟨68623678254427304729417147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45749118836284869819611431 68623678254427304729417147)
      ·
        refine ⟨102935517381640957094125721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68623678254427304729417147 102935517381640957094125721)
        ·
          refine ⟨77201638036230717820594291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102935517381640957094125721 77201638036230717820594291)
          ·
            refine ⟨115802457054346076730891437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77201638036230717820594291 115802457054346076730891437)
            ·
              refine ⟨43425921395379778774084289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 115802457054346076730891437 43425921395379778774084289)
              ·
                refine ⟨32569441046534834080563217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43425921395379778774084289 32569441046534834080563217)
                ·
                  refine ⟨24427080784901125560422413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32569441046534834080563217 24427080784901125560422413)
                  ·
                    refine ⟨9160155294337922085158405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24427080784901125560422413 9160155294337922085158405)
                    ·
                      refine ⟨1717529117688360390967201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9160155294337922085158405 1717529117688360390967201)
                      ·
                        rfl

theorem cell23_3344876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 4].length) (baseStart_3344876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3344876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3344876 prefixEnd_3344876 := by exact prefixLift 3344876
  have htrace : WordTrace (prefixWord ++ tailWord_3344876) baseStart_3344876 baseEnd_3344876 := by
    simpa [prefixWord, tailWord_3344876, baseEnd_3344876] using wordTrace_append hprefix tailTrace_3344876
  have hstable : (prefixWord ++ tailWord_3344876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3344876).length < 2 ^ (prefixWord ++ tailWord_3344876).sum := by decide
  have hdescent : baseEnd_3344876 < baseStart_3344876 := by decide
  rcases family_descends (prefixWord ++ tailWord_3344876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3344880 : List Nat := [2, 1, 1, 1, 3, 3, 2, 4, 1, 3, 2]
def baseStart_3344880 : Nat := 118140960795 + 3344880 * 2 ^ 59
def prefixEnd_3344880 : Nat := 4983230072969 + 3 ^ 40 * 3344880 * 2
def baseEnd_3344880 : Nat := 1717531171610978375317183

theorem tailTrace_3344880 : CollatzResearch.WordTrace tailWord_3344880 prefixEnd_3344880 1717531171610978375317183 := by
  unfold tailWord_3344880
  simp only [CollatzResearch.WordTrace]
  refine ⟨60998898061039247434388047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81331864081385663245850729 60998898061039247434388047)
  ·
    refine ⟨91498347091558871151582071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60998898061039247434388047 91498347091558871151582071)
    ·
      refine ⟨137247520637338306727373107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91498347091558871151582071 137247520637338306727373107)
      ·
        refine ⟨205871280956007460091059661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137247520637338306727373107 205871280956007460091059661)
        ·
          refine ⟨77201730358502797534147373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 205871280956007460091059661 77201730358502797534147373)
          ·
            refine ⟨28950648884438549075305265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77201730358502797534147373 28950648884438549075305265)
            ·
              refine ⟨21712986663328911806478949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28950648884438549075305265 21712986663328911806478949)
              ·
                refine ⟨4071184999374170963714803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21712986663328911806478949 4071184999374170963714803)
                ·
                  refine ⟨6106777499061256445572205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4071184999374170963714803 6106777499061256445572205)
                  ·
                    refine ⟨2290041562147971167089577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6106777499061256445572205 2290041562147971167089577)
                    ·
                      refine ⟨1717531171610978375317183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2290041562147971167089577 1717531171610978375317183)
                      ·
                        rfl

theorem cell23_3344880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 4, 1, 3, 2].length) (baseStart_3344880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3344880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3344880 prefixEnd_3344880 := by exact prefixLift 3344880
  have htrace : WordTrace (prefixWord ++ tailWord_3344880) baseStart_3344880 baseEnd_3344880 := by
    simpa [prefixWord, tailWord_3344880, baseEnd_3344880] using wordTrace_append hprefix tailTrace_3344880
  have hstable : (prefixWord ++ tailWord_3344880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3344880).length < 2 ^ (prefixWord ++ tailWord_3344880).sum := by decide
  have hdescent : baseEnd_3344880 < baseStart_3344880 := by decide
  rcases family_descends (prefixWord ++ tailWord_3344880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3344897 : List Nat := [1, 2, 4, 1, 3, 2, 1, 3, 1, 3, 2]
def baseStart_3344897 : Nat := 118140960795 + 3344897 * 2 ^ 59
def prefixEnd_3344897 : Nat := 4983230072969 + 3 ^ 40 * 3344897 * 2
def baseEnd_3344897 : Nat := 1717539900782104808804605

theorem tailTrace_3344897 : CollatzResearch.WordTrace tailWord_3344897 prefixEnd_3344897 1717539900782104808804605 := by
  unfold tailWord_3344897
  simp only [CollatzResearch.WordTrace]
  refine ⟨121998416163016906772144945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81332277442011271181429963 121998416163016906772144945)
  ·
    refine ⟨91498812122262680079108709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121998416163016906772144945 91498812122262680079108709)
    ·
      refine ⟨17156027272924252514832883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 91498812122262680079108709 17156027272924252514832883)
      ·
        refine ⟨25734040909386378772249325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17156027272924252514832883 25734040909386378772249325)
        ·
          refine ⟨9650265341019892039593497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25734040909386378772249325 9650265341019892039593497)
          ·
            refine ⟨7237699005764919029695123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9650265341019892039593497 7237699005764919029695123)
            ·
              refine ⟨10856548508647378544542685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7237699005764919029695123 10856548508647378544542685)
              ·
                refine ⟨4071205690742766954203507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10856548508647378544542685 4071205690742766954203507)
                ·
                  refine ⟨6106808536114150431305261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4071205690742766954203507 6106808536114150431305261)
                  ·
                    refine ⟨2290053201042806411739473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6106808536114150431305261 2290053201042806411739473)
                    ·
                      refine ⟨1717539900782104808804605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2290053201042806411739473 1717539900782104808804605)
                      ·
                        rfl

theorem cell23_3344897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 1, 3, 1, 3, 2].length) (baseStart_3344897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3344897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3344897 prefixEnd_3344897 := by exact prefixLift 3344897
  have htrace : WordTrace (prefixWord ++ tailWord_3344897) baseStart_3344897 baseEnd_3344897 := by
    simpa [prefixWord, tailWord_3344897, baseEnd_3344897] using wordTrace_append hprefix tailTrace_3344897
  have hstable : (prefixWord ++ tailWord_3344897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3344897).length < 2 ^ (prefixWord ++ tailWord_3344897).sum := by decide
  have hdescent : baseEnd_3344897 < baseStart_3344897 := by decide
  rcases family_descends (prefixWord ++ tailWord_3344897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3344967 : List Nat := [1, 1, 4, 1, 4, 2, 3, 2, 5]
def baseStart_3344967 : Nat := 118140960795 + 3344967 * 2 ^ 59
def prefixEnd_3344967 : Nat := 4983230072969 + 3 ^ 40 * 3344967 * 2
def baseEnd_3344967 : Nat := 190841760491991059436587

theorem tailTrace_3344967 : CollatzResearch.WordTrace tailWord_3344967 prefixEnd_3344967 190841760491991059436587 := by
  unfold tailWord_3344967
  simp only [CollatzResearch.WordTrace]
  refine ⟨122000969272763308727193155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81333979515175539151462103 122000969272763308727193155)
  ·
    refine ⟨183001453909144963090789733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122000969272763308727193155 183001453909144963090789733)
    ·
      refine ⟨34312772607964680579523075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 183001453909144963090789733 34312772607964680579523075)
      ·
        refine ⟨51469158911947020869284613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34312772607964680579523075 51469158911947020869284613)
        ·
          refine ⟨9650467295990066412990865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51469158911947020869284613 9650467295990066412990865)
          ·
            refine ⟨7237850471992549809743149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9650467295990066412990865 7237850471992549809743149)
            ·
              refine ⟨2714193926997206178653681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7237850471992549809743149 2714193926997206178653681)
              ·
                refine ⟨2035645445247904633990261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2714193926997206178653681 2035645445247904633990261)
                ·
                  refine ⟨190841760491991059436587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2035645445247904633990261 190841760491991059436587)
                  ·
                    rfl

theorem cell23_3344967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 3, 2, 5].length) (baseStart_3344967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3344967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3344967 prefixEnd_3344967 := by exact prefixLift 3344967
  have htrace : WordTrace (prefixWord ++ tailWord_3344967) baseStart_3344967 baseEnd_3344967 := by
    simpa [prefixWord, tailWord_3344967, baseEnd_3344967] using wordTrace_append hprefix tailTrace_3344967
  have hstable : (prefixWord ++ tailWord_3344967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3344967).length < 2 ^ (prefixWord ++ tailWord_3344967).sum := by decide
  have hdescent : baseEnd_3344967 < baseStart_3344967 := by decide
  rcases family_descends (prefixWord ++ tailWord_3344967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3344976 : List Nat := [2, 1, 1, 1, 1, 3, 2, 2, 2, 8]
def baseStart_3344976 : Nat := 118140960795 + 3344976 * 2 ^ 59
def prefixEnd_3344976 : Nat := 4983230072969 + 3 ^ 40 * 3344976 * 2
def baseEnd_3344976 : Nat := 572526821917936666572247

theorem tailTrace_3344976 : CollatzResearch.WordTrace tailWord_3344976 prefixEnd_3344976 572526821917936666572247 := by
  unfold tailWord_3344976
  simp only [CollatzResearch.WordTrace]
  refine ⟨61000648764865351632135391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81334198353153802176180521 61000648764865351632135391)
  ·
    refine ⟨91500973147298027448203087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61000648764865351632135391 91500973147298027448203087)
    ·
      refine ⟨137251459720947041172304631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91500973147298027448203087 137251459720947041172304631)
      ·
        refine ⟨205877189581420561758456947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137251459720947041172304631 205877189581420561758456947)
        ·
          refine ⟨308815784372130842637685421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 205877189581420561758456947 308815784372130842637685421)
          ·
            refine ⟨115805919139549065989132033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 308815784372130842637685421 115805919139549065989132033)
            ·
              refine ⟨86854439354661799491849025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 115805919139549065989132033 86854439354661799491849025)
              ·
                refine ⟨65140829515996349618886769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86854439354661799491849025 65140829515996349618886769)
                ·
                  refine ⟨48855622136997262214165077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65140829515996349618886769 48855622136997262214165077)
                  ·
                    refine ⟨572526821917936666572247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 48855622136997262214165077 572526821917936666572247)
                    ·
                      rfl

theorem cell23_3344976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 2, 2, 8].length) (baseStart_3344976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3344976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3344976 prefixEnd_3344976 := by exact prefixLift 3344976
  have htrace : WordTrace (prefixWord ++ tailWord_3344976) baseStart_3344976 baseEnd_3344976 := by
    simpa [prefixWord, tailWord_3344976, baseEnd_3344976] using wordTrace_append hprefix tailTrace_3344976
  have hstable : (prefixWord ++ tailWord_3344976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3344976).length < 2 ^ (prefixWord ++ tailWord_3344976).sum := by decide
  have hdescent : baseEnd_3344976 < baseStart_3344976 := by decide
  rcases family_descends (prefixWord ++ tailWord_3344976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3344983 : List Nat := [1, 1, 3, 2, 2, 2, 1, 2, 4, 1, 4]
def baseStart_3344983 : Nat := 118140960795 + 3344983 * 2 ^ 59
def prefixEnd_3344983 : Nat := 4983230072969 + 3 ^ 40 * 3344983 * 2
def baseEnd_3344983 : Nat := 1717584060118391472329209

theorem tailTrace_3344983 : CollatzResearch.WordTrace tailWord_3344983 prefixEnd_3344983 1717584060118391472329209 := by
  unfold tailWord_3344983
  simp only [CollatzResearch.WordTrace]
  refine ⟨122001552840705343459775603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81334368560470228973183735 122001552840705343459775603)
  ·
    refine ⟨183002329261058015189663405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122001552840705343459775603 183002329261058015189663405)
    ·
      refine ⟨68625873472896755696123777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 183002329261058015189663405 68625873472896755696123777)
      ·
        refine ⟨51469405104672566772092833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68625873472896755696123777 51469405104672566772092833)
        ·
          refine ⟨38602053828504425079069625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51469405104672566772092833 38602053828504425079069625)
          ·
            refine ⟨28951540371378318809302219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38602053828504425079069625 28951540371378318809302219)
            ·
              refine ⟨43427310557067478213953329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28951540371378318809302219 43427310557067478213953329)
              ·
                refine ⟨32570482917800608660464997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43427310557067478213953329 32570482917800608660464997)
                ·
                  refine ⟨6106965547087614123837187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32570482917800608660464997 6106965547087614123837187)
                  ·
                    refine ⟨9160448320631421185755781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6106965547087614123837187 9160448320631421185755781)
                    ·
                      refine ⟨1717584060118391472329209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9160448320631421185755781 1717584060118391472329209)
                      ·
                        rfl

theorem cell23_3344983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 2, 4, 1, 4].length) (baseStart_3344983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3344983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3344983 prefixEnd_3344983 := by exact prefixLift 3344983
  have htrace : WordTrace (prefixWord ++ tailWord_3344983) baseStart_3344983 baseEnd_3344983 := by
    simpa [prefixWord, tailWord_3344983, baseEnd_3344983] using wordTrace_append hprefix tailTrace_3344983
  have hstable : (prefixWord ++ tailWord_3344983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3344983).length < 2 ^ (prefixWord ++ tailWord_3344983).sum := by decide
  have hdescent : baseEnd_3344983 < baseStart_3344983 := by decide
  rcases family_descends (prefixWord ++ tailWord_3344983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3345020 : List Nat := [2, 2, 2, 1, 1, 2, 4, 2, 2, 2, 3]
def baseStart_3345020 : Nat := 118140960795 + 3345020 * 2 ^ 59
def prefixEnd_3345020 : Nat := 4983230072969 + 3 ^ 40 * 3345020 * 2
def baseEnd_3345020 : Nat := 1717603058902607827566539

theorem tailTrace_3345020 : CollatzResearch.WordTrace tailWord_3345020 prefixEnd_3345020 1717603058902607827566539 := by
  unfold tailWord_3345020
  simp only [CollatzResearch.WordTrace]
  refine ⟨61001451170785649389436257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81335268227714199185915009 61001451170785649389436257)
  ·
    refine ⟨45751088378089237042077193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61001451170785649389436257 45751088378089237042077193)
    ·
      refine ⟨34313316283566927781557895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45751088378089237042077193 34313316283566927781557895)
      ·
        refine ⟨51469974425350391672336843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34313316283566927781557895 51469974425350391672336843)
        ·
          refine ⟨77204961638025587508505265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51469974425350391672336843 77204961638025587508505265)
          ·
            refine ⟨57903721228519190631378949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77204961638025587508505265 57903721228519190631378949)
            ·
              refine ⟨10856947730347348243383553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57903721228519190631378949 10856947730347348243383553)
              ·
                refine ⟨8142710797760511182537665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10856947730347348243383553 8142710797760511182537665)
                ·
                  refine ⟨6107033098320383386903249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8142710797760511182537665 6107033098320383386903249)
                  ·
                    refine ⟨4580274823740287540177437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6107033098320383386903249 4580274823740287540177437)
                    ·
                      refine ⟨1717603058902607827566539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4580274823740287540177437 1717603058902607827566539)
                      ·
                        rfl

theorem cell23_3345020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 4, 2, 2, 2, 3].length) (baseStart_3345020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3345020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3345020 prefixEnd_3345020 := by exact prefixLift 3345020
  have htrace : WordTrace (prefixWord ++ tailWord_3345020) baseStart_3345020 baseEnd_3345020 := by
    simpa [prefixWord, tailWord_3345020, baseEnd_3345020] using wordTrace_append hprefix tailTrace_3345020
  have hstable : (prefixWord ++ tailWord_3345020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3345020).length < 2 ^ (prefixWord ++ tailWord_3345020).sum := by decide
  have hdescent : baseEnd_3345020 < baseStart_3345020 := by decide
  rcases family_descends (prefixWord ++ tailWord_3345020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3345033 : List Nat := [1, 2, 1, 1, 4, 1, 1, 2, 2, 5, 3]
def baseStart_3345033 : Nat := 118140960795 + 3345033 * 2 ^ 59
def prefixEnd_3345033 : Nat := 4983230072969 + 3 ^ 40 * 3345033 * 2
def baseEnd_3345033 : Nat := 1717609734151116276703979

theorem tailTrace_3345033 : CollatzResearch.WordTrace tailWord_3345033 prefixEnd_3345033 1717609734151116276703979 := by
  unfold tailWord_3345033
  simp only [CollatzResearch.WordTrace]
  refine ⟨122003376490524201999095753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81335584327016134666063835 122003376490524201999095753)
  ·
    refine ⟨91502532367893151499321815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122003376490524201999095753 91502532367893151499321815)
    ·
      refine ⟨137253798551839727248982723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91502532367893151499321815 137253798551839727248982723)
      ·
        refine ⟨205880697827759590873474085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137253798551839727248982723 205880697827759590873474085)
        ·
          refine ⟨38602630842704923288776391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 205880697827759590873474085 38602630842704923288776391)
          ·
            refine ⟨57903946264057384933164587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38602630842704923288776391 57903946264057384933164587)
            ·
              refine ⟨86855919396086077399746881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57903946264057384933164587 86855919396086077399746881)
              ·
                refine ⟨65141939547064558049810161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86855919396086077399746881 65141939547064558049810161)
                ·
                  refine ⟨48856454660298418537357621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65141939547064558049810161 48856454660298418537357621)
                  ·
                    refine ⟨4580292624402976737877277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 48856454660298418537357621 4580292624402976737877277)
                    ·
                      refine ⟨1717609734151116276703979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4580292624402976737877277 1717609734151116276703979)
                      ·
                        rfl

theorem cell23_3345033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 2, 2, 5, 3].length) (baseStart_3345033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3345033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3345033 prefixEnd_3345033 := by exact prefixLift 3345033
  have htrace : WordTrace (prefixWord ++ tailWord_3345033) baseStart_3345033 baseEnd_3345033 := by
    simpa [prefixWord, tailWord_3345033, baseEnd_3345033] using wordTrace_append hprefix tailTrace_3345033
  have hstable : (prefixWord ++ tailWord_3345033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3345033).length < 2 ^ (prefixWord ++ tailWord_3345033).sum := by decide
  have hdescent : baseEnd_3345033 < baseStart_3345033 := by decide
  rcases family_descends (prefixWord ++ tailWord_3345033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3345084 : List Nat := [2, 2, 2, 3, 1, 1, 1, 6, 1, 1, 3]
def baseStart_3345084 : Nat := 118140960795 + 3345084 * 2 ^ 59
def prefixEnd_3345084 : Nat := 4983230072969 + 3 ^ 40 * 3345084 * 2
def baseEnd_3345084 : Nat := 1717635921664495577166245

theorem tailTrace_3345084 : CollatzResearch.WordTrace tailWord_3345084 prefixEnd_3345084 1717635921664495577166245 := by
  unfold tailWord_3345084
  simp only [CollatzResearch.WordTrace]
  refine ⟨61002618306669718854601153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81336824408892958472801537 61002618306669718854601153)
  ·
    refine ⟨45751963730002289140950865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61002618306669718854601153 45751963730002289140950865)
    ·
      refine ⟨34313972797501716855713149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45751963730002289140950865 34313972797501716855713149)
      ·
        refine ⟨12867739799063143820892431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34313972797501716855713149 12867739799063143820892431)
        ·
          refine ⟨19301609698594715731338647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12867739799063143820892431 19301609698594715731338647)
          ·
            refine ⟨28952414547892073597007971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19301609698594715731338647 28952414547892073597007971)
            ·
              refine ⟨43428621821838110395511957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28952414547892073597007971 43428621821838110395511957)
              ·
                refine ⟨2035716647898661424789623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 43428621821838110395511957 2035716647898661424789623)
                ·
                  refine ⟨3053574971847992137184435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2035716647898661424789623 3053574971847992137184435)
                  ·
                    refine ⟨4580362457771988205776653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3053574971847992137184435 4580362457771988205776653)
                    ·
                      refine ⟨1717635921664495577166245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4580362457771988205776653 1717635921664495577166245)
                      ·
                        rfl

theorem cell23_3345084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 6, 1, 1, 3].length) (baseStart_3345084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3345084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3345084 prefixEnd_3345084 := by exact prefixLift 3345084
  have htrace : WordTrace (prefixWord ++ tailWord_3345084) baseStart_3345084 baseEnd_3345084 := by
    simpa [prefixWord, tailWord_3345084, baseEnd_3345084] using wordTrace_append hprefix tailTrace_3345084
  have hstable : (prefixWord ++ tailWord_3345084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3345084).length < 2 ^ (prefixWord ++ tailWord_3345084).sum := by decide
  have hdescent : baseEnd_3345084 < baseStart_3345084 := by decide
  rcases family_descends (prefixWord ++ tailWord_3345084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3345113 : List Nat := [1, 2, 1, 2, 3, 2, 3, 9]
def baseStart_3345113 : Nat := 118140960795 + 3345113 * 2 ^ 59
def prefixEnd_3345113 : Nat := 4983230072969 + 3 ^ 40 * 3345113 * 2
def baseEnd_3345113 : Nat := 63616696763091702359393

theorem tailTrace_3345113 : CollatzResearch.WordTrace tailWord_3345113 prefixEnd_3345113 63616696763091702359393 := by
  unfold tailWord_3345113
  simp only [CollatzResearch.WordTrace]
  refine ⟨122006294330234375662007993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81337529553489583774671995 122006294330234375662007993)
  ·
    refine ⟨91504720747675781746505995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122006294330234375662007993 91504720747675781746505995)
    ·
      refine ⟨137257081121513672619758993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91504720747675781746505995 137257081121513672619758993)
      ·
        refine ⟨102942810841135254464819245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137257081121513672619758993 102942810841135254464819245)
        ·
          refine ⟨38603554065425720424307217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102942810841135254464819245 38603554065425720424307217)
          ·
            refine ⟨28952665549069290318230413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38603554065425720424307217 28952665549069290318230413)
            ·
              refine ⟨10857249580900983869336405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28952665549069290318230413 10857249580900983869336405)
              ·
                refine ⟨63616696763091702359393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 10857249580900983869336405 63616696763091702359393)
                ·
                  rfl

theorem cell23_3345113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 3, 9].length) (baseStart_3345113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3345113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3345113 prefixEnd_3345113 := by exact prefixLift 3345113
  have htrace : WordTrace (prefixWord ++ tailWord_3345113) baseStart_3345113 baseEnd_3345113 := by
    simpa [prefixWord, tailWord_3345113, baseEnd_3345113] using wordTrace_append hprefix tailTrace_3345113
  have hstable : (prefixWord ++ tailWord_3345113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3345113).length < 2 ^ (prefixWord ++ tailWord_3345113).sum := by decide
  have hdescent : baseEnd_3345113 < baseStart_3345113 := by decide
  rcases family_descends (prefixWord ++ tailWord_3345113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3345143 : List Nat := [1, 1, 3, 1, 1, 1, 3, 3, 2, 7]
def baseStart_3345143 : Nat := 118140960795 + 3345143 * 2 ^ 59
def prefixEnd_3345143 : Nat := 4983230072969 + 3 ^ 40 * 3345143 * 2
def baseEnd_3345143 : Nat := 572555405674370282109491

theorem tailTrace_3345143 : CollatzResearch.WordTrace tailWord_3345143 prefixEnd_3345143 572555405674370282109491 := by
  unfold tailWord_3345143
  simp only [CollatzResearch.WordTrace]
  refine ⟨122007388520125690785600083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81338259013417127190400055 122007388520125690785600083)
  ·
    refine ⟨183011082780188536178400125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122007388520125690785600083 183011082780188536178400125)
    ·
      refine ⟨68629156042570701066900047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 183011082780188536178400125 68629156042570701066900047)
      ·
        refine ⟨102943734063856051600350071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68629156042570701066900047 102943734063856051600350071)
        ·
          refine ⟨154415601095784077400525107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102943734063856051600350071 154415601095784077400525107)
          ·
            refine ⟨231623401643676116100787661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154415601095784077400525107 231623401643676116100787661)
            ·
              refine ⟨86858775616378543537795373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 231623401643676116100787661 86858775616378543537795373)
              ·
                refine ⟨32572040856141953826673265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 86858775616378543537795373 32572040856141953826673265)
                ·
                  refine ⟨24429030642106465370004949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32572040856141953826673265 24429030642106465370004949)
                  ·
                    refine ⟨572555405674370282109491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24429030642106465370004949 572555405674370282109491)
                    ·
                      rfl

theorem cell23_3345143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 3, 2, 7].length) (baseStart_3345143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3345143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3345143 prefixEnd_3345143 := by exact prefixLift 3345143
  have htrace : WordTrace (prefixWord ++ tailWord_3345143) baseStart_3345143 baseEnd_3345143 := by
    simpa [prefixWord, tailWord_3345143, baseEnd_3345143] using wordTrace_append hprefix tailTrace_3345143
  have hstable : (prefixWord ++ tailWord_3345143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3345143).length < 2 ^ (prefixWord ++ tailWord_3345143).sum := by decide
  have hdescent : baseEnd_3345143 < baseStart_3345143 := by decide
  rcases family_descends (prefixWord ++ tailWord_3345143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3345163 : List Nat := [1, 1, 1, 1, 5, 1, 1, 1, 1, 2, 8]
def baseStart_3345163 : Nat := 118140960795 + 3345163 * 2 ^ 59
def prefixEnd_3345163 : Nat := 4983230072969 + 3 ^ 40 * 3345163 * 2
def baseEnd_3345163 : Nat := 1717676486636200768078381

theorem tailTrace_3345163 : CollatzResearch.WordTrace tailWord_3345163 prefixEnd_3345163 1717676486636200768078381 := by
  unfold tailWord_3345163
  simp only [CollatzResearch.WordTrace]
  refine ⟨122008117980053234201328143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81338745320035489467552095 122008117980053234201328143)
  ·
    refine ⟨183012176970079851301992215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122008117980053234201328143 183012176970079851301992215)
    ·
      refine ⟨274518265455119776952988323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183012176970079851301992215 274518265455119776952988323)
      ·
        refine ⟨411777398182679665429482485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 274518265455119776952988323 411777398182679665429482485)
        ·
          refine ⟨38604131079626218634013983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 411777398182679665429482485 38604131079626218634013983)
          ·
            refine ⟨57906196619439327951020975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38604131079626218634013983 57906196619439327951020975)
            ·
              refine ⟨86859294929158991926531463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57906196619439327951020975 86859294929158991926531463)
              ·
                refine ⟨130288942393738487889797195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86859294929158991926531463 130288942393738487889797195)
                ·
                  refine ⟨195433413590607731834695793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 130288942393738487889797195 195433413590607731834695793)
                  ·
                    refine ⟨146575060192955798876021845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 195433413590607731834695793 146575060192955798876021845)
                    ·
                      refine ⟨1717676486636200768078381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 146575060192955798876021845 1717676486636200768078381)
                      ·
                        rfl

theorem cell23_3345163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 1, 1, 2, 8].length) (baseStart_3345163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3345163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3345163 prefixEnd_3345163 := by exact prefixLift 3345163
  have htrace : WordTrace (prefixWord ++ tailWord_3345163) baseStart_3345163 baseEnd_3345163 := by
    simpa [prefixWord, tailWord_3345163, baseEnd_3345163] using wordTrace_append hprefix tailTrace_3345163
  have hstable : (prefixWord ++ tailWord_3345163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3345163).length < 2 ^ (prefixWord ++ tailWord_3345163).sum := by decide
  have hdescent : baseEnd_3345163 < baseStart_3345163 := by decide
  rcases family_descends (prefixWord ++ tailWord_3345163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3345167 : List Nat := [1, 1, 2, 1, 1, 1, 7, 1, 3, 3, 2]
def baseStart_3345167 : Nat := 118140960795 + 3345167 * 2 ^ 59
def prefixEnd_3345167 : Nat := 4983230072969 + 3 ^ 40 * 3345167 * 2
def baseEnd_3345167 : Nat := 1717678540558818752428363

theorem tailTrace_3345167 : CollatzResearch.WordTrace tailWord_3345167 prefixEnd_3345167 1717678540558818752428363 := by
  unfold tailWord_3345167
  simp only [CollatzResearch.WordTrace]
  refine ⟨122008263872038742884473755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81338842581359161922982503 122008263872038742884473755)
  ·
    refine ⟨183012395808058114326710633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122008263872038742884473755 183012395808058114326710633)
    ·
      refine ⟨137259296856043585745032975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183012395808058114326710633 137259296856043585745032975)
      ·
        refine ⟨205888945284065378617549463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137259296856043585745032975 205888945284065378617549463)
        ·
          refine ⟨308833417926098067926324195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 205888945284065378617549463 308833417926098067926324195)
          ·
            refine ⟨463250126889147101889486293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 308833417926098067926324195 463250126889147101889486293)
            ·
              refine ⟨10857424848964385200534835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 463250126889147101889486293 10857424848964385200534835)
              ·
                refine ⟨16286137273446577800802253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10857424848964385200534835 16286137273446577800802253)
                ·
                  refine ⟨6107301477542466675300845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16286137273446577800802253 6107301477542466675300845)
                  ·
                    refine ⟨2290238054078425003237817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6107301477542466675300845 2290238054078425003237817)
                    ·
                      refine ⟨1717678540558818752428363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2290238054078425003237817 1717678540558818752428363)
                      ·
                        rfl

theorem cell23_3345167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 7, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 7, 1, 3, 3, 2].length) (baseStart_3345167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3345167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3345167 prefixEnd_3345167 := by exact prefixLift 3345167
  have htrace : WordTrace (prefixWord ++ tailWord_3345167) baseStart_3345167 baseEnd_3345167 := by
    simpa [prefixWord, tailWord_3345167, baseEnd_3345167] using wordTrace_append hprefix tailTrace_3345167
  have hstable : (prefixWord ++ tailWord_3345167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3345167).length < 2 ^ (prefixWord ++ tailWord_3345167).sum := by decide
  have hdescent : baseEnd_3345167 < baseStart_3345167 := by decide
  rcases family_descends (prefixWord ++ tailWord_3345167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3345260 : List Nat := [2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 7]
def baseStart_3345260 : Nat := 118140960795 + 3345260 * 2 ^ 59
def prefixEnd_3345260 : Nat := 4983230072969 + 3 ^ 40 * 3345260 * 2
def baseEnd_3345260 : Nat := 1717726294259686888565435

theorem tailTrace_3345260 : CollatzResearch.WordTrace tailWord_3345260 prefixEnd_3345260 1717726294259686888565435 := by
  unfold tailWord_3345260
  simp only [CollatzResearch.WordTrace]
  refine ⟨61005827930350909883804617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81341103907134546511739489 61005827930350909883804617)
  ·
    refine ⟨45754370947763182412853463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61005827930350909883804617 45754370947763182412853463)
    ·
      refine ⟨68631556421644773619280195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45754370947763182412853463 68631556421644773619280195)
      ·
        refine ⟨102947334632467160428920293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68631556421644773619280195 102947334632467160428920293)
        ·
          refine ⟨19302625243587592580422555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 102947334632467160428920293 19302625243587592580422555)
          ·
            refine ⟨28953937865381388870633833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19302625243587592580422555 28953937865381388870633833)
            ·
              refine ⟨21715453399036041652975375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28953937865381388870633833 21715453399036041652975375)
              ·
                refine ⟨32573180098554062479463063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21715453399036041652975375 32573180098554062479463063)
                ·
                  refine ⟨48859770147831093719194595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32573180098554062479463063 48859770147831093719194595)
                  ·
                    refine ⟨73289655221746640578791893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 48859770147831093719194595 73289655221746640578791893)
                    ·
                      refine ⟨1717726294259686888565435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 73289655221746640578791893 1717726294259686888565435)
                      ·
                        rfl

theorem cell23_3345260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 7].length) (baseStart_3345260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3345260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3345260 prefixEnd_3345260 := by exact prefixLift 3345260
  have htrace : WordTrace (prefixWord ++ tailWord_3345260) baseStart_3345260 baseEnd_3345260 := by
    simpa [prefixWord, tailWord_3345260, baseEnd_3345260] using wordTrace_append hprefix tailTrace_3345260
  have hstable : (prefixWord ++ tailWord_3345260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3345260).length < 2 ^ (prefixWord ++ tailWord_3345260).sum := by decide
  have hdescent : baseEnd_3345260 < baseStart_3345260 := by decide
  rcases family_descends (prefixWord ++ tailWord_3345260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3345287 : List Nat := [1, 1, 4, 2, 3, 1, 2, 1, 1, 3, 4]
def baseStart_3345287 : Nat := 118140960795 + 3345287 * 2 ^ 59
def prefixEnd_3345287 : Nat := 4983230072969 + 3 ^ 40 * 3345287 * 2
def baseEnd_3345287 : Nat := 1717740158237358282927811

theorem tailTrace_3345287 : CollatzResearch.WordTrace tailWord_3345287 prefixEnd_3345287 1717740158237358282927811 := by
  unfold tailWord_3345287
  simp only [CollatzResearch.WordTrace]
  refine ⟨122012640631604003378842115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81341760421069335585894743 122012640631604003378842115)
  ·
    refine ⟨183018960947406005068263173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122012640631604003378842115 183018960947406005068263173)
    ·
      refine ⟨34316055177638625950299345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 183018960947406005068263173 34316055177638625950299345)
      ·
        refine ⟨25737041383228969462724509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34316055177638625950299345 25737041383228969462724509)
        ·
          refine ⟨9651390518710863548521691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25737041383228969462724509 9651390518710863548521691)
          ·
            refine ⟨14477085778066295322782537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9651390518710863548521691 14477085778066295322782537)
            ·
              refine ⟨10857814333549721492086903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14477085778066295322782537 10857814333549721492086903)
              ·
                refine ⟨16286721500324582238130355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10857814333549721492086903 16286721500324582238130355)
                ·
                  refine ⟨24430082250486873357195533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16286721500324582238130355 24430082250486873357195533)
                  ·
                    refine ⟨9161280843932577508948325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24430082250486873357195533 9161280843932577508948325)
                    ·
                      refine ⟨1717740158237358282927811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9161280843932577508948325 1717740158237358282927811)
                      ·
                        rfl

theorem cell23_3345287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 2, 1, 1, 3, 4].length) (baseStart_3345287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3345287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3345287 prefixEnd_3345287 := by exact prefixLift 3345287
  have htrace : WordTrace (prefixWord ++ tailWord_3345287) baseStart_3345287 baseEnd_3345287 := by
    simpa [prefixWord, tailWord_3345287, baseEnd_3345287] using wordTrace_append hprefix tailTrace_3345287
  have hstable : (prefixWord ++ tailWord_3345287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3345287).length < 2 ^ (prefixWord ++ tailWord_3345287).sum := by decide
  have hdescent : baseEnd_3345287 < baseStart_3345287 := by decide
  rcases family_descends (prefixWord ++ tailWord_3345287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3345341 : List Nat := [1, 4, 1, 2, 4, 1, 2, 1, 2, 2, 3]
def baseStart_3345341 : Nat := 118140960795 + 3345341 * 2 ^ 59
def prefixEnd_3345341 : Nat := 4983230072969 + 3 ^ 40 * 3345341 * 2
def baseEnd_3345341 : Nat := 1717767886192701071652563

theorem tailTrace_3345341 : CollatzResearch.WordTrace tailWord_3345341 prefixEnd_3345341 1717767886192701071652563 := by
  unfold tailWord_3345341
  simp only [CollatzResearch.WordTrace]
  refine ⟨122014610173408370601307877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81343073448938913734205251 122014610173408370601307877)
  ·
    refine ⟨22877739407514069487745227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 122014610173408370601307877 22877739407514069487745227)
    ·
      refine ⟨34316609111271104231617841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22877739407514069487745227 34316609111271104231617841)
      ·
        refine ⟨25737456833453328173713381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34316609111271104231617841 25737456833453328173713381)
        ·
          refine ⟨4825773156272499032571259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25737456833453328173713381 4825773156272499032571259)
          ·
            refine ⟨7238659734408748548856889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4825773156272499032571259 7238659734408748548856889)
            ·
              refine ⟨5428994800806561411642667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7238659734408748548856889 5428994800806561411642667)
              ·
                refine ⟨8143492201209842117464001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5428994800806561411642667 8143492201209842117464001)
                ·
                  refine ⟨6107619150907381588098001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8143492201209842117464001 6107619150907381588098001)
                  ·
                    refine ⟨4580714363180536191073501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6107619150907381588098001 4580714363180536191073501)
                    ·
                      refine ⟨1717767886192701071652563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4580714363180536191073501 1717767886192701071652563)
                      ·
                        rfl

theorem cell23_3345341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 2, 1, 2, 2, 3].length) (baseStart_3345341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3345341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3345341 prefixEnd_3345341 := by exact prefixLift 3345341
  have htrace : WordTrace (prefixWord ++ tailWord_3345341) baseStart_3345341 baseEnd_3345341 := by
    simpa [prefixWord, tailWord_3345341, baseEnd_3345341] using wordTrace_append hprefix tailTrace_3345341
  have hstable : (prefixWord ++ tailWord_3345341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3345341).length < 2 ^ (prefixWord ++ tailWord_3345341).sum := by decide
  have hdescent : baseEnd_3345341 < baseStart_3345341 := by decide
  rcases family_descends (prefixWord ++ tailWord_3345341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3345365 : List Nat := [1, 3, 2, 3, 3, 2, 2, 2, 1, 4]
def baseStart_3345365 : Nat := 118140960795 + 3345365 * 2 ^ 59
def prefixEnd_3345365 : Nat := 4983230072969 + 3 ^ 40 * 3345365 * 2
def baseEnd_3345365 : Nat := 572593403242802992584151

theorem tailTrace_3345365 : CollatzResearch.WordTrace tailWord_3345365 prefixEnd_3345365 572593403242802992584151 := by
  unfold tailWord_3345365
  simp only [CollatzResearch.WordTrace]
  refine ⟨122015485525321422700181549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81343657016880948466787699 122015485525321422700181549)
  ·
    refine ⟨45755807071995533512568081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122015485525321422700181549 45755807071995533512568081)
    ·
      refine ⟨34316855303996650134426061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45755807071995533512568081 34316855303996650134426061)
      ·
        refine ⟨12868820738998743800409773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34316855303996650134426061 12868820738998743800409773)
        ·
          refine ⟨4825807777124528925153665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12868820738998743800409773 4825807777124528925153665)
          ·
            refine ⟨3619355832843396693865249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4825807777124528925153665 3619355832843396693865249)
            ·
              refine ⟨2714516874632547520398937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3619355832843396693865249 2714516874632547520398937)
              ·
                refine ⟨2035887655974410640299203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2714516874632547520398937 2035887655974410640299203)
                ·
                  refine ⟨3053831483961615960448805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2035887655974410640299203 3053831483961615960448805)
                  ·
                    refine ⟨572593403242802992584151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3053831483961615960448805 572593403242802992584151)
                    ·
                      rfl

theorem cell23_3345365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 2, 2, 2, 1, 4].length) (baseStart_3345365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3345365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3345365 prefixEnd_3345365 := by exact prefixLift 3345365
  have htrace : WordTrace (prefixWord ++ tailWord_3345365) baseStart_3345365 baseEnd_3345365 := by
    simpa [prefixWord, tailWord_3345365, baseEnd_3345365] using wordTrace_append hprefix tailTrace_3345365
  have hstable : (prefixWord ++ tailWord_3345365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3345365).length < 2 ^ (prefixWord ++ tailWord_3345365).sum := by decide
  have hdescent : baseEnd_3345365 < baseStart_3345365 := by decide
  rcases family_descends (prefixWord ++ tailWord_3345365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3345387 : List Nat := [1, 1, 1, 1, 2, 3, 1, 1, 8, 4]
def baseStart_3345387 : Nat := 118140960795 + 3345387 * 2 ^ 59
def prefixEnd_3345387 : Nat := 4983230072969 + 3 ^ 40 * 3345387 * 2
def baseEnd_3345387 : Nat := 572597168767602630559117

theorem tailTrace_3345387 : CollatzResearch.WordTrace tailWord_3345387 prefixEnd_3345387 572597168767602630559117 := by
  unfold tailWord_3345387
  simp only [CollatzResearch.WordTrace]
  refine ⟨122016287931241720457482415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81344191954161146971654943 122016287931241720457482415)
  ·
    refine ⟨183024431896862580686223623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122016287931241720457482415 183024431896862580686223623)
    ·
      refine ⟨274536647845293871029335435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183024431896862580686223623 274536647845293871029335435)
      ·
        refine ⟨411804971767940806544003153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 274536647845293871029335435 411804971767940806544003153)
        ·
          refine ⟨308853728825955604908002365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 411804971767940806544003153 308853728825955604908002365)
          ·
            refine ⟨115820148309733351840500887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 308853728825955604908002365 115820148309733351840500887)
            ·
              refine ⟨173730222464600027760751331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115820148309733351840500887 173730222464600027760751331)
              ·
                refine ⟨260595333696900041641126997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 173730222464600027760751331 260595333696900041641126997)
                ·
                  refine ⟨3053851566760547362981957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 260595333696900041641126997 3053851566760547362981957)
                  ·
                    refine ⟨572597168767602630559117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3053851566760547362981957 572597168767602630559117)
                    ·
                      rfl

theorem cell23_3345387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 1, 8, 4].length) (baseStart_3345387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3345387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3345387 prefixEnd_3345387 := by exact prefixLift 3345387
  have htrace : WordTrace (prefixWord ++ tailWord_3345387) baseStart_3345387 baseEnd_3345387 := by
    simpa [prefixWord, tailWord_3345387, baseEnd_3345387] using wordTrace_append hprefix tailTrace_3345387
  have hstable : (prefixWord ++ tailWord_3345387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3345387).length < 2 ^ (prefixWord ++ tailWord_3345387).sum := by decide
  have hdescent : baseEnd_3345387 < baseStart_3345387 := by decide
  rcases family_descends (prefixWord ++ tailWord_3345387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3345398 : List Nat := [5, 1, 1, 1, 3, 1, 3, 1, 2, 3, 2]
def baseStart_3345398 : Nat := 118140960795 + 3345398 * 2 ^ 59
def prefixEnd_3345398 : Nat := 4983230072969 + 3 ^ 40 * 3345398 * 2
def baseEnd_3345398 : Nat := 1717797154590007348639801

theorem tailTrace_3345398 : CollatzResearch.WordTrace tailWord_3345398 prefixEnd_3345398 1717797154590007348639801 := by
  unfold tailWord_3345398
  simp only [CollatzResearch.WordTrace]
  refine ⟨7626043070887616833508303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 81344459422801246224088565 7626043070887616833508303)
  ·
    refine ⟨11439064606331425250262455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7626043070887616833508303 11439064606331425250262455)
    ·
      refine ⟨17158596909497137875393683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11439064606331425250262455 17158596909497137875393683)
      ·
        refine ⟨25737895364245706813090525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17158596909497137875393683 25737895364245706813090525)
        ·
          refine ⟨9651710761592140054908947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25737895364245706813090525 9651710761592140054908947)
          ·
            refine ⟨14477566142388210082363421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9651710761592140054908947 14477566142388210082363421)
            ·
              refine ⟨5429087303395578780886283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14477566142388210082363421 5429087303395578780886283)
              ·
                refine ⟨8143630955093368171329425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5429087303395578780886283 8143630955093368171329425)
                ·
                  refine ⟨6107723216320026128497069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8143630955093368171329425 6107723216320026128497069)
                  ·
                    refine ⟨2290396206120009798186401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6107723216320026128497069 2290396206120009798186401)
                    ·
                      refine ⟨1717797154590007348639801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2290396206120009798186401 1717797154590007348639801)
                      ·
                        rfl

theorem cell23_3345398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 3, 1, 2, 3, 2].length) (baseStart_3345398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3345398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3345398 prefixEnd_3345398 := by exact prefixLift 3345398
  have htrace : WordTrace (prefixWord ++ tailWord_3345398) baseStart_3345398 baseEnd_3345398 := by
    simpa [prefixWord, tailWord_3345398, baseEnd_3345398] using wordTrace_append hprefix tailTrace_3345398
  have hstable : (prefixWord ++ tailWord_3345398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3345398).length < 2 ^ (prefixWord ++ tailWord_3345398).sum := by decide
  have hdescent : baseEnd_3345398 < baseStart_3345398 := by decide
  rcases family_descends (prefixWord ++ tailWord_3345398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3345441 : List Nat := [1, 2, 3, 2, 3, 3, 1, 1, 1, 2, 4]
def baseStart_3345441 : Nat := 118140960795 + 3345441 * 2 ^ 59
def prefixEnd_3345441 : Nat := 4983230072969 + 3 ^ 40 * 3345441 * 2
def baseEnd_3345441 : Nat := 1717819234258150680402103

theorem tailTrace_3345441 : CollatzResearch.WordTrace tailWord_3345441 prefixEnd_3345441 1717819234258150680402103 := by
  unfold tailWord_3345441
  simp only [CollatzResearch.WordTrace]
  refine ⟨122018257473046087679948177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81345504982030725119965451 122018257473046087679948177)
  ·
    refine ⟨91513693104784565759961133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122018257473046087679948177 91513693104784565759961133)
    ·
      refine ⟨34317634914294212159985425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91513693104784565759961133 34317634914294212159985425)
      ·
        refine ⟨25738226185720659119989069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34317634914294212159985425 25738226185720659119989069)
        ·
          refine ⟨9651834819645247169995901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25738226185720659119989069 9651834819645247169995901)
          ·
            refine ⟨3619438057366967688748463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9651834819645247169995901 3619438057366967688748463)
            ·
              refine ⟨5429157086050451533122695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3619438057366967688748463 5429157086050451533122695)
              ·
                refine ⟨8143735629075677299684043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5429157086050451533122695 8143735629075677299684043)
                ·
                  refine ⟨12215603443613515949526065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8143735629075677299684043 12215603443613515949526065)
                  ·
                    refine ⟨9161702582710136962144549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12215603443613515949526065 9161702582710136962144549)
                    ·
                      refine ⟨1717819234258150680402103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9161702582710136962144549 1717819234258150680402103)
                      ·
                        rfl

theorem cell23_3345441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 3, 1, 1, 1, 2, 4].length) (baseStart_3345441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3345441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3345441 prefixEnd_3345441 := by exact prefixLift 3345441
  have htrace : WordTrace (prefixWord ++ tailWord_3345441) baseStart_3345441 baseEnd_3345441 := by
    simpa [prefixWord, tailWord_3345441, baseEnd_3345441] using wordTrace_append hprefix tailTrace_3345441
  have hstable : (prefixWord ++ tailWord_3345441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3345441).length < 2 ^ (prefixWord ++ tailWord_3345441).sum := by decide
  have hdescent : baseEnd_3345441 < baseStart_3345441 := by decide
  rcases family_descends (prefixWord ++ tailWord_3345441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3345457 : List Nat := [1, 2, 2, 3, 1, 2, 1, 1, 1, 4, 5]
def baseStart_3345457 : Nat := 118140960795 + 3345457 * 2 ^ 59
def prefixEnd_3345457 : Nat := 4983230072969 + 3 ^ 40 * 3345457 * 2
def baseEnd_3345457 : Nat := 1717827449948622617802029

theorem tailTrace_3345457 : CollatzResearch.WordTrace tailWord_3345457 prefixEnd_3345457 1717827449948622617802029 := by
  unfold tailWord_3345457
  simp only [CollatzResearch.WordTrace]
  refine ⟨122018841040988122412530625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81345894027325414941687083 122018841040988122412530625)
  ·
    refine ⟨91514130780741091809397969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122018841040988122412530625 91514130780741091809397969)
    ·
      refine ⟨68635598085555818857048477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91514130780741091809397969 68635598085555818857048477)
      ·
        refine ⟨25738349282083432071393179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68635598085555818857048477 25738349282083432071393179)
        ·
          refine ⟨38607523923125148107089769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25738349282083432071393179 38607523923125148107089769)
          ·
            refine ⟨28955642942343861080317327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38607523923125148107089769 28955642942343861080317327)
            ·
              refine ⟨43433464413515791620475991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28955642942343861080317327 43433464413515791620475991)
              ·
                refine ⟨65150196620273687430713987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43433464413515791620475991 65150196620273687430713987)
                ·
                  refine ⟨97725294930410531146070981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65150196620273687430713987 97725294930410531146070981)
                  ·
                    refine ⟨18323492799451974589888309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 97725294930410531146070981 18323492799451974589888309)
                    ·
                      refine ⟨1717827449948622617802029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18323492799451974589888309 1717827449948622617802029)
                      ·
                        rfl

theorem cell23_3345457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 1, 1, 4, 5].length) (baseStart_3345457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3345457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3345457 prefixEnd_3345457 := by exact prefixLift 3345457
  have htrace : WordTrace (prefixWord ++ tailWord_3345457) baseStart_3345457 baseEnd_3345457 := by
    simpa [prefixWord, tailWord_3345457, baseEnd_3345457] using wordTrace_append hprefix tailTrace_3345457
  have hstable : (prefixWord ++ tailWord_3345457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3345457).length < 2 ^ (prefixWord ++ tailWord_3345457).sum := by decide
  have hdescent : baseEnd_3345457 < baseStart_3345457 := by decide
  rcases family_descends (prefixWord ++ tailWord_3345457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3345462 : List Nat := [5, 1, 2, 1, 1, 2, 3, 3, 1, 2, 2]
def baseStart_3345462 : Nat := 118140960795 + 3345462 * 2 ^ 59
def prefixEnd_3345462 : Nat := 4983230072969 + 3 ^ 40 * 3345462 * 2
def baseEnd_3345462 : Nat := 1717830017351895098239507

theorem tailTrace_3345462 : CollatzResearch.WordTrace tailWord_3345462 prefixEnd_3345462 1717830017351895098239507 := by
  unfold tailWord_3345462
  simp only [CollatzResearch.WordTrace]
  refine ⟨7626188962873125516653915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 81346015603980005510975093 7626188962873125516653915)
  ·
    refine ⟨11439283444309688274980873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7626188962873125516653915 11439283444309688274980873)
    ·
      refine ⟨8579462583232266206235655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11439283444309688274980873 8579462583232266206235655)
      ·
        refine ⟨12869193874848399309353483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8579462583232266206235655 12869193874848399309353483)
        ·
          refine ⟨19303790812272598964030225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12869193874848399309353483 19303790812272598964030225)
          ·
            refine ⟨14477843109204449223022669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19303790812272598964030225 14477843109204449223022669)
            ·
              refine ⟨5429191165951668458633501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14477843109204449223022669 5429191165951668458633501)
              ·
                refine ⟨2035946687231875671987563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5429191165951668458633501 2035946687231875671987563)
                ·
                  refine ⟨3053920030847813507981345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2035946687231875671987563 3053920030847813507981345)
                  ·
                    refine ⟨2290440023135860130986009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3053920030847813507981345 2290440023135860130986009)
                    ·
                      refine ⟨1717830017351895098239507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2290440023135860130986009 1717830017351895098239507)
                      ·
                        rfl

theorem cell23_3345462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 3, 3, 1, 2, 2].length) (baseStart_3345462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3345462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3345462 prefixEnd_3345462 := by exact prefixLift 3345462
  have htrace : WordTrace (prefixWord ++ tailWord_3345462) baseStart_3345462 baseEnd_3345462 := by
    simpa [prefixWord, tailWord_3345462, baseEnd_3345462] using wordTrace_append hprefix tailTrace_3345462
  have hstable : (prefixWord ++ tailWord_3345462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3345462).length < 2 ^ (prefixWord ++ tailWord_3345462).sum := by decide
  have hdescent : baseEnd_3345462 < baseStart_3345462 := by decide
  rcases family_descends (prefixWord ++ tailWord_3345462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3345477 : List Nat := [1, 3, 1, 1, 1, 3, 2, 1, 4, 6]
def baseStart_3345477 : Nat := 118140960795 + 3345477 * 2 ^ 59
def prefixEnd_3345477 : Nat := 4983230072969 + 3 ^ 40 * 3345477 * 2
def baseEnd_3345477 : Nat := 572612573187237513183979

theorem tailTrace_3345477 : CollatzResearch.WordTrace tailWord_3345477 prefixEnd_3345477 572612573187237513183979 := by
  unfold tailWord_3345477
  simp only [CollatzResearch.WordTrace]
  refine ⟨122019570500915665828258685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81346380333943777218839123 122019570500915665828258685)
  ·
    refine ⟨45757338937843374685597007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122019570500915665828258685 45757338937843374685597007)
    ·
      refine ⟨68636008406765062028395511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45757338937843374685597007 68636008406765062028395511)
      ·
        refine ⟨102954012610147593042593267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68636008406765062028395511 102954012610147593042593267)
        ·
          refine ⟨154431018915221389563889901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102954012610147593042593267 154431018915221389563889901)
          ·
            refine ⟨57911632093208021086458713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 154431018915221389563889901 57911632093208021086458713)
            ·
              refine ⟨43433724069906015814844035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57911632093208021086458713 43433724069906015814844035)
              ·
                refine ⟨65150586104859023722266053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43433724069906015814844035 65150586104859023722266053)
                ·
                  refine ⟨12215734894661066947924885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 65150586104859023722266053 12215734894661066947924885)
                  ·
                    refine ⟨572612573187237513183979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12215734894661066947924885 572612573187237513183979)
                    ·
                      rfl

theorem cell23_3345477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 1, 4, 6].length) (baseStart_3345477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3345477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3345477 prefixEnd_3345477 := by exact prefixLift 3345477
  have htrace : WordTrace (prefixWord ++ tailWord_3345477) baseStart_3345477 baseEnd_3345477 := by
    simpa [prefixWord, tailWord_3345477, baseEnd_3345477] using wordTrace_append hprefix tailTrace_3345477
  have hstable : (prefixWord ++ tailWord_3345477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3345477).length < 2 ^ (prefixWord ++ tailWord_3345477).sum := by decide
  have hdescent : baseEnd_3345477 < baseStart_3345477 := by decide
  rcases family_descends (prefixWord ++ tailWord_3345477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3345487 : List Nat := [1, 1, 2, 1, 1, 2, 2, 1, 6, 1, 5]
def baseStart_3345487 : Nat := 118140960795 + 3345487 * 2 ^ 59
def prefixEnd_3345487 : Nat := 4983230072969 + 3 ^ 40 * 3345487 * 2
def baseEnd_3345487 : Nat := 1717842854368257500426891

theorem tailTrace_3345487 : CollatzResearch.WordTrace tailWord_3345487 prefixEnd_3345487 1717842854368257500426891 := by
  unfold tailWord_3345487
  simp only [CollatzResearch.WordTrace]
  refine ⟨122019935230879437536122715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81346623487252958357415143 122019935230879437536122715)
  ·
    refine ⟨183029902846319156304184073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122019935230879437536122715 183029902846319156304184073)
    ·
      refine ⟨137272427134739367228138055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183029902846319156304184073 137272427134739367228138055)
      ·
        refine ⟨205908640702109050842207083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137272427134739367228138055 205908640702109050842207083)
        ·
          refine ⟨308862961053163576263310625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 205908640702109050842207083 308862961053163576263310625)
          ·
            refine ⟨231647220789872682197482969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 308862961053163576263310625 231647220789872682197482969)
            ·
              refine ⟨173735415592404511648112227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 231647220789872682197482969 173735415592404511648112227)
              ·
                refine ⟨260603123388606767472168341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 173735415592404511648112227 260603123388606767472168341)
                ·
                  refine ⟨12215771408840942225257891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 260603123388606767472168341 12215771408840942225257891)
                  ·
                    refine ⟨18323657113261413337886837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12215771408840942225257891 18323657113261413337886837)
                    ·
                      refine ⟨1717842854368257500426891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18323657113261413337886837 1717842854368257500426891)
                      ·
                        rfl

theorem cell23_3345487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 1, 6, 1, 5].length) (baseStart_3345487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3345487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3345487 prefixEnd_3345487 := by exact prefixLift 3345487
  have htrace : WordTrace (prefixWord ++ tailWord_3345487) baseStart_3345487 baseEnd_3345487 := by
    simpa [prefixWord, tailWord_3345487, baseEnd_3345487] using wordTrace_append hprefix tailTrace_3345487
  have hstable : (prefixWord ++ tailWord_3345487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3345487).length < 2 ^ (prefixWord ++ tailWord_3345487).sum := by decide
  have hdescent : baseEnd_3345487 < baseStart_3345487 := by decide
  rcases family_descends (prefixWord ++ tailWord_3345487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3345507 : List Nat := [1, 1, 1, 5, 1, 1, 1, 3, 9]
def baseStart_3345507 : Nat := 118140960795 + 3345507 * 2 ^ 59
def prefixEnd_3345507 : Nat := 4983230072969 + 3 ^ 40 * 3345507 * 2
def baseEnd_3345507 : Nat := 190872569331260824686311

theorem tailTrace_3345507 : CollatzResearch.WordTrace tailWord_3345507 prefixEnd_3345507 190872569331260824686311 := by
  unfold tailWord_3345507
  simp only [CollatzResearch.WordTrace]
  refine ⟨122020664690806980951850775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81347109793871320634567183 122020664690806980951850775)
  ·
    refine ⟨183030997036210471427776163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122020664690806980951850775 183030997036210471427776163)
    ·
      refine ⟨274546495554315707141664245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183030997036210471427776163 274546495554315707141664245)
      ·
        refine ⟨25738733958217097544531023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 274546495554315707141664245 25738733958217097544531023)
        ·
          refine ⟨38608100937325646316796535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25738733958217097544531023 38608100937325646316796535)
          ·
            refine ⟨57912151405988469475194803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38608100937325646316796535 57912151405988469475194803)
            ·
              refine ⟨86868227108982704212792205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57912151405988469475194803 86868227108982704212792205)
              ·
                refine ⟨32575585165868514079797077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 86868227108982704212792205 32575585165868514079797077)
                ·
                  refine ⟨190872569331260824686311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 32575585165868514079797077 190872569331260824686311)
                  ·
                    rfl

theorem cell23_3345507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 3, 9].length) (baseStart_3345507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3345507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3345507 prefixEnd_3345507 := by exact prefixLift 3345507
  have htrace : WordTrace (prefixWord ++ tailWord_3345507) baseStart_3345507 baseEnd_3345507 := by
    simpa [prefixWord, tailWord_3345507, baseEnd_3345507] using wordTrace_append hprefix tailTrace_3345507
  have hstable : (prefixWord ++ tailWord_3345507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3345507).length < 2 ^ (prefixWord ++ tailWord_3345507).sum := by decide
  have hdescent : baseEnd_3345507 < baseStart_3345507 := by decide
  rcases family_descends (prefixWord ++ tailWord_3345507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3345518 : List Nat := [4, 1, 2, 2, 1, 3, 1, 2, 1, 4, 2]
def baseStart_3345518 : Nat := 118140960795 + 3345518 * 2 ^ 59
def prefixEnd_3345518 : Nat := 4983230072969 + 3 ^ 40 * 3345518 * 2
def baseEnd_3345518 : Nat := 1717858772268546879139249

theorem tailTrace_3345518 : CollatzResearch.WordTrace tailWord_3345518 prefixEnd_3345518 1717858772268546879139249 := by
  unfold tailWord_3345518
  simp only [CollatzResearch.WordTrace]
  refine ⟨15252633236720891228812651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81347377262511419887000805 15252633236720891228812651)
  ·
    refine ⟨22878949855081336843218977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15252633236720891228812651 22878949855081336843218977)
    ·
      refine ⟨17159212391311002632414233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22878949855081336843218977 17159212391311002632414233)
      ·
        refine ⟨12869409293483251974310675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17159212391311002632414233 12869409293483251974310675)
        ·
          refine ⟨19304113940224877961466013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12869409293483251974310675 19304113940224877961466013)
          ·
            refine ⟨7239042727584329235549755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19304113940224877961466013 7239042727584329235549755)
            ·
              refine ⟨10858564091376493853324633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7239042727584329235549755 10858564091376493853324633)
              ·
                refine ⟨8143923068532370389993475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10858564091376493853324633 8143923068532370389993475)
                ·
                  refine ⟨12215884602798555584990213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8143923068532370389993475 12215884602798555584990213)
                  ·
                    refine ⟨2290478363024729172185665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12215884602798555584990213 2290478363024729172185665)
                    ·
                      refine ⟨1717858772268546879139249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2290478363024729172185665 1717858772268546879139249)
                      ·
                        rfl

theorem cell23_3345518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 1, 2, 1, 4, 2].length) (baseStart_3345518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3345518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3345518 prefixEnd_3345518 := by exact prefixLift 3345518
  have htrace : WordTrace (prefixWord ++ tailWord_3345518) baseStart_3345518 baseEnd_3345518 := by
    simpa [prefixWord, tailWord_3345518, baseEnd_3345518] using wordTrace_append hprefix tailTrace_3345518
  have hstable : (prefixWord ++ tailWord_3345518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3345518).length < 2 ^ (prefixWord ++ tailWord_3345518).sum := by decide
  have hdescent : baseEnd_3345518 < baseStart_3345518 := by decide
  rcases family_descends (prefixWord ++ tailWord_3345518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3345591 : List Nat := [1, 1, 3, 1, 4, 1, 1, 1, 4, 4, 2]
def baseStart_3345591 : Nat := 118140960795 + 3345591 * 2 ^ 59
def prefixEnd_3345591 : Nat := 4983230072969 + 3 ^ 40 * 3345591 * 2
def baseEnd_3345591 : Nat := 1717896256356325093526413

theorem tailTrace_3345591 : CollatzResearch.WordTrace tailWord_3345591 prefixEnd_3345591 1717896256356325093526413 := by
  unfold tailWord_3345591
  simp only [CollatzResearch.WordTrace]
  refine ⟨122023728422502663297908627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81349152281668442198605751 122023728422502663297908627)
  ·
    refine ⟨183035592633753994946862941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122023728422502663297908627 183035592633753994946862941)
    ·
      refine ⟨68638347237657748105073603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 183035592633753994946862941 68638347237657748105073603)
      ·
        refine ⟨102957520856486622157610405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68638347237657748105073603 102957520856486622157610405)
        ·
          refine ⟨19304535160591241654551951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 102957520856486622157610405 19304535160591241654551951)
          ·
            refine ⟨28956802740886862481827927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19304535160591241654551951 28956802740886862481827927)
            ·
              refine ⟨43435204111330293722741891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28956802740886862481827927 43435204111330293722741891)
              ·
                refine ⟨65152806166995440584112837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43435204111330293722741891 65152806166995440584112837)
                ·
                  refine ⟨12216151156311645109521157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 65152806166995440584112837 12216151156311645109521157)
                  ·
                    refine ⟨2290528341808433458035217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12216151156311645109521157 2290528341808433458035217)
                    ·
                      refine ⟨1717896256356325093526413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2290528341808433458035217 1717896256356325093526413)
                      ·
                        rfl

theorem cell23_3345591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 1, 4, 4, 2].length) (baseStart_3345591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3345591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3345591 prefixEnd_3345591 := by exact prefixLift 3345591
  have htrace : WordTrace (prefixWord ++ tailWord_3345591) baseStart_3345591 baseEnd_3345591 := by
    simpa [prefixWord, tailWord_3345591, baseEnd_3345591] using wordTrace_append hprefix tailTrace_3345591
  have hstable : (prefixWord ++ tailWord_3345591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3345591).length < 2 ^ (prefixWord ++ tailWord_3345591).sum := by decide
  have hdescent : baseEnd_3345591 < baseStart_3345591 := by decide
  rcases family_descends (prefixWord ++ tailWord_3345591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3345664 : List Nat := [2, 1, 1, 2, 1, 1, 3, 1, 2, 5, 4]
def baseStart_3345664 : Nat := 118140960795 + 3345664 * 2 ^ 59
def prefixEnd_3345664 : Nat := 4983230072969 + 3 ^ 40 * 3345664 * 2
def baseEnd_3345664 : Nat := 1717933740444103307913577

theorem tailTrace_3345664 : CollatzResearch.WordTrace tailWord_3345664 prefixEnd_3345664 1717933740444103307913577 := by
  unfold tailWord_3345664
  simp only [CollatzResearch.WordTrace]
  refine ⟨61013195475619098382658023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81350927300825464510210697 61013195475619098382658023)
  ·
    refine ⟨91519793213428647573987035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61013195475619098382658023 91519793213428647573987035)
    ·
      refine ⟨137279689820142971360980553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91519793213428647573987035 137279689820142971360980553)
      ·
        refine ⟨102959767365107228520735415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137279689820142971360980553 102959767365107228520735415)
        ·
          refine ⟨154439651047660842781103123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102959767365107228520735415 154439651047660842781103123)
          ·
            refine ⟨231659476571491264171654685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154439651047660842781103123 231659476571491264171654685)
            ·
              refine ⟨86872303714309224064370507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 231659476571491264171654685 86872303714309224064370507)
              ·
                refine ⟨130308455571463836096555761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86872303714309224064370507 130308455571463836096555761)
                ·
                  refine ⟨97731341678597877072416821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 130308455571463836096555761 97731341678597877072416821)
                  ·
                    refine ⟨9162313282368550975539077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 97731341678597877072416821 9162313282368550975539077)
                    ·
                      refine ⟨1717933740444103307913577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9162313282368550975539077 1717933740444103307913577)
                      ·
                        rfl

theorem cell23_3345664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 1, 2, 5, 4].length) (baseStart_3345664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3345664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3345664 prefixEnd_3345664 := by exact prefixLift 3345664
  have htrace : WordTrace (prefixWord ++ tailWord_3345664) baseStart_3345664 baseEnd_3345664 := by
    simpa [prefixWord, tailWord_3345664, baseEnd_3345664] using wordTrace_append hprefix tailTrace_3345664
  have hstable : (prefixWord ++ tailWord_3345664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3345664).length < 2 ^ (prefixWord ++ tailWord_3345664).sum := by decide
  have hdescent : baseEnd_3345664 < baseStart_3345664 := by decide
  rcases family_descends (prefixWord ++ tailWord_3345664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3345678 : List Nat := [4, 1, 1, 2, 1, 3, 3, 2, 1, 5]
def baseStart_3345678 : Nat := 118140960795 + 3345678 * 2 ^ 59
def prefixEnd_3345678 : Nat := 4983230072969 + 3 ^ 40 * 3345678 * 2
def baseEnd_3345678 : Nat := 572646976391088751046171

theorem tailTrace_3345678 : CollatzResearch.WordTrace tailWord_3345678 prefixEnd_3345678 572646976391088751046171 := by
  unfold tailWord_3345678
  simp only [CollatzResearch.WordTrace]
  refine ⟨15253362696648434644540711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81351267715458318104217125 15253362696648434644540711)
  ·
    refine ⟨22880044044972651966811067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15253362696648434644540711 22880044044972651966811067)
    ·
      refine ⟨34320066067458977950216601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22880044044972651966811067 34320066067458977950216601)
      ·
        refine ⟨25740049550594233462662451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34320066067458977950216601 25740049550594233462662451)
        ·
          refine ⟨38610074325891350193993677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25740049550594233462662451 38610074325891350193993677)
          ·
            refine ⟨14478777872209256322747629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38610074325891350193993677 14478777872209256322747629)
            ·
              refine ⟨5429541702078471121030361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14478777872209256322747629 5429541702078471121030361)
              ·
                refine ⟨4072156276558853340772771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5429541702078471121030361 4072156276558853340772771)
                ·
                  refine ⟨6108234414838280011159157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4072156276558853340772771 6108234414838280011159157)
                  ·
                    refine ⟨572646976391088751046171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6108234414838280011159157 572646976391088751046171)
                    ·
                      rfl

theorem cell23_3345678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 3, 2, 1, 5].length) (baseStart_3345678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3345678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3345678 prefixEnd_3345678 := by exact prefixLift 3345678
  have htrace : WordTrace (prefixWord ++ tailWord_3345678) baseStart_3345678 baseEnd_3345678 := by
    simpa [prefixWord, tailWord_3345678, baseEnd_3345678] using wordTrace_append hprefix tailTrace_3345678
  have hstable : (prefixWord ++ tailWord_3345678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3345678).length < 2 ^ (prefixWord ++ tailWord_3345678).sum := by decide
  have hdescent : baseEnd_3345678 < baseStart_3345678 := by decide
  rcases family_descends (prefixWord ++ tailWord_3345678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3345681 : List Nat := [1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 4]
def baseStart_3345681 : Nat := 118140960795 + 3345681 * 2 ^ 59
def prefixEnd_3345681 : Nat := 4983230072969 + 3 ^ 40 * 3345681 * 2
def baseEnd_3345681 : Nat := 1717942469615229741400999

theorem tailTrace_3345681 : CollatzResearch.WordTrace tailWord_3345681 prefixEnd_3345681 1717942469615229741400999 := by
  unfold tailWord_3345681
  simp only [CollatzResearch.WordTrace]
  refine ⟨122027010992176608668684897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81351340661451072445789931 122027010992176608668684897)
  ·
    refine ⟨91520258244132456501513673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122027010992176608668684897 91520258244132456501513673)
    ·
      refine ⟨68640193683099342376135255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91520258244132456501513673 68640193683099342376135255)
      ·
        refine ⟨102960290524649013564202883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68640193683099342376135255 102960290524649013564202883)
        ·
          refine ⟨154440435786973520346304325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102960290524649013564202883 154440435786973520346304325)
          ·
            refine ⟨28957581710057535064932061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 154440435786973520346304325 28957581710057535064932061)
            ·
              refine ⟨10859093141271575649349523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28957581710057535064932061 10859093141271575649349523)
              ·
                refine ⟨16288639711907363474024285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10859093141271575649349523 16288639711907363474024285)
                ·
                  refine ⟨6108239891965261302759107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16288639711907363474024285 6108239891965261302759107)
                  ·
                    refine ⟨9162359837947891954138661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6108239891965261302759107 9162359837947891954138661)
                    ·
                      refine ⟨1717942469615229741400999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9162359837947891954138661 1717942469615229741400999)
                      ·
                        rfl

theorem cell23_3345681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 4].length) (baseStart_3345681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3345681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3345681 prefixEnd_3345681 := by exact prefixLift 3345681
  have htrace : WordTrace (prefixWord ++ tailWord_3345681) baseStart_3345681 baseEnd_3345681 := by
    simpa [prefixWord, tailWord_3345681, baseEnd_3345681] using wordTrace_append hprefix tailTrace_3345681
  have hstable : (prefixWord ++ tailWord_3345681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3345681).length < 2 ^ (prefixWord ++ tailWord_3345681).sum := by decide
  have hdescent : baseEnd_3345681 < baseStart_3345681 := by decide
  rcases family_descends (prefixWord ++ tailWord_3345681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3345695 : List Nat := [1, 1, 2, 4, 4, 1, 3, 1, 1, 5]
def baseStart_3345695 : Nat := 118140960795 + 3345695 * 2 ^ 59
def prefixEnd_3345695 : Nat := 4983230072969 + 3 ^ 40 * 3345695 * 2
def baseEnd_3345695 : Nat := 572649886114797562208645

theorem tailTrace_3345695 : CollatzResearch.WordTrace tailWord_3345695 prefixEnd_3345695 572649886114797562208645 := by
  unfold tailWord_3345695
  simp only [CollatzResearch.WordTrace]
  refine ⟨122027521614125889059694539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81351681076083926039796359 122027521614125889059694539)
  ·
    refine ⟨183041282421188833589541809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122027521614125889059694539 183041282421188833589541809)
    ·
      refine ⟨137280961815891625192156357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183041282421188833589541809 137280961815891625192156357)
      ·
        refine ⟨25740180340479679723529317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 137280961815891625192156357 25740180340479679723529317)
        ·
          refine ⟨4826283813839939948161747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25740180340479679723529317 4826283813839939948161747)
          ·
            refine ⟨7239425720759909922242621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4826283813839939948161747 7239425720759909922242621)
            ·
              refine ⟨2714784645284966220840983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7239425720759909922242621 2714784645284966220840983)
              ·
                refine ⟨4072176967927449331261475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2714784645284966220840983 4072176967927449331261475)
                ·
                  refine ⟨6108265451891173996892213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4072176967927449331261475 6108265451891173996892213)
                  ·
                    refine ⟨572649886114797562208645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6108265451891173996892213 572649886114797562208645)
                    ·
                      rfl

theorem cell23_3345695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 3, 1, 1, 5].length) (baseStart_3345695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3345695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3345695 prefixEnd_3345695 := by exact prefixLift 3345695
  have htrace : WordTrace (prefixWord ++ tailWord_3345695) baseStart_3345695 baseEnd_3345695 := by
    simpa [prefixWord, tailWord_3345695, baseEnd_3345695] using wordTrace_append hprefix tailTrace_3345695
  have hstable : (prefixWord ++ tailWord_3345695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3345695).length < 2 ^ (prefixWord ++ tailWord_3345695).sum := by decide
  have hdescent : baseEnd_3345695 < baseStart_3345695 := by decide
  rcases family_descends (prefixWord ++ tailWord_3345695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3345709 : List Nat := [1, 5, 3, 1, 1, 2, 1, 4, 1, 1, 3]
def baseStart_3345709 : Nat := 118140960795 + 3345709 * 2 ^ 59
def prefixEnd_3345709 : Nat := 4983230072969 + 3 ^ 40 * 3345709 * 2
def baseEnd_3345709 : Nat := 1717956847073555631850871

theorem tailTrace_3345709 : CollatzResearch.WordTrace tailWord_3345709 prefixEnd_3345709 1717956847073555631850871 := by
  unfold tailWord_3345709
  simp only [CollatzResearch.WordTrace]
  refine ⟨122028032236075169450704181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81352021490716779633802787 122028032236075169450704181)
  ·
    refine ⟨11440128022132047136003517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 122028032236075169450704181 11440128022132047136003517)
    ·
      refine ⟨4290048008299517676001319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11440128022132047136003517 4290048008299517676001319)
      ·
        refine ⟨6435072012449276514001979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4290048008299517676001319 6435072012449276514001979)
        ·
          refine ⟨9652608018673914771002969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6435072012449276514001979 9652608018673914771002969)
          ·
            refine ⟨7239456014005436078252227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9652608018673914771002969 7239456014005436078252227)
            ·
              refine ⟨10859184021008154117378341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7239456014005436078252227 10859184021008154117378341)
              ·
                refine ⟨2036097003939028897008439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10859184021008154117378341 2036097003939028897008439)
                ·
                  refine ⟨3054145505908543345512659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2036097003939028897008439 3054145505908543345512659)
                  ·
                    refine ⟨4581218258862815018268989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3054145505908543345512659 4581218258862815018268989)
                    ·
                      refine ⟨1717956847073555631850871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4581218258862815018268989 1717956847073555631850871)
                      ·
                        rfl

theorem cell23_3345709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 1, 4, 1, 1, 3].length) (baseStart_3345709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3345709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3345709 prefixEnd_3345709 := by exact prefixLift 3345709
  have htrace : WordTrace (prefixWord ++ tailWord_3345709) baseStart_3345709 baseEnd_3345709 := by
    simpa [prefixWord, tailWord_3345709, baseEnd_3345709] using wordTrace_append hprefix tailTrace_3345709
  have hstable : (prefixWord ++ tailWord_3345709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3345709).length < 2 ^ (prefixWord ++ tailWord_3345709).sum := by decide
  have hdescent : baseEnd_3345709 < baseStart_3345709 := by decide
  rcases family_descends (prefixWord ++ tailWord_3345709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3345725 : List Nat := [1, 4, 1, 5, 1, 1, 2, 1, 1, 6]
def baseStart_3345725 : Nat := 118140960795 + 3345725 * 2 ^ 59
def prefixEnd_3345725 : Nat := 4983230072969 + 3 ^ 40 * 3345725 * 2
def baseEnd_3345725 : Nat := 572655020921342523083599

theorem tailTrace_3345725 : CollatzResearch.WordTrace tailWord_3345725 prefixEnd_3345725 572655020921342523083599 := by
  unfold tailWord_3345725
  simp only [CollatzResearch.WordTrace]
  refine ⟨122028615804017204183286629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81352410536011469455524419 122028615804017204183286629)
  ·
    refine ⟨22880365463253225784366243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 122028615804017204183286629 22880365463253225784366243)
    ·
      refine ⟨34320548194879838676549365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22880365463253225784366243 34320548194879838676549365)
      ·
        refine ⟨3217551393269984875926503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 34320548194879838676549365 3217551393269984875926503)
        ·
          refine ⟨4826327089904977313889755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3217551393269984875926503 4826327089904977313889755)
          ·
            refine ⟨7239490634857465970834633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4826327089904977313889755 7239490634857465970834633)
            ·
              refine ⟨5429617976143099478125975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7239490634857465970834633 5429617976143099478125975)
              ·
                refine ⟨8144426964214649217188963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5429617976143099478125975 8144426964214649217188963)
                ·
                  refine ⟨12216640446321973825783445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8144426964214649217188963 12216640446321973825783445)
                  ·
                    refine ⟨572655020921342523083599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12216640446321973825783445 572655020921342523083599)
                    ·
                      rfl

theorem cell23_3345725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 2, 1, 1, 6].length) (baseStart_3345725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3345725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3345725 prefixEnd_3345725 := by exact prefixLift 3345725
  have htrace : WordTrace (prefixWord ++ tailWord_3345725) baseStart_3345725 baseEnd_3345725 := by
    simpa [prefixWord, tailWord_3345725, baseEnd_3345725] using wordTrace_append hprefix tailTrace_3345725
  have hstable : (prefixWord ++ tailWord_3345725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3345725).length < 2 ^ (prefixWord ++ tailWord_3345725).sum := by decide
  have hdescent : baseEnd_3345725 < baseStart_3345725 := by decide
  rcases family_descends (prefixWord ++ tailWord_3345725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3345732 : List Nat := [2, 3, 4, 1, 1, 1, 1, 1, 5, 2, 2]
def baseStart_3345732 : Nat := 118140960795 + 3345732 * 2 ^ 59
def prefixEnd_3345732 : Nat := 4983230072969 + 3 ^ 40 * 3345732 * 2
def baseEnd_3345732 : Nat := 1717968657128609041863265

theorem tailTrace_3345732 : CollatzResearch.WordTrace tailWord_3345732 prefixEnd_3345732 1717968657128609041863265 := by
  unfold tailWord_3345732
  simp only [CollatzResearch.WordTrace]
  refine ⟨61014435557495922189395725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81352580743327896252527633 61014435557495922189395725)
  ·
    refine ⟨22880413334060970821023397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61014435557495922189395725 22880413334060970821023397)
    ·
      refine ⟨4290077500136432028941887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22880413334060970821023397 4290077500136432028941887)
      ·
        refine ⟨6435116250204648043412831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4290077500136432028941887 6435116250204648043412831)
        ·
          refine ⟨9652674375306972065119247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6435116250204648043412831 9652674375306972065119247)
          ·
            refine ⟨14479011562960458097678871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9652674375306972065119247 14479011562960458097678871)
            ·
              refine ⟨21718517344440687146518307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14479011562960458097678871 21718517344440687146518307)
              ·
                refine ⟨32577776016661030719777461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21718517344440687146518307 32577776016661030719777461)
                ·
                  refine ⟨3054166501561971629979137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 32577776016661030719777461 3054166501561971629979137)
                  ·
                    refine ⟨2290624876171478722484353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3054166501561971629979137 2290624876171478722484353)
                    ·
                      refine ⟨1717968657128609041863265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2290624876171478722484353 1717968657128609041863265)
                      ·
                        rfl

theorem cell23_3345732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 1, 5, 2, 2].length) (baseStart_3345732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3345732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3345732 prefixEnd_3345732 := by exact prefixLift 3345732
  have htrace : WordTrace (prefixWord ++ tailWord_3345732) baseStart_3345732 baseEnd_3345732 := by
    simpa [prefixWord, tailWord_3345732, baseEnd_3345732] using wordTrace_append hprefix tailTrace_3345732
  have hstable : (prefixWord ++ tailWord_3345732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3345732).length < 2 ^ (prefixWord ++ tailWord_3345732).sum := by decide
  have hdescent : baseEnd_3345732 < baseStart_3345732 := by decide
  rcases family_descends (prefixWord ++ tailWord_3345732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3345748 : List Nat := [2, 4, 1, 1, 2, 1, 1, 4, 1, 3, 3]
def baseStart_3345748 : Nat := 118140960795 + 3345748 * 2 ^ 59
def prefixEnd_3345748 : Nat := 4983230072969 + 3 ^ 40 * 3345748 * 2
def baseEnd_3345748 : Nat := 1717976872819080979263191

theorem tailTrace_3345748 : CollatzResearch.WordTrace tailWord_3345748 prefixEnd_3345748 1717976872819080979263191 := by
  unfold tailWord_3345748
  simp only [CollatzResearch.WordTrace]
  refine ⟨61014727341466939555686949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81352969788622586074249265 61014727341466939555686949)
  ·
    refine ⟨11440261376525051166691303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61014727341466939555686949 11440261376525051166691303)
    ·
      refine ⟨17160392064787576750036955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11440261376525051166691303 17160392064787576750036955)
      ·
        refine ⟨25740588097181365125055433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17160392064787576750036955 25740588097181365125055433)
        ·
          refine ⟨19305441072886023843791575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25740588097181365125055433 19305441072886023843791575)
          ·
            refine ⟨28958161609329035765687363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19305441072886023843791575 28958161609329035765687363)
            ·
              refine ⟨43437242413993553648531045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28958161609329035765687363 43437242413993553648531045)
              ·
                refine ⟨8144482952623791309099571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43437242413993553648531045 8144482952623791309099571)
                ·
                  refine ⟨12216724428935686963649357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8144482952623791309099571 12216724428935686963649357)
                  ·
                    refine ⟨4581271660850882611368509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12216724428935686963649357 4581271660850882611368509)
                    ·
                      refine ⟨1717976872819080979263191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4581271660850882611368509 1717976872819080979263191)
                      ·
                        rfl

theorem cell23_3345748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 4, 1, 3, 3].length) (baseStart_3345748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3345748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3345748 prefixEnd_3345748 := by exact prefixLift 3345748
  have htrace : WordTrace (prefixWord ++ tailWord_3345748) baseStart_3345748 baseEnd_3345748 := by
    simpa [prefixWord, tailWord_3345748, baseEnd_3345748] using wordTrace_append hprefix tailTrace_3345748
  have hstable : (prefixWord ++ tailWord_3345748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3345748).length < 2 ^ (prefixWord ++ tailWord_3345748).sum := by decide
  have hdescent : baseEnd_3345748 < baseStart_3345748 := by decide
  rcases family_descends (prefixWord ++ tailWord_3345748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3345749 : List Nat := [1, 3, 2, 2, 3, 2, 2, 3, 1, 2, 2]
def baseStart_3345749 : Nat := 118140960795 + 3345749 * 2 ^ 59
def prefixEnd_3345749 : Nat := 4983230072969 + 3 ^ 40 * 3345749 * 2
def baseEnd_3345749 : Nat := 1717977386299735475350687

theorem tailTrace_3345749 : CollatzResearch.WordTrace tailWord_3345749 prefixEnd_3345749 1717977386299735475350687 := by
  unfold tailWord_3345749
  simp only [CollatzResearch.WordTrace]
  refine ⟨122029491155930256282160301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81352994103953504188106867 122029491155930256282160301)
  ·
    refine ⟨45761059183473846105810113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122029491155930256282160301 45761059183473846105810113)
    ·
      refine ⟨34320794387605384579357585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45761059183473846105810113 34320794387605384579357585)
      ·
        refine ⟨25740595790704038434518189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34320794387605384579357585 25740595790704038434518189)
        ·
          refine ⟨9652723421514014412944321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25740595790704038434518189 9652723421514014412944321)
          ·
            refine ⟨7239542566135510809708241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9652723421514014412944321 7239542566135510809708241)
            ·
              refine ⟨5429656924601633107281181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7239542566135510809708241 5429656924601633107281181)
              ·
                refine ⟨2036121346725612415230443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5429656924601633107281181 2036121346725612415230443)
                ·
                  refine ⟨3054182020088418622845665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2036121346725612415230443 3054182020088418622845665)
                  ·
                    refine ⟨2290636515066313967134249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3054182020088418622845665 2290636515066313967134249)
                    ·
                      refine ⟨1717977386299735475350687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2290636515066313967134249 1717977386299735475350687)
                      ·
                        rfl

theorem cell23_3345749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 2, 3, 1, 2, 2].length) (baseStart_3345749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3345749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3345749 prefixEnd_3345749 := by exact prefixLift 3345749
  have htrace : WordTrace (prefixWord ++ tailWord_3345749) baseStart_3345749 baseEnd_3345749 := by
    simpa [prefixWord, tailWord_3345749, baseEnd_3345749] using wordTrace_append hprefix tailTrace_3345749
  have hstable : (prefixWord ++ tailWord_3345749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3345749).length < 2 ^ (prefixWord ++ tailWord_3345749).sum := by decide
  have hdescent : baseEnd_3345749 < baseStart_3345749 := by decide
  rcases family_descends (prefixWord ++ tailWord_3345749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3345868 : List Nat := [2, 2, 1, 4, 2, 1, 1, 2, 1, 2, 5]
def baseStart_3345868 : Nat := 118140960795 + 3345868 * 2 ^ 59
def prefixEnd_3345868 : Nat := 4983230072969 + 3 ^ 40 * 3345868 * 2
def baseEnd_3345868 : Nat := 1718038490497620509762639

theorem tailTrace_3345868 : CollatzResearch.WordTrace tailWord_3345868 prefixEnd_3345868 1718038490497620509762639 := by
  unfold tailWord_3345868
  simp only [CollatzResearch.WordTrace]
  refine ⟨61016915721249569802871129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81355887628332759737161505 61016915721249569802871129)
  ·
    refine ⟨45762686790937177352153347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61016915721249569802871129 45762686790937177352153347)
    ·
      refine ⟨68644030186405766028230021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45762686790937177352153347 68644030186405766028230021)
      ·
        refine ⟨12870755659951081130293129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 68644030186405766028230021 12870755659951081130293129)
        ·
          refine ⟨9653066744963310847719847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12870755659951081130293129 9653066744963310847719847)
          ·
            refine ⟨14479600117444966271579771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9653066744963310847719847 14479600117444966271579771)
            ·
              refine ⟨21719400176167449407369657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14479600117444966271579771 21719400176167449407369657)
              ·
                refine ⟨16289550132125587055527243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21719400176167449407369657 16289550132125587055527243)
                ·
                  refine ⟨24434325198188380583290865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16289550132125587055527243 24434325198188380583290865)
                  ·
                    refine ⟨18325743898641285437468149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24434325198188380583290865 18325743898641285437468149)
                    ·
                      refine ⟨1718038490497620509762639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18325743898641285437468149 1718038490497620509762639)
                      ·
                        rfl

theorem cell23_3345868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 2, 1, 2, 5].length) (baseStart_3345868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3345868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3345868 prefixEnd_3345868 := by exact prefixLift 3345868
  have htrace : WordTrace (prefixWord ++ tailWord_3345868) baseStart_3345868 baseEnd_3345868 := by
    simpa [prefixWord, tailWord_3345868, baseEnd_3345868] using wordTrace_append hprefix tailTrace_3345868
  have hstable : (prefixWord ++ tailWord_3345868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3345868).length < 2 ^ (prefixWord ++ tailWord_3345868).sum := by decide
  have hdescent : baseEnd_3345868 < baseStart_3345868 := by decide
  rcases family_descends (prefixWord ++ tailWord_3345868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3345895 : List Nat := [1, 1, 5, 2, 1, 2, 1, 1, 1, 6, 2]
def baseStart_3345895 : Nat := 118140960795 + 3345895 * 2 ^ 59
def prefixEnd_3345895 : Nat := 4983230072969 + 3 ^ 40 * 3345895 * 2
def baseEnd_3345895 : Nat := 1718052354475291904125015

theorem tailTrace_3345895 : CollatzResearch.WordTrace tailWord_3345895 prefixEnd_3345895 1718052354475291904125015 := by
  unfold tailWord_3345895
  simp only [CollatzResearch.WordTrace]
  refine ⟨122034816213401323216975139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81356544142267548811316759 122034816213401323216975139)
  ·
    refine ⟨183052224320101984825462709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122034816213401323216975139 183052224320101984825462709)
    ·
      refine ⟨17161146030009561077387129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 183052224320101984825462709 17161146030009561077387129)
      ·
        refine ⟨12870859522507170808040347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17161146030009561077387129 12870859522507170808040347)
        ·
          refine ⟨19306289283760756212060521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12870859522507170808040347 19306289283760756212060521)
          ·
            refine ⟨14479716962820567159045391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19306289283760756212060521 14479716962820567159045391)
            ·
              refine ⟨21719575444230850738568087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14479716962820567159045391 21719575444230850738568087)
              ·
                refine ⟨32579363166346276107852131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21719575444230850738568087 32579363166346276107852131)
                ·
                  refine ⟨48869044749519414161778197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32579363166346276107852131 48869044749519414161778197)
                  ·
                    refine ⟨2290736472633722538833353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 48869044749519414161778197 2290736472633722538833353)
                    ·
                      refine ⟨1718052354475291904125015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2290736472633722538833353 1718052354475291904125015)
                      ·
                        rfl

theorem cell23_3345895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 1, 1, 6, 2].length) (baseStart_3345895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3345895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3345895 prefixEnd_3345895 := by exact prefixLift 3345895
  have htrace : WordTrace (prefixWord ++ tailWord_3345895) baseStart_3345895 baseEnd_3345895 := by
    simpa [prefixWord, tailWord_3345895, baseEnd_3345895] using wordTrace_append hprefix tailTrace_3345895
  have hstable : (prefixWord ++ tailWord_3345895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3345895).length < 2 ^ (prefixWord ++ tailWord_3345895).sum := by decide
  have hdescent : baseEnd_3345895 < baseStart_3345895 := by decide
  rcases family_descends (prefixWord ++ tailWord_3345895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3345905 : List Nat := [1, 2, 2, 2, 3, 3, 1, 2, 3, 4]
def baseStart_3345905 : Nat := 118140960795 + 3345905 * 2 ^ 59
def prefixEnd_3345905 : Nat := 4983230072969 + 3 ^ 40 * 3345905 * 2
def baseEnd_3345905 : Nat := 572685829760612288333323

theorem tailTrace_3345905 : CollatzResearch.WordTrace tailWord_3345905 prefixEnd_3345905 572685829760612288333323 := by
  unfold tailWord_3345905
  simp only [CollatzResearch.WordTrace]
  refine ⟨122035180943365094924839169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81356787295576729949892779 122035180943365094924839169)
  ·
    refine ⟨91526385707523821193629377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122035180943365094924839169 91526385707523821193629377)
    ·
      refine ⟨68644789280642865895222033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91526385707523821193629377 68644789280642865895222033)
      ·
        refine ⟨51483591960482149421416525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68644789280642865895222033 51483591960482149421416525)
        ·
          refine ⟨19306346985180806033031197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51483591960482149421416525 19306346985180806033031197)
          ·
            refine ⟨7239880119442802262386699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19306346985180806033031197 7239880119442802262386699)
            ·
              refine ⟨10859820179164203393580049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7239880119442802262386699 10859820179164203393580049)
              ·
                refine ⟨8144865134373152545185037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10859820179164203393580049 8144865134373152545185037)
                ·
                  refine ⟨3054324425389932204444389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8144865134373152545185037 3054324425389932204444389)
                  ·
                    refine ⟨572685829760612288333323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3054324425389932204444389 572685829760612288333323)
                    ·
                      rfl

theorem cell23_3345905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 1, 2, 3, 4].length) (baseStart_3345905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3345905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3345905 prefixEnd_3345905 := by exact prefixLift 3345905
  have htrace : WordTrace (prefixWord ++ tailWord_3345905) baseStart_3345905 baseEnd_3345905 := by
    simpa [prefixWord, tailWord_3345905, baseEnd_3345905] using wordTrace_append hprefix tailTrace_3345905
  have hstable : (prefixWord ++ tailWord_3345905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3345905).length < 2 ^ (prefixWord ++ tailWord_3345905).sum := by decide
  have hdescent : baseEnd_3345905 < baseStart_3345905 := by decide
  rcases family_descends (prefixWord ++ tailWord_3345905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3345952 : List Nat := [2, 1, 1, 6, 1, 2, 3, 1, 6]
def baseStart_3345952 : Nat := 118140960795 + 3345952 * 2 ^ 59
def prefixEnd_3345952 : Nat := 4983230072969 + 3 ^ 40 * 3345952 * 2
def baseEnd_3345952 : Nat := 190897958096955353456917

theorem tailTrace_3345952 : CollatzResearch.WordTrace tailWord_3345952 prefixEnd_3345952 190897958096955353456917 := by
  unfold tailWord_3345952
  simp only [CollatzResearch.WordTrace]
  refine ⟨61018447587097410975900055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81357930116129881301200073 61018447587097410975900055)
  ·
    refine ⟨91527671380646116463850083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61018447587097410975900055 91527671380646116463850083)
    ·
      refine ⟨137291507070969174695775125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91527671380646116463850083 137291507070969174695775125)
      ·
        refine ⟨6435539393951680063864459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 137291507070969174695775125 6435539393951680063864459)
        ·
          refine ⟨9653309090927520095796689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6435539393951680063864459 9653309090927520095796689)
          ·
            refine ⟨7239981818195640071847517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9653309090927520095796689 7239981818195640071847517)
            ·
              refine ⟨2714993181823365026942819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7239981818195640071847517 2714993181823365026942819)
              ·
                refine ⟨4072489772735047540414229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2714993181823365026942819 4072489772735047540414229)
                ·
                  refine ⟨190897958096955353456917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4072489772735047540414229 190897958096955353456917)
                  ·
                    rfl

theorem cell23_3345952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 3, 1, 6].length) (baseStart_3345952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3345952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3345952 prefixEnd_3345952 := by exact prefixLift 3345952
  have htrace : WordTrace (prefixWord ++ tailWord_3345952) baseStart_3345952 baseEnd_3345952 := by
    simpa [prefixWord, tailWord_3345952, baseEnd_3345952] using wordTrace_append hprefix tailTrace_3345952
  have hstable : (prefixWord ++ tailWord_3345952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3345952).length < 2 ^ (prefixWord ++ tailWord_3345952).sum := by decide
  have hdescent : baseEnd_3345952 < baseStart_3345952 := by decide
  rcases family_descends (prefixWord ++ tailWord_3345952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3345962 : List Nat := [3, 1, 4, 1, 1, 1, 1, 4, 3, 1, 3]
def baseStart_3345962 : Nat := 118140960795 + 3345962 * 2 ^ 59
def prefixEnd_3345962 : Nat := 4983230072969 + 3 ^ 40 * 3345962 * 2
def baseEnd_3345962 : Nat := 1718086757679143141987207

theorem tailTrace_3345962 : CollatzResearch.WordTrace tailWord_3345962 prefixEnd_3345962 1718086757679143141987207 := by
  unfold tailWord_3345962
  simp only [CollatzResearch.WordTrace]
  refine ⟨30509314976039648414916035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81358173269439062439776093 30509314976039648414916035)
  ·
    refine ⟨45763972464059472622374053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30509314976039648414916035 45763972464059472622374053)
    ·
      refine ⟨8580744837011151116695135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45763972464059472622374053 8580744837011151116695135)
      ·
        refine ⟨12871117255516726675042703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8580744837011151116695135 12871117255516726675042703)
        ·
          refine ⟨19306675883275090012564055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12871117255516726675042703 19306675883275090012564055)
          ·
            refine ⟨28960013824912635018846083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19306675883275090012564055 28960013824912635018846083)
            ·
              refine ⟨43440020737368952528269125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28960013824912635018846083 43440020737368952528269125)
              ·
                refine ⟨8145003888256678599050461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43440020737368952528269125 8145003888256678599050461)
                ·
                  refine ⟨3054376458096254474643923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8145003888256678599050461 3054376458096254474643923)
                  ·
                    refine ⟨4581564687144381711965885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3054376458096254474643923 4581564687144381711965885)
                    ·
                      refine ⟨1718086757679143141987207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4581564687144381711965885 1718086757679143141987207)
                      ·
                        rfl

theorem cell23_3345962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 4, 3, 1, 3].length) (baseStart_3345962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3345962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3345962 prefixEnd_3345962 := by exact prefixLift 3345962
  have htrace : WordTrace (prefixWord ++ tailWord_3345962) baseStart_3345962 baseEnd_3345962 := by
    simpa [prefixWord, tailWord_3345962, baseEnd_3345962] using wordTrace_append hprefix tailTrace_3345962
  have hstable : (prefixWord ++ tailWord_3345962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3345962).length < 2 ^ (prefixWord ++ tailWord_3345962).sum := by decide
  have hdescent : baseEnd_3345962 < baseStart_3345962 := by decide
  rcases family_descends (prefixWord ++ tailWord_3345962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3345978 : List Nat := [3, 1, 1, 1, 3, 2, 2, 1, 3, 6]
def baseStart_3345978 : Nat := 118140960795 + 3345978 * 2 ^ 59
def prefixEnd_3345978 : Nat := 4983230072969 + 3 ^ 40 * 3345978 * 2
def baseEnd_3345978 : Nat := 572698324456538359795711

theorem tailTrace_3345978 : CollatzResearch.WordTrace tailWord_3345978 prefixEnd_3345978 572698324456538359795711 := by
  unfold tailWord_3345978
  simp only [CollatzResearch.WordTrace]
  refine ⟨30509460868025157098061647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81358562314733752261497725 30509460868025157098061647)
  ·
    refine ⟨45764191302037735647092471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30509460868025157098061647 45764191302037735647092471)
    ·
      refine ⟨68646286953056603470638707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45764191302037735647092471 68646286953056603470638707)
      ·
        refine ⟨102969430429584905205958061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68646286953056603470638707 102969430429584905205958061)
        ·
          refine ⟨38613536411094339452234273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102969430429584905205958061 38613536411094339452234273)
          ·
            refine ⟨28960152308320754589175705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38613536411094339452234273 28960152308320754589175705)
            ·
              refine ⟨21720114231240565941881779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28960152308320754589175705 21720114231240565941881779)
              ·
                refine ⟨32580171346860848912822669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21720114231240565941881779 32580171346860848912822669)
                ·
                  refine ⟨12217564255072818342308501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32580171346860848912822669 12217564255072818342308501)
                  ·
                    refine ⟨572698324456538359795711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12217564255072818342308501 572698324456538359795711)
                    ·
                      rfl

theorem cell23_3345978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 1, 3, 6].length) (baseStart_3345978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3345978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3345978 prefixEnd_3345978 := by exact prefixLift 3345978
  have htrace : WordTrace (prefixWord ++ tailWord_3345978) baseStart_3345978 baseEnd_3345978 := by
    simpa [prefixWord, tailWord_3345978, baseEnd_3345978] using wordTrace_append hprefix tailTrace_3345978
  have hstable : (prefixWord ++ tailWord_3345978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3345978).length < 2 ^ (prefixWord ++ tailWord_3345978).sum := by decide
  have hdescent : baseEnd_3345978 < baseStart_3345978 := by decide
  rcases family_descends (prefixWord ++ tailWord_3345978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3345995 : List Nat := [1, 1, 1, 1, 3, 1, 3, 6, 2, 4]
def baseStart_3345995 : Nat := 118140960795 + 3345995 * 2 ^ 59
def prefixEnd_3345995 : Nat := 4983230072969 + 3 ^ 40 * 3345995 * 2
def baseEnd_3345995 : Nat := 572701234180247170958185

theorem tailTrace_3345995 : CollatzResearch.WordTrace tailWord_3345995 prefixEnd_3345995 572701234180247170958185 := by
  unfold tailWord_3345995
  simp only [CollatzResearch.WordTrace]
  refine ⟨122038463513039040295615439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81358975675359360197076959 122038463513039040295615439)
  ·
    refine ⟨183057695269558560443423159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122038463513039040295615439 183057695269558560443423159)
    ·
      refine ⟨274586542904337840665134739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183057695269558560443423159 274586542904337840665134739)
      ·
        refine ⟨411879814356506760997702109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 274586542904337840665134739 411879814356506760997702109)
        ·
          refine ⟨154454930383690035374138291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 411879814356506760997702109 154454930383690035374138291)
          ·
            refine ⟨231682395575535053061207437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154454930383690035374138291 231682395575535053061207437)
            ·
              refine ⟨86880898340825644897952789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 231682395575535053061207437 86880898340825644897952789)
              ·
                refine ⟨4072542109726202104591537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 86880898340825644897952789 4072542109726202104591537)
                ·
                  refine ⟨3054406582294651578443653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4072542109726202104591537 3054406582294651578443653)
                  ·
                    refine ⟨572701234180247170958185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3054406582294651578443653 572701234180247170958185)
                    ·
                      rfl

theorem cell23_3345995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 6, 2, 4].length) (baseStart_3345995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3345995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3345995 prefixEnd_3345995 := by exact prefixLift 3345995
  have htrace : WordTrace (prefixWord ++ tailWord_3345995) baseStart_3345995 baseEnd_3345995 := by
    simpa [prefixWord, tailWord_3345995, baseEnd_3345995] using wordTrace_append hprefix tailTrace_3345995
  have hstable : (prefixWord ++ tailWord_3345995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3345995).length < 2 ^ (prefixWord ++ tailWord_3345995).sum := by decide
  have hdescent : baseEnd_3345995 < baseStart_3345995 := by decide
  rcases family_descends (prefixWord ++ tailWord_3345995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3345996 : List Nat := [2, 2, 1, 3, 1, 4, 3, 2, 1, 1, 3]
def baseStart_3345996 : Nat := 118140960795 + 3345996 * 2 ^ 59
def prefixEnd_3345996 : Nat := 4983230072969 + 3 ^ 40 * 3345996 * 2
def baseEnd_3345996 : Nat := 1718104216021396008962051

theorem tailTrace_3345996 : CollatzResearch.WordTrace tailWord_3345996 prefixEnd_3345996 1718104216021396008962051 := by
  unfold tailWord_3345996
  simp only [CollatzResearch.WordTrace]
  refine ⟨61019249993017708733200921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81358999990690278310934561 61019249993017708733200921)
  ·
    refine ⟨45764437494763281549900691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61019249993017708733200921 45764437494763281549900691)
    ·
      refine ⟨68646656242144922324851037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45764437494763281549900691 68646656242144922324851037)
      ·
        refine ⟨25742496090804345871819139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68646656242144922324851037 25742496090804345871819139)
        ·
          refine ⟨38613744136206518807728709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25742496090804345871819139 38613744136206518807728709)
          ·
            refine ⟨7240077025538722276449133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38613744136206518807728709 7240077025538722276449133)
            ·
              refine ⟨2715028884577020853668425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7240077025538722276449133 2715028884577020853668425)
              ·
                refine ⟨2036271663432765640251319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2715028884577020853668425 2036271663432765640251319)
                ·
                  refine ⟨3054407495149148460376979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2036271663432765640251319 3054407495149148460376979)
                  ·
                    refine ⟨4581611242723722690565469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3054407495149148460376979 4581611242723722690565469)
                    ·
                      refine ⟨1718104216021396008962051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4581611242723722690565469 1718104216021396008962051)
                      ·
                        rfl

theorem cell23_3345996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 3, 2, 1, 1, 3].length) (baseStart_3345996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3345996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3345996 prefixEnd_3345996 := by exact prefixLift 3345996
  have htrace : WordTrace (prefixWord ++ tailWord_3345996) baseStart_3345996 baseEnd_3345996 := by
    simpa [prefixWord, tailWord_3345996, baseEnd_3345996] using wordTrace_append hprefix tailTrace_3345996
  have hstable : (prefixWord ++ tailWord_3345996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3345996).length < 2 ^ (prefixWord ++ tailWord_3345996).sum := by decide
  have hdescent : baseEnd_3345996 < baseStart_3345996 := by decide
  rcases family_descends (prefixWord ++ tailWord_3345996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3346005 : List Nat := [1, 3, 2, 2, 1, 1, 1, 4, 3, 2, 3]
def baseStart_3346005 : Nat := 118140960795 + 3346005 * 2 ^ 59
def prefixEnd_3346005 : Nat := 4983230072969 + 3 ^ 40 * 3346005 * 2
def baseEnd_3346005 : Nat := 1718108837347286473749509

theorem tailTrace_3346005 : CollatzResearch.WordTrace tailWord_3346005 prefixEnd_3346005 1718108837347286473749509 := by
  unfold tailWord_3346005
  simp only [CollatzResearch.WordTrace]
  refine ⟨122038828243002812003479469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81359218828668541335652979 122038828243002812003479469)
  ·
    refine ⟨45764560591126054501304801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122038828243002812003479469 45764560591126054501304801)
    ·
      refine ⟨34323420443344540875978601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45764560591126054501304801 34323420443344540875978601)
      ·
        refine ⟨25742565332508405656983951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34323420443344540875978601 25742565332508405656983951)
        ·
          refine ⟨38613847998762608485475927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25742565332508405656983951 38613847998762608485475927)
          ·
            refine ⟨57920771998143912728213891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38613847998762608485475927 57920771998143912728213891)
            ·
              refine ⟨86881157997215869092320837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57920771998143912728213891 86881157997215869092320837)
              ·
                refine ⟨16290217124477975454810157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 86881157997215869092320837 16290217124477975454810157)
                ·
                  refine ⟨6108831421679240795553809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16290217124477975454810157 6108831421679240795553809)
                  ·
                    refine ⟨4581623566259430596665357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6108831421679240795553809 4581623566259430596665357)
                    ·
                      refine ⟨1718108837347286473749509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4581623566259430596665357 1718108837347286473749509)
                      ·
                        rfl

theorem cell23_3346005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 4, 3, 2, 3].length) (baseStart_3346005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3346005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3346005 prefixEnd_3346005 := by exact prefixLift 3346005
  have htrace : WordTrace (prefixWord ++ tailWord_3346005) baseStart_3346005 baseEnd_3346005 := by
    simpa [prefixWord, tailWord_3346005, baseEnd_3346005] using wordTrace_append hprefix tailTrace_3346005
  have hstable : (prefixWord ++ tailWord_3346005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3346005).length < 2 ^ (prefixWord ++ tailWord_3346005).sum := by decide
  have hdescent : baseEnd_3346005 < baseStart_3346005 := by decide
  rcases family_descends (prefixWord ++ tailWord_3346005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3346075 : List Nat := [1, 1, 1, 1, 1, 1, 2, 2, 1, 10, 2]
def baseStart_3346075 : Nat := 118140960795 + 3346075 * 2 ^ 59
def prefixEnd_3346075 : Nat := 4983230072969 + 3 ^ 40 * 3346075 * 2
def baseEnd_3346075 : Nat := 1718144780993101199874187

theorem tailTrace_3346075 : CollatzResearch.WordTrace tailWord_3346075 prefixEnd_3346075 1718144780993101199874187 := by
  unfold tailWord_3346075
  simp only [CollatzResearch.WordTrace]
  refine ⟨122041381352749213958527679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81360920901832809305685119 122041381352749213958527679)
  ·
    refine ⟨183062072029123820937791519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122041381352749213958527679 183062072029123820937791519)
    ·
      refine ⟨274593108043685731406687279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183062072029123820937791519 274593108043685731406687279)
      ·
        refine ⟨411889662065528597110030919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 274593108043685731406687279 411889662065528597110030919)
        ·
          refine ⟨617834493098292895665046379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 411889662065528597110030919 617834493098292895665046379)
          ·
            refine ⟨926751739647439343497569569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 617834493098292895665046379 926751739647439343497569569)
            ·
              refine ⟨695063804735579507623177177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 926751739647439343497569569 695063804735579507623177177)
              ·
                refine ⟨521297853551684630717382883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 695063804735579507623177177 521297853551684630717382883)
                ·
                  refine ⟨781946780327526946076074325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 521297853551684630717382883 781946780327526946076074325)
                  ·
                    refine ⟨2290859707990801599832249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 781946780327526946076074325 2290859707990801599832249)
                    ·
                      refine ⟨1718144780993101199874187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2290859707990801599832249 1718144780993101199874187)
                      ·
                        rfl

theorem cell23_3346075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 10, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 10, 2].length) (baseStart_3346075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3346075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3346075 prefixEnd_3346075 := by exact prefixLift 3346075
  have htrace : WordTrace (prefixWord ++ tailWord_3346075) baseStart_3346075 baseEnd_3346075 := by
    simpa [prefixWord, tailWord_3346075, baseEnd_3346075] using wordTrace_append hprefix tailTrace_3346075
  have hstable : (prefixWord ++ tailWord_3346075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3346075).length < 2 ^ (prefixWord ++ tailWord_3346075).sum := by decide
  have hdescent : baseEnd_3346075 < baseStart_3346075 := by decide
  rcases family_descends (prefixWord ++ tailWord_3346075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3346105 : List Nat := [1, 2, 1, 4, 1, 1, 3, 2, 2, 2, 4]
def baseStart_3346105 : Nat := 118140960795 + 3346105 * 2 ^ 59
def prefixEnd_3346105 : Nat := 4983230072969 + 3 ^ 40 * 3346105 * 2
def baseEnd_3346105 : Nat := 1718160185412736082499049

theorem tailTrace_3346105 : CollatzResearch.WordTrace tailWord_3346105 prefixEnd_3346105 1718160185412736082499049 := by
  unfold tailWord_3346105
  simp only [CollatzResearch.WordTrace]
  refine ⟨122042475542640529082119769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81361650361760352721413179 122042475542640529082119769)
  ·
    refine ⟨91531856656980396811589827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122042475542640529082119769 91531856656980396811589827)
    ·
      refine ⟨137297784985470595217384741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91531856656980396811589827 137297784985470595217384741)
      ·
        refine ⟨25743334684775736603259639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 137297784985470595217384741 25743334684775736603259639)
        ·
          refine ⟨38615002027163604904889459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25743334684775736603259639 38615002027163604904889459)
          ·
            refine ⟨57922503040745407357334189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38615002027163604904889459 57922503040745407357334189)
            ·
              refine ⟨21720938640279527759000321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57922503040745407357334189 21720938640279527759000321)
              ·
                refine ⟨16290703980209645819250241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21720938640279527759000321 16290703980209645819250241)
                ·
                  refine ⟨12218027985157234364437681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16290703980209645819250241 12218027985157234364437681)
                  ·
                    refine ⟨9163520988867925773328261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12218027985157234364437681 9163520988867925773328261)
                    ·
                      refine ⟨1718160185412736082499049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9163520988867925773328261 1718160185412736082499049)
                      ·
                        rfl

theorem cell23_3346105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 2, 2, 2, 4].length) (baseStart_3346105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3346105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3346105 prefixEnd_3346105 := by exact prefixLift 3346105
  have htrace : WordTrace (prefixWord ++ tailWord_3346105) baseStart_3346105 baseEnd_3346105 := by
    simpa [prefixWord, tailWord_3346105, baseEnd_3346105] using wordTrace_append hprefix tailTrace_3346105
  have hstable : (prefixWord ++ tailWord_3346105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3346105).length < 2 ^ (prefixWord ++ tailWord_3346105).sum := by decide
  have hdescent : baseEnd_3346105 < baseStart_3346105 := by decide
  rcases family_descends (prefixWord ++ tailWord_3346105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3346109 : List Nat := [1, 4, 1, 2, 1, 2, 3, 1, 4, 2, 2]
def baseStart_3346109 : Nat := 118140960795 + 3346109 * 2 ^ 59
def prefixEnd_3346109 : Nat := 4983230072969 + 3 ^ 40 * 3346109 * 2
def baseEnd_3346109 : Nat := 1718162239335354066849031

theorem tailTrace_3346109 : CollatzResearch.WordTrace tailWord_3346109 prefixEnd_3346109 1718162239335354066849031 := by
  unfold tailWord_3346109
  simp only [CollatzResearch.WordTrace]
  refine ⟨122042621434626037765265381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81361747623084025176843587 122042621434626037765265381)
  ·
    refine ⟨22882991518992382080987259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 122042621434626037765265381 22882991518992382080987259)
    ·
      refine ⟨34324487278488573121480889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22882991518992382080987259 34324487278488573121480889)
      ·
        refine ⟨25743365458866429841110667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34324487278488573121480889 25743365458866429841110667)
        ·
          refine ⟨38615048188299644761666001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25743365458866429841110667 38615048188299644761666001)
          ·
            refine ⟨28961286141224733571249501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38615048188299644761666001 28961286141224733571249501)
            ·
              refine ⟨10860482302959275089218563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28961286141224733571249501 10860482302959275089218563)
              ·
                refine ⟨16290723454438912633827845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10860482302959275089218563 16290723454438912633827845)
                ·
                  refine ⟨3054510647707296118842721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16290723454438912633827845 3054510647707296118842721)
                  ·
                    refine ⟨2290882985780472089132041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3054510647707296118842721 2290882985780472089132041)
                    ·
                      refine ⟨1718162239335354066849031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2290882985780472089132041 1718162239335354066849031)
                      ·
                        rfl

theorem cell23_3346109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 3, 1, 4, 2, 2].length) (baseStart_3346109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3346109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3346109 prefixEnd_3346109 := by exact prefixLift 3346109
  have htrace : WordTrace (prefixWord ++ tailWord_3346109) baseStart_3346109 baseEnd_3346109 := by
    simpa [prefixWord, tailWord_3346109, baseEnd_3346109] using wordTrace_append hprefix tailTrace_3346109
  have hstable : (prefixWord ++ tailWord_3346109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3346109).length < 2 ^ (prefixWord ++ tailWord_3346109).sum := by decide
  have hdescent : baseEnd_3346109 < baseStart_3346109 := by decide
  rcases family_descends (prefixWord ++ tailWord_3346109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3346132 : List Nat := [2, 4, 1, 3, 1, 1, 2, 2, 7]
def baseStart_3346132 : Nat := 118140960795 + 3346132 * 2 ^ 59
def prefixEnd_3346132 : Nat := 4983230072969 + 3 ^ 40 * 3346132 * 2
def baseEnd_3346132 : Nat := 190908227710045275206825

theorem tailTrace_3346132 : CollatzResearch.WordTrace tailWord_3346132 prefixEnd_3346132 190908227710045275206825 := by
  unfold tailWord_3346132
  simp only [CollatzResearch.WordTrace]
  refine ⟨61021730156771356346676325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81362306875695141795568433 61021730156771356346676325)
  ·
    refine ⟨11441574404394629315001811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61021730156771356346676325 11441574404394629315001811)
    ·
      refine ⟨17162361606591943972502717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11441574404394629315001811 17162361606591943972502717)
      ·
        refine ⟨6435885602471978989688519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17162361606591943972502717 6435885602471978989688519)
        ·
          refine ⟨9653828403707968484532779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6435885602471978989688519 9653828403707968484532779)
          ·
            refine ⟨14480742605561952726799169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9653828403707968484532779 14480742605561952726799169)
            ·
              refine ⟨10860556954171464545099377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14480742605561952726799169 10860556954171464545099377)
              ·
                refine ⟨8145417715628598408824533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10860556954171464545099377 8145417715628598408824533)
                ·
                  refine ⟨190908227710045275206825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8145417715628598408824533 190908227710045275206825)
                  ·
                    rfl

theorem cell23_3346132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 2, 2, 7].length) (baseStart_3346132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3346132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3346132 prefixEnd_3346132 := by exact prefixLift 3346132
  have htrace : WordTrace (prefixWord ++ tailWord_3346132) baseStart_3346132 baseEnd_3346132 := by
    simpa [prefixWord, tailWord_3346132, baseEnd_3346132] using wordTrace_append hprefix tailTrace_3346132
  have hstable : (prefixWord ++ tailWord_3346132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3346132).length < 2 ^ (prefixWord ++ tailWord_3346132).sum := by decide
  have hdescent : baseEnd_3346132 < baseStart_3346132 := by decide
  rcases family_descends (prefixWord ++ tailWord_3346132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3346162 : List Nat := [3, 2, 1, 3, 1, 1, 3, 2, 2, 5]
def baseStart_3346162 : Nat := 118140960795 + 3346162 * 2 ^ 59
def prefixEnd_3346162 : Nat := 4983230072969 + 3 ^ 40 * 3346162 * 2
def baseEnd_3346162 : Nat := 572729817936680786495429

theorem tailTrace_3346162 : CollatzResearch.WordTrace tailWord_3346162 prefixEnd_3346162 572729817936680786495429 := by
  unfold tailWord_3346162
  simp only [CollatzResearch.WordTrace]
  refine ⟨30511138625858506954236185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81363036335622685211296493 30511138625858506954236185)
  ·
    refine ⟨22883353969393880215677139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30511138625858506954236185 22883353969393880215677139)
    ·
      refine ⟨34325030954090820323515709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22883353969393880215677139 34325030954090820323515709)
      ·
        refine ⟨12871886607784057621318391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34325030954090820323515709 12871886607784057621318391)
        ·
          refine ⟨19307829911676086431977587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12871886607784057621318391 19307829911676086431977587)
          ·
            refine ⟨28961744867514129647966381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19307829911676086431977587 28961744867514129647966381)
            ·
              refine ⟨10860654325317798617987393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28961744867514129647966381 10860654325317798617987393)
              ·
                refine ⟨8145490743988348963490545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10860654325317798617987393 8145490743988348963490545)
                ·
                  refine ⟨6109118057991261722617909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8145490743988348963490545 6109118057991261722617909)
                  ·
                    refine ⟨572729817936680786495429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6109118057991261722617909 572729817936680786495429)
                    ·
                      rfl

theorem cell23_3346162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 3, 2, 2, 5].length) (baseStart_3346162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3346162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3346162 prefixEnd_3346162 := by exact prefixLift 3346162
  have htrace : WordTrace (prefixWord ++ tailWord_3346162) baseStart_3346162 baseEnd_3346162 := by
    simpa [prefixWord, tailWord_3346162, baseEnd_3346162] using wordTrace_append hprefix tailTrace_3346162
  have hstable : (prefixWord ++ tailWord_3346162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3346162).length < 2 ^ (prefixWord ++ tailWord_3346162).sum := by decide
  have hdescent : baseEnd_3346162 < baseStart_3346162 := by decide
  rcases family_descends (prefixWord ++ tailWord_3346162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3346166 : List Nat := [5, 1, 1, 1, 1, 4, 3, 2, 5]
def baseStart_3346166 : Nat := 118140960795 + 3346166 * 2 ^ 59
def prefixEnd_3346166 : Nat := 4983230072969 + 3 ^ 40 * 3346166 * 2
def baseEnd_3346166 : Nat := 190910167525851149315141

theorem tailTrace_3346166 : CollatzResearch.WordTrace tailWord_3346166 prefixEnd_3346166 190910167525851149315141 := by
  unfold tailWord_3346166
  simp only [CollatzResearch.WordTrace]
  refine ⟨7627793774713721031255647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 81363133596946357666726901 7627793774713721031255647)
  ·
    refine ⟨11441690662070581546883471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7627793774713721031255647 11441690662070581546883471)
    ·
      refine ⟨17162535993105872320325207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11441690662070581546883471 17162535993105872320325207)
      ·
        refine ⟨25743803989658808480487811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17162535993105872320325207 25743803989658808480487811)
        ·
          refine ⟨38615705984488212720731717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25743803989658808480487811 38615705984488212720731717)
          ·
            refine ⟨7240444872091539885137197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38615705984488212720731717 7240444872091539885137197)
            ·
              refine ⟨2715166827034327456926449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7240444872091539885137197 2715166827034327456926449)
              ·
                refine ⟨2036375120275745592694837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2715166827034327456926449 2036375120275745592694837)
                ·
                  refine ⟨190910167525851149315141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2036375120275745592694837 190910167525851149315141)
                  ·
                    rfl

theorem cell23_3346166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 3, 2, 5].length) (baseStart_3346166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3346166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3346166 prefixEnd_3346166 := by exact prefixLift 3346166
  have htrace : WordTrace (prefixWord ++ tailWord_3346166) baseStart_3346166 baseEnd_3346166 := by
    simpa [prefixWord, tailWord_3346166, baseEnd_3346166] using wordTrace_append hprefix tailTrace_3346166
  have hstable : (prefixWord ++ tailWord_3346166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3346166).length < 2 ^ (prefixWord ++ tailWord_3346166).sum := by decide
  have hdescent : baseEnd_3346166 < baseStart_3346166 := by decide
  rcases family_descends (prefixWord ++ tailWord_3346166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3346199 : List Nat := [1, 1, 3, 4, 2, 2, 2, 1, 2, 1, 4]
def baseStart_3346199 : Nat := 118140960795 + 3346199 * 2 ^ 59
def prefixEnd_3346199 : Nat := 4983230072969 + 3 ^ 40 * 3346199 * 2
def baseEnd_3346199 : Nat := 1718208452594258714723617

theorem tailTrace_3346199 : CollatzResearch.WordTrace tailWord_3346199 prefixEnd_3346199 1718208452594258714723617 := by
  unfold tailWord_3346199
  simp only [CollatzResearch.WordTrace]
  refine ⟨122045904004299983136041651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81363936002866655424027767 122045904004299983136041651)
  ·
    refine ⟨183068856006449974704062477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122045904004299983136041651 183068856006449974704062477)
    ·
      refine ⟨68650821002418740514023429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 183068856006449974704062477 68650821002418740514023429)
      ·
        refine ⟨12872028937953513846379393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 68650821002418740514023429 12872028937953513846379393)
        ·
          refine ⟨9654021703465135384784545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12872028937953513846379393 9654021703465135384784545)
          ·
            refine ⟨7240516277598851538588409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9654021703465135384784545 7240516277598851538588409)
            ·
              refine ⟨5430387208199138653941307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7240516277598851538588409 5430387208199138653941307)
              ·
                refine ⟨8145580812298707980911961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5430387208199138653941307 8145580812298707980911961)
                ·
                  refine ⟨6109185609224030985683971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8145580812298707980911961 6109185609224030985683971)
                  ·
                    refine ⟨9163778413836046478525957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6109185609224030985683971 9163778413836046478525957)
                    ·
                      refine ⟨1718208452594258714723617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9163778413836046478525957 1718208452594258714723617)
                      ·
                        rfl

theorem cell23_3346199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 2, 1, 2, 1, 4].length) (baseStart_3346199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3346199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3346199 prefixEnd_3346199 := by exact prefixLift 3346199
  have htrace : WordTrace (prefixWord ++ tailWord_3346199) baseStart_3346199 baseEnd_3346199 := by
    simpa [prefixWord, tailWord_3346199, baseEnd_3346199] using wordTrace_append hprefix tailTrace_3346199
  have hstable : (prefixWord ++ tailWord_3346199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3346199).length < 2 ^ (prefixWord ++ tailWord_3346199).sum := by decide
  have hdescent : baseEnd_3346199 < baseStart_3346199 := by decide
  rcases family_descends (prefixWord ++ tailWord_3346199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3346226 : List Nat := [3, 2, 1, 1, 3, 3, 1, 4, 1, 4]
def baseStart_3346226 : Nat := 118140960795 + 3346226 * 2 ^ 59
def prefixEnd_3346226 : Nat := 4983230072969 + 3 ^ 40 * 3346226 * 2
def baseEnd_3346226 : Nat := 572740772190643369695331

theorem tailTrace_3346226 : CollatzResearch.WordTrace tailWord_3346226 prefixEnd_3346226 572740772190643369695331 := by
  unfold tailWord_3346226
  simp only [CollatzResearch.WordTrace]
  refine ⟨30511722193800541686818633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81364592516801444498183021 30511722193800541686818633)
  ·
    refine ⟨22883791645350406265113975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30511722193800541686818633 22883791645350406265113975)
    ·
      refine ⟨34325687468025609397670963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22883791645350406265113975 34325687468025609397670963)
      ·
        refine ⟨51488531202038414096506445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34325687468025609397670963 51488531202038414096506445)
        ·
          refine ⟨19308199200764405286189917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51488531202038414096506445 19308199200764405286189917)
          ·
            refine ⟨7240574700286651982321219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19308199200764405286189917 7240574700286651982321219)
            ·
              refine ⟨10860862050429977973481829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7240574700286651982321219 10860862050429977973481829)
              ·
                refine ⟨2036411634455620870027843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10860862050429977973481829 2036411634455620870027843)
                ·
                  refine ⟨3054617451683431305041765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2036411634455620870027843 3054617451683431305041765)
                  ·
                    refine ⟨572740772190643369695331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3054617451683431305041765 572740772190643369695331)
                    ·
                      rfl

theorem cell23_3346226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 1, 4, 1, 4].length) (baseStart_3346226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3346226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3346226 prefixEnd_3346226 := by exact prefixLift 3346226
  have htrace : WordTrace (prefixWord ++ tailWord_3346226) baseStart_3346226 baseEnd_3346226 := by
    simpa [prefixWord, tailWord_3346226, baseEnd_3346226] using wordTrace_append hprefix tailTrace_3346226
  have hstable : (prefixWord ++ tailWord_3346226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3346226).length < 2 ^ (prefixWord ++ tailWord_3346226).sum := by decide
  have hdescent : baseEnd_3346226 < baseStart_3346226 := by decide
  rcases family_descends (prefixWord ++ tailWord_3346226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3346245 : List Nat := [1, 3, 1, 1, 1, 2, 3, 1, 2, 1, 7]
def baseStart_3346245 : Nat := 118140960795 + 3346245 * 2 ^ 59
def prefixEnd_3346245 : Nat := 4983230072969 + 3 ^ 40 * 3346245 * 2
def baseEnd_3346245 : Nat := 1718232072704365534748405

theorem tailTrace_3346245 : CollatzResearch.WordTrace tailWord_3346245 prefixEnd_3346245 1718232072704365534748405 := by
  unfold tailWord_3346245
  simp only [CollatzResearch.WordTrace]
  refine ⟨122047581762133332992216189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81365054508088888661477459 122047581762133332992216189)
  ·
    refine ⟨45767843160799999872081071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122047581762133332992216189 45767843160799999872081071)
    ·
      refine ⟨68651764741199999808121607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45767843160799999872081071 68651764741199999808121607)
      ·
        refine ⟨102977647111799999712182411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68651764741199999808121607 102977647111799999712182411)
        ·
          refine ⟨154466470667699999568273617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102977647111799999712182411 154466470667699999568273617)
          ·
            refine ⟨115849853000774999676205213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 154466470667699999568273617 115849853000774999676205213)
            ·
              refine ⟨43443694875290624878576955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 115849853000774999676205213 43443694875290624878576955)
              ·
                refine ⟨65165542312935937317865433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43443694875290624878576955 65165542312935937317865433)
                ·
                  refine ⟨48874156734701952988399075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65165542312935937317865433 48874156734701952988399075)
                  ·
                    refine ⟨73311235102052929482598613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 48874156734701952988399075 73311235102052929482598613)
                    ·
                      refine ⟨1718232072704365534748405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 73311235102052929482598613 1718232072704365534748405)
                      ·
                        rfl

theorem cell23_3346245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 1, 2, 1, 7].length) (baseStart_3346245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3346245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3346245 prefixEnd_3346245 := by exact prefixLift 3346245
  have htrace : WordTrace (prefixWord ++ tailWord_3346245) baseStart_3346245 baseEnd_3346245 := by
    simpa [prefixWord, tailWord_3346245, baseEnd_3346245] using wordTrace_append hprefix tailTrace_3346245
  have hstable : (prefixWord ++ tailWord_3346245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3346245).length < 2 ^ (prefixWord ++ tailWord_3346245).sum := by decide
  have hdescent : baseEnd_3346245 < baseStart_3346245 := by decide
  rcases family_descends (prefixWord ++ tailWord_3346245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3346249 : List Nat := [1, 2, 1, 1, 2, 4, 3, 2, 3, 1, 3]
def baseStart_3346249 : Nat := 118140960795 + 3346249 * 2 ^ 59
def prefixEnd_3346249 : Nat := 4983230072969 + 3 ^ 40 * 3346249 * 2
def baseEnd_3346249 : Nat := 1718234126626983519098387

theorem tailTrace_3346249 : CollatzResearch.WordTrace tailWord_3346249 prefixEnd_3346249 1718234126626983519098387 := by
  unfold tailWord_3346249
  simp only [CollatzResearch.WordTrace]
  refine ⟨122047727654118841675361801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81365151769412561116907867 122047727654118841675361801)
  ·
    refine ⟨91535795740589131256521351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122047727654118841675361801 91535795740589131256521351)
    ·
      refine ⟨137303693610883696884782027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91535795740589131256521351 137303693610883696884782027)
      ·
        refine ⟨205955540416325545327173041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137303693610883696884782027 205955540416325545327173041)
        ·
          refine ⟨154466655312244158995379781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 205955540416325545327173041 154466655312244158995379781)
          ·
            refine ⟨28962497871045779811633709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 154466655312244158995379781 28962497871045779811633709)
            ·
              refine ⟨10860936701642167429362641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28962497871045779811633709 10860936701642167429362641)
              ·
                refine ⟨8145702526231625572021981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10860936701642167429362641 8145702526231625572021981)
                ·
                  refine ⟨3054638447336859589508243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8145702526231625572021981 3054638447336859589508243)
                  ·
                    refine ⟨4581957671005289384262365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3054638447336859589508243 4581957671005289384262365)
                    ·
                      refine ⟨1718234126626983519098387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4581957671005289384262365 1718234126626983519098387)
                      ·
                        rfl

theorem cell23_3346249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 3, 2, 3, 1, 3].length) (baseStart_3346249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3346249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3346249 prefixEnd_3346249 := by exact prefixLift 3346249
  have htrace : WordTrace (prefixWord ++ tailWord_3346249) baseStart_3346249 baseEnd_3346249 := by
    simpa [prefixWord, tailWord_3346249, baseEnd_3346249] using wordTrace_append hprefix tailTrace_3346249
  have hstable : (prefixWord ++ tailWord_3346249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3346249).length < 2 ^ (prefixWord ++ tailWord_3346249).sum := by decide
  have hdescent : baseEnd_3346249 < baseStart_3346249 := by decide
  rcases family_descends (prefixWord ++ tailWord_3346249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3346253 : List Nat := [1, 6, 1, 2, 1, 3, 1, 1, 2, 2, 3]
def baseStart_3346253 : Nat := 118140960795 + 3346253 * 2 ^ 59
def prefixEnd_3346253 : Nat := 4983230072969 + 3 ^ 40 * 3346253 * 2
def baseEnd_3346253 : Nat := 1718236180549601503448369

theorem tailTrace_3346253 : CollatzResearch.WordTrace tailWord_3346253 prefixEnd_3346253 1718236180549601503448369 := by
  unfold tailWord_3346253
  simp only [CollatzResearch.WordTrace]
  refine ⟨122047873546104350358507413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81365249030736233572338275 122047873546104350358507413)
  ·
    refine ⟨5720994072473641423055035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 122047873546104350358507413 5720994072473641423055035)
    ·
      refine ⟨8581491108710462134582553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5720994072473641423055035 8581491108710462134582553)
      ·
        refine ⟨6436118331532846600936915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8581491108710462134582553 6436118331532846600936915)
        ·
          refine ⟨9654177497299269901405373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6436118331532846600936915 9654177497299269901405373)
          ·
            refine ⟨3620316561487226213027015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9654177497299269901405373 3620316561487226213027015)
            ·
              refine ⟨5430474842230839319540523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3620316561487226213027015 5430474842230839319540523)
              ·
                refine ⟨8145712263346258979310785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5430474842230839319540523 8145712263346258979310785)
                ·
                  refine ⟨6109284197509694234483089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8145712263346258979310785 6109284197509694234483089)
                  ·
                    refine ⟨4581963148132270675862317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6109284197509694234483089 4581963148132270675862317)
                    ·
                      refine ⟨1718236180549601503448369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4581963148132270675862317 1718236180549601503448369)
                      ·
                        rfl

theorem cell23_3346253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 3, 1, 1, 2, 2, 3].length) (baseStart_3346253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3346253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3346253 prefixEnd_3346253 := by exact prefixLift 3346253
  have htrace : WordTrace (prefixWord ++ tailWord_3346253) baseStart_3346253 baseEnd_3346253 := by
    simpa [prefixWord, tailWord_3346253, baseEnd_3346253] using wordTrace_append hprefix tailTrace_3346253
  have hstable : (prefixWord ++ tailWord_3346253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3346253).length < 2 ^ (prefixWord ++ tailWord_3346253).sum := by decide
  have hdescent : baseEnd_3346253 < baseStart_3346253 := by decide
  rcases family_descends (prefixWord ++ tailWord_3346253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3346334 : List Nat := [4, 3, 1, 3, 1, 1, 3, 2, 1, 1, 3]
def baseStart_3346334 : Nat := 118140960795 + 3346334 * 2 ^ 59
def prefixEnd_3346334 : Nat := 4983230072969 + 3 ^ 40 * 3346334 * 2
def baseEnd_3346334 : Nat := 1718277772482615686535497

theorem tailTrace_3346334 : CollatzResearch.WordTrace tailWord_3346334 prefixEnd_3346334 1718277772482615686535497 := by
  unfold tailWord_3346334
  simp only [CollatzResearch.WordTrace]
  refine ⟨15256353482351362649025757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81367218572540600794804037 15256353482351362649025757)
  ·
    refine ⟨5721132555881760993384659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15256353482351362649025757 5721132555881760993384659)
    ·
      refine ⟨8581698833822641490076989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5721132555881760993384659 8581698833822641490076989)
      ·
        refine ⟨3218137062683490558778871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8581698833822641490076989 3218137062683490558778871)
        ·
          refine ⟨4827205594025235838168307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3218137062683490558778871 4827205594025235838168307)
          ·
            refine ⟨7240808391037853757252461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4827205594025235838168307 7240808391037853757252461)
            ·
              refine ⟨2715303146639195158969673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7240808391037853757252461 2715303146639195158969673)
              ·
                refine ⟨2036477359979396369227255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2715303146639195158969673 2036477359979396369227255)
                ·
                  refine ⟨3054716039969094553840883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2036477359979396369227255 3054716039969094553840883)
                  ·
                    refine ⟨4582074059953641830761325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3054716039969094553840883 4582074059953641830761325)
                    ·
                      refine ⟨1718277772482615686535497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4582074059953641830761325 1718277772482615686535497)
                      ·
                        rfl

theorem cell23_3346334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 3, 2, 1, 1, 3].length) (baseStart_3346334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3346334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3346334 prefixEnd_3346334 := by exact prefixLift 3346334
  have htrace : WordTrace (prefixWord ++ tailWord_3346334) baseStart_3346334 baseEnd_3346334 := by
    simpa [prefixWord, tailWord_3346334, baseEnd_3346334] using wordTrace_append hprefix tailTrace_3346334
  have hstable : (prefixWord ++ tailWord_3346334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3346334).length < 2 ^ (prefixWord ++ tailWord_3346334).sum := by decide
  have hdescent : baseEnd_3346334 < baseStart_3346334 := by decide
  rcases family_descends (prefixWord ++ tailWord_3346334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3346362 : List Nat := [3, 1, 1, 1, 2, 1, 2, 1, 4, 3, 4]
def baseStart_3346362 : Nat := 118140960795 + 3346362 * 2 ^ 59
def prefixEnd_3346362 : Nat := 4983230072969 + 3 ^ 40 * 3346362 * 2
def baseEnd_3346362 : Nat := 1718292149940941576985367

theorem tailTrace_3346362 : CollatzResearch.WordTrace tailWord_3346362 prefixEnd_3346362 1718292149940941576985367 := by
  unfold tailWord_3346362
  simp only [CollatzResearch.WordTrace]
  refine ⟨30512962275677365493556335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81367899401806307982816893 30512962275677365493556335)
  ·
    refine ⟨45769443413516048240334503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30512962275677365493556335 45769443413516048240334503)
    ·
      refine ⟨68654165120274072360501755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45769443413516048240334503 68654165120274072360501755)
      ·
        refine ⟨102981247680411108540752633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68654165120274072360501755 102981247680411108540752633)
        ·
          refine ⟨77235935760308331405564475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102981247680411108540752633 77235935760308331405564475)
          ·
            refine ⟨115853903640462497108346713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77235935760308331405564475 115853903640462497108346713)
            ·
              refine ⟨86890427730346872831260035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 115853903640462497108346713 86890427730346872831260035)
              ·
                refine ⟨130335641595520309246890053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86890427730346872831260035 130335641595520309246890053)
                ·
                  refine ⟨24437932799160057983791885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 130335641595520309246890053 24437932799160057983791885)
                  ·
                    refine ⟨9164224799685021743921957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24437932799160057983791885 9164224799685021743921957)
                    ·
                      refine ⟨1718292149940941576985367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9164224799685021743921957 1718292149940941576985367)
                      ·
                        rfl

theorem cell23_3346362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 1, 4, 3, 4].length) (baseStart_3346362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3346362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3346362 prefixEnd_3346362 := by exact prefixLift 3346362
  have htrace : WordTrace (prefixWord ++ tailWord_3346362) baseStart_3346362 baseEnd_3346362 := by
    simpa [prefixWord, tailWord_3346362, baseEnd_3346362] using wordTrace_append hprefix tailTrace_3346362
  have hstable : (prefixWord ++ tailWord_3346362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3346362).length < 2 ^ (prefixWord ++ tailWord_3346362).sum := by decide
  have hdescent : baseEnd_3346362 < baseStart_3346362 := by decide
  rcases family_descends (prefixWord ++ tailWord_3346362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3346383 : List Nat := [1, 1, 2, 1, 1, 5, 5, 1, 1, 3, 2]
def baseStart_3346383 : Nat := 118140960795 + 3346383 * 2 ^ 59
def prefixEnd_3346383 : Nat := 4983230072969 + 3 ^ 40 * 3346383 * 2
def baseEnd_3346383 : Nat := 1718302933034685994822771

theorem tailTrace_3346383 : CollatzResearch.WordTrace tailWord_3346383 prefixEnd_3346383 1718302933034685994822771 := by
  unfold tailWord_3346383
  simp only [CollatzResearch.WordTrace]
  refine ⟨122052615035633382560739803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81368410023755588373826535 122052615035633382560739803)
  ·
    refine ⟨183078922553450073841109705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122052615035633382560739803 183078922553450073841109705)
    ·
      refine ⟨137309191915087555380832279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183078922553450073841109705 137309191915087555380832279)
      ·
        refine ⟨205963787872631333071248419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137309191915087555380832279 205963787872631333071248419)
        ·
          refine ⟨308945681808946999606872629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 205963787872631333071248419 308945681808946999606872629)
          ·
            refine ⟨28963657669588781213144309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 308945681808946999606872629 28963657669588781213144309)
            ·
              refine ⟨2715342906523948238732279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28963657669588781213144309 2715342906523948238732279)
              ·
                refine ⟨4073014359785922358098419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2715342906523948238732279 4073014359785922358098419)
                ·
                  refine ⟨6109521539678883537147629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4073014359785922358098419 6109521539678883537147629)
                  ·
                    refine ⟨2291070577379581326430361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6109521539678883537147629 2291070577379581326430361)
                    ·
                      refine ⟨1718302933034685994822771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2291070577379581326430361 1718302933034685994822771)
                      ·
                        rfl

theorem cell23_3346383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 5, 1, 1, 3, 2].length) (baseStart_3346383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3346383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3346383 prefixEnd_3346383 := by exact prefixLift 3346383
  have htrace : WordTrace (prefixWord ++ tailWord_3346383) baseStart_3346383 baseEnd_3346383 := by
    simpa [prefixWord, tailWord_3346383, baseEnd_3346383] using wordTrace_append hprefix tailTrace_3346383
  have hstable : (prefixWord ++ tailWord_3346383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3346383).length < 2 ^ (prefixWord ++ tailWord_3346383).sum := by decide
  have hdescent : baseEnd_3346383 < baseStart_3346383 := by decide
  rcases family_descends (prefixWord ++ tailWord_3346383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3346399 : List Nat := [1, 1, 2, 3, 4, 1, 1, 1, 2, 4, 3]
def baseStart_3346399 : Nat := 118140960795 + 3346399 * 2 ^ 59
def prefixEnd_3346399 : Nat := 4983230072969 + 3 ^ 40 * 3346399 * 2
def baseEnd_3346399 : Nat := 1718311148725157932222697

theorem tailTrace_3346399 : CollatzResearch.WordTrace tailWord_3346399 prefixEnd_3346399 1718311148725157932222697 := by
  unfold tailWord_3346399
  simp only [CollatzResearch.WordTrace]
  refine ⟨122053198603575417293322251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81368799069050278195548167 122053198603575417293322251)
  ·
    refine ⟨183079797905363125939983377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122053198603575417293322251 183079797905363125939983377)
    ·
      refine ⟨137309848429022344454987533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183079797905363125939983377 137309848429022344454987533)
      ·
        refine ⟨51491193160883379170620325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 137309848429022344454987533 51491193160883379170620325)
        ·
          refine ⟨9654598717665633594491311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51491193160883379170620325 9654598717665633594491311)
          ·
            refine ⟨14481898076498450391736967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9654598717665633594491311 14481898076498450391736967)
            ·
              refine ⟨21722847114747675587605451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14481898076498450391736967 21722847114747675587605451)
              ·
                refine ⟨32584270672121513381408177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21722847114747675587605451 32584270672121513381408177)
                ·
                  refine ⟨24438203004091135036056133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32584270672121513381408177 24438203004091135036056133)
                  ·
                    refine ⟨4582163063267087819260525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24438203004091135036056133 4582163063267087819260525)
                    ·
                      refine ⟨1718311148725157932222697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4582163063267087819260525 1718311148725157932222697)
                      ·
                        rfl

theorem cell23_3346399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 1, 2, 4, 3].length) (baseStart_3346399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3346399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3346399 prefixEnd_3346399 := by exact prefixLift 3346399
  have htrace : WordTrace (prefixWord ++ tailWord_3346399) baseStart_3346399 baseEnd_3346399 := by
    simpa [prefixWord, tailWord_3346399, baseEnd_3346399] using wordTrace_append hprefix tailTrace_3346399
  have hstable : (prefixWord ++ tailWord_3346399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3346399).length < 2 ^ (prefixWord ++ tailWord_3346399).sum := by decide
  have hdescent : baseEnd_3346399 < baseStart_3346399 := by decide
  rcases family_descends (prefixWord ++ tailWord_3346399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3346469 : List Nat := [1, 3, 1, 2, 2, 3, 1, 2, 1, 3, 4]
def baseStart_3346469 : Nat := 118140960795 + 3346469 * 2 ^ 59
def prefixEnd_3346469 : Nat := 4983230072969 + 3 ^ 40 * 3346469 * 2
def baseEnd_3346469 : Nat := 1718347092370972658347375

theorem tailTrace_3346469 : CollatzResearch.WordTrace tailWord_3346469 prefixEnd_3346469 1718347092370972658347375 := by
  unfold tailWord_3346469
  simp only [CollatzResearch.WordTrace]
  refine ⟨122055751713321819248370461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81370501142214546165580307 122055751713321819248370461)
  ·
    refine ⟨45770906892495682218138923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122055751713321819248370461 45770906892495682218138923)
    ·
      refine ⟨68656360338743523327208385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45770906892495682218138923 68656360338743523327208385)
      ·
        refine ⟨51492270254057642495406289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68656360338743523327208385 51492270254057642495406289)
        ·
          refine ⟨38619202690543231871554717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51492270254057642495406289 38619202690543231871554717)
          ·
            refine ⟨14482201008953711951833019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38619202690543231871554717 14482201008953711951833019)
            ·
              refine ⟨21723301513430567927749529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14482201008953711951833019 21723301513430567927749529)
              ·
                refine ⟨16292476135072925945812147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21723301513430567927749529 16292476135072925945812147)
                ·
                  refine ⟨24438714202609388918718221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16292476135072925945812147 24438714202609388918718221)
                  ·
                    refine ⟨9164517825978520844519333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24438714202609388918718221 9164517825978520844519333)
                    ·
                      refine ⟨1718347092370972658347375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9164517825978520844519333 1718347092370972658347375)
                      ·
                        rfl

theorem cell23_3346469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 2, 1, 3, 4].length) (baseStart_3346469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3346469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3346469 prefixEnd_3346469 := by exact prefixLift 3346469
  have htrace : WordTrace (prefixWord ++ tailWord_3346469) baseStart_3346469 baseEnd_3346469 := by
    simpa [prefixWord, tailWord_3346469, baseEnd_3346469] using wordTrace_append hprefix tailTrace_3346469
  have hstable : (prefixWord ++ tailWord_3346469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3346469).length < 2 ^ (prefixWord ++ tailWord_3346469).sum := by decide
  have hdescent : baseEnd_3346469 < baseStart_3346469 := by decide
  rcases family_descends (prefixWord ++ tailWord_3346469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3346479 : List Nat := [1, 1, 2, 1, 2, 1, 1, 5, 5, 4]
def baseStart_3346479 : Nat := 118140960795 + 3346479 * 2 ^ 59
def prefixEnd_3346479 : Nat := 4983230072969 + 3 ^ 40 * 3346479 * 2
def baseEnd_3346479 : Nat := 572784075725839206407443

theorem tailTrace_3346479 : CollatzResearch.WordTrace tailWord_3346479 prefixEnd_3346479 572784075725839206407443 := by
  unfold tailWord_3346479
  simp only [CollatzResearch.WordTrace]
  refine ⟨122056116443285590956234491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81370744295523727304156327 122056116443285590956234491)
  ·
    refine ⟨183084174664928386434351737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122056116443285590956234491 183084174664928386434351737)
    ·
      refine ⟨137313130998696289825763803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183084174664928386434351737 137313130998696289825763803)
      ·
        refine ⟨205969696498044434738645705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137313130998696289825763803 205969696498044434738645705)
        ·
          refine ⟨154477272373533326053984279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 205969696498044434738645705 154477272373533326053984279)
          ·
            refine ⟨231715908560299989080976419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154477272373533326053984279 231715908560299989080976419)
            ·
              refine ⟨347573862840449983621464629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 231715908560299989080976419 347573862840449983621464629)
              ·
                refine ⟨32585049641292185964512309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 347573862840449983621464629 32585049641292185964512309)
                ·
                  refine ⟨3054848403871142434173029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 32585049641292185964512309 3054848403871142434173029)
                  ·
                    refine ⟨572784075725839206407443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3054848403871142434173029 572784075725839206407443)
                    ·
                      rfl

theorem cell23_3346479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 5, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 5, 5, 4].length) (baseStart_3346479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3346479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3346479 prefixEnd_3346479 := by exact prefixLift 3346479
  have htrace : WordTrace (prefixWord ++ tailWord_3346479) baseStart_3346479 baseEnd_3346479 := by
    simpa [prefixWord, tailWord_3346479, baseEnd_3346479] using wordTrace_append hprefix tailTrace_3346479
  have hstable : (prefixWord ++ tailWord_3346479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3346479).length < 2 ^ (prefixWord ++ tailWord_3346479).sum := by decide
  have hdescent : baseEnd_3346479 < baseStart_3346479 := by decide
  rcases family_descends (prefixWord ++ tailWord_3346479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3346486 : List Nat := [5, 1, 2, 1, 1, 1, 1, 3, 1, 3, 4]
def baseStart_3346486 : Nat := 118140960795 + 3346486 * 2 ^ 59
def prefixEnd_3346486 : Nat := 4983230072969 + 3 ^ 40 * 3346486 * 2
def baseEnd_3346486 : Nat := 1718355821542099091834797

theorem tailTrace_3346486 : CollatzResearch.WordTrace tailWord_3346486 prefixEnd_3346486 1718355821542099091834797 := by
  unfold tailWord_3346486
  simp only [CollatzResearch.WordTrace]
  refine ⟨7628523234641264446983707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 81370914502840154101159541 7628523234641264446983707)
  ·
    refine ⟨11442784851961896670475561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7628523234641264446983707 11442784851961896670475561)
    ·
      refine ⟨8582088638971422502856671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11442784851961896670475561 8582088638971422502856671)
      ·
        refine ⟨12873132958457133754285007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8582088638971422502856671 12873132958457133754285007)
        ·
          refine ⟨19309699437685700631427511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12873132958457133754285007 19309699437685700631427511)
          ·
            refine ⟨28964549156528550947141267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19309699437685700631427511 28964549156528550947141267)
            ·
              refine ⟨43446823734792826420711901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28964549156528550947141267 43446823734792826420711901)
              ·
                refine ⟨16292558900547309907766963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43446823734792826420711901 16292558900547309907766963)
                ·
                  refine ⟨24438838350820964861650445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16292558900547309907766963 24438838350820964861650445)
                  ·
                    refine ⟨9164564381557861823118917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24438838350820964861650445 9164564381557861823118917)
                    ·
                      refine ⟨1718355821542099091834797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9164564381557861823118917 1718355821542099091834797)
                      ·
                        rfl

theorem cell23_3346486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 3, 1, 3, 4].length) (baseStart_3346486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3346486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3346486 prefixEnd_3346486 := by exact prefixLift 3346486
  have htrace : WordTrace (prefixWord ++ tailWord_3346486) baseStart_3346486 baseEnd_3346486 := by
    simpa [prefixWord, tailWord_3346486, baseEnd_3346486] using wordTrace_append hprefix tailTrace_3346486
  have hstable : (prefixWord ++ tailWord_3346486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3346486).length < 2 ^ (prefixWord ++ tailWord_3346486).sum := by decide
  have hdescent : baseEnd_3346486 < baseStart_3346486 := by decide
  rcases family_descends (prefixWord ++ tailWord_3346486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3346563 : List Nat := [1, 1, 1, 3, 3, 3, 2, 2, 2, 3, 2]
def baseStart_3346563 : Nat := 118140960795 + 3346563 * 2 ^ 59
def prefixEnd_3346563 : Nat := 4983230072969 + 3 ^ 40 * 3346563 * 2
def baseEnd_3346563 : Nat := 1718395359552495290571943

theorem tailTrace_3346563 : CollatzResearch.WordTrace tailWord_3346563 prefixEnd_3346563 1718395359552495290571943 := by
  unfold tailWord_3346563
  simp only [CollatzResearch.WordTrace]
  refine ⟨122059180174981273302292343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81372786783320848868194895 122059180174981273302292343)
  ·
    refine ⟨183088770262471909953438515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122059180174981273302292343 183088770262471909953438515)
    ·
      refine ⟨274633155393707864930157773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183088770262471909953438515 274633155393707864930157773)
      ·
        refine ⟨102987433272640449348809165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 274633155393707864930157773 102987433272640449348809165)
        ·
          refine ⟨38620287477240168505803437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102987433272640449348809165 38620287477240168505803437)
          ·
            refine ⟨14482607803965063189676289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38620287477240168505803437 14482607803965063189676289)
            ·
              refine ⟨10861955852973797392257217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14482607803965063189676289 10861955852973797392257217)
              ·
                refine ⟨8146466889730348044192913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10861955852973797392257217 8146466889730348044192913)
                ·
                  refine ⟨6109850167297761033144685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8146466889730348044192913 6109850167297761033144685)
                  ·
                    refine ⟨2291193812736660387429257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6109850167297761033144685 2291193812736660387429257)
                    ·
                      refine ⟨1718395359552495290571943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2291193812736660387429257 1718395359552495290571943)
                      ·
                        rfl

theorem cell23_3346563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 2, 2, 2, 3, 2].length) (baseStart_3346563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3346563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3346563 prefixEnd_3346563 := by exact prefixLift 3346563
  have htrace : WordTrace (prefixWord ++ tailWord_3346563) baseStart_3346563 baseEnd_3346563 := by
    simpa [prefixWord, tailWord_3346563, baseEnd_3346563] using wordTrace_append hprefix tailTrace_3346563
  have hstable : (prefixWord ++ tailWord_3346563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3346563).length < 2 ^ (prefixWord ++ tailWord_3346563).sum := by decide
  have hdescent : baseEnd_3346563 < baseStart_3346563 := by decide
  rcases family_descends (prefixWord ++ tailWord_3346563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
