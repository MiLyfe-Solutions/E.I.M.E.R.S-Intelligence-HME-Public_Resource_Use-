import V185TrunkScan22Chunk007

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_71164 : List Nat := [2, 2, 2, 1, 2, 1, 3, 1, 4, 4]
def baseStart_71164 : Nat := 118140960795 + 71164 * 2 ^ 59
def prefixEnd_71164 : Nat := 4983230072969 + 3 ^ 40 * 71164 * 2
def baseEnd_71164 : Nat := 24360891531109869481819

theorem tailTrace_71164 : CollatzResearch.WordTrace tailWord_71164 prefixEnd_71164 24360891531109869481819 := by
  unfold tailWord_71164
  simp only [CollatzResearch.WordTrace]
  refine ⟨1297782157096228344346273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1730376209461637792461697 1297782157096228344346273)
  ·
    refine ⟨973336617822171258259705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1297782157096228344346273 973336617822171258259705)
    ·
      refine ⟨730002463366628443694779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 973336617822171258259705 730002463366628443694779)
      ·
        refine ⟨1095003695049942665542169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 730002463366628443694779 1095003695049942665542169)
        ·
          refine ⟨821252771287456999156627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1095003695049942665542169 821252771287456999156627)
          ·
            refine ⟨1231879156931185498734941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 821252771287456999156627 1231879156931185498734941)
            ·
              refine ⟨461954683849194562025603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1231879156931185498734941 461954683849194562025603)
              ·
                refine ⟨692932025773791843038405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 461954683849194562025603 692932025773791843038405)
                ·
                  refine ⟨129924754832585970569701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 692932025773791843038405 129924754832585970569701)
                  ·
                    refine ⟨24360891531109869481819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 129924754832585970569701 24360891531109869481819)
                    ·
                      rfl

theorem cell22_71164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 1, 4, 4].length) (baseStart_71164 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_71164 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_71164 prefixEnd_71164 := by exact prefixLift 71164
  have htrace : WordTrace (prefixWord ++ tailWord_71164) baseStart_71164 baseEnd_71164 := by
    simpa [prefixWord, tailWord_71164, baseEnd_71164] using wordTrace_append hprefix tailTrace_71164
  have hstable : (prefixWord ++ tailWord_71164).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_71164).length < 2 ^ (prefixWord ++ tailWord_71164).sum := by decide
  have hdescent : baseEnd_71164 < baseStart_71164 := by decide
  rcases family_descends (prefixWord ++ tailWord_71164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_71174 : List Nat := [6, 2, 1, 1, 2, 2, 2, 1, 5]
def baseStart_71174 : Nat := 118140960795 + 71174 * 2 ^ 59
def prefixEnd_71174 : Nat := 4983230072969 + 3 ^ 40 * 71174 * 2
def baseEnd_71174 : Nat := 8121438245157725577263

theorem tailTrace_71174 : CollatzResearch.WordTrace tailWord_71174 prefixEnd_71174 8121438245157725577263 := by
  unfold tailWord_71174
  simp only [CollatzResearch.WordTrace]
  refine ⟨81122782629882137392393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 1730619362770818931037717 81122782629882137392393)
  ·
    refine ⟨60842086972411603044295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81122782629882137392393 60842086972411603044295)
    ·
      refine ⟨91263130458617404566443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60842086972411603044295 91263130458617404566443)
      ·
        refine ⟨136894695687926106849665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91263130458617404566443 136894695687926106849665)
        ·
          refine ⟨102671021765944580137249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 136894695687926106849665 102671021765944580137249)
          ·
            refine ⟨77003266324458435102937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 102671021765944580137249 77003266324458435102937)
            ·
              refine ⟨57752449743343826327203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 77003266324458435102937 57752449743343826327203)
              ·
                refine ⟨86628674615015739490805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57752449743343826327203 86628674615015739490805)
                ·
                  refine ⟨8121438245157725577263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 86628674615015739490805 8121438245157725577263)
                  ·
                    rfl

theorem cell22_71174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 2, 2, 1, 5].length) (baseStart_71174 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_71174 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_71174 prefixEnd_71174 := by exact prefixLift 71174
  have htrace : WordTrace (prefixWord ++ tailWord_71174) baseStart_71174 baseEnd_71174 := by
    simpa [prefixWord, tailWord_71174, baseEnd_71174] using wordTrace_append hprefix tailTrace_71174
  have hstable : (prefixWord ++ tailWord_71174).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_71174).length < 2 ^ (prefixWord ++ tailWord_71174).sum := by decide
  have hdescent : baseEnd_71174 < baseStart_71174 := by decide
  rcases family_descends (prefixWord ++ tailWord_71174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_71245 : List Nat := [1, 6, 1, 1, 3, 1, 1, 2, 3, 3]
def baseStart_71245 : Nat := 118140960795 + 71245 * 2 ^ 59
def prefixEnd_71245 : Nat := 4983230072969 + 3 ^ 40 * 71245 * 2
def baseEnd_71245 : Nat := 24388619486452658206571

theorem tailTrace_71245 : CollatzResearch.WordTrace tailWord_71245 prefixEnd_71245 24388619486452658206571 := by
  unfold tailWord_71245
  simp only [CollatzResearch.WordTrace]
  refine ⟨2598518626899007522391189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1732345751266005014927459 2598518626899007522391189)
  ·
    refine ⟨121805560635890977612087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 2598518626899007522391189 121805560635890977612087)
    ·
      refine ⟨182708340953836466418131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121805560635890977612087 182708340953836466418131)
      ·
        refine ⟨274062511430754699627197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 182708340953836466418131 274062511430754699627197)
        ·
          refine ⟨102773441786533012360199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 274062511430754699627197 102773441786533012360199)
          ·
            refine ⟨154160162679799518540299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102773441786533012360199 154160162679799518540299)
            ·
              refine ⟨231240244019699277810449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 154160162679799518540299 231240244019699277810449)
              ·
                refine ⟨173430183014774458357837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 231240244019699277810449 173430183014774458357837)
                ·
                  refine ⟨65036318630540421884189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 173430183014774458357837 65036318630540421884189)
                  ·
                    refine ⟨24388619486452658206571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 65036318630540421884189 24388619486452658206571)
                    ·
                      rfl

theorem cell22_71245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 1, 2, 3, 3].length) (baseStart_71245 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_71245 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_71245 prefixEnd_71245 := by exact prefixLift 71245
  have htrace : WordTrace (prefixWord ++ tailWord_71245) baseStart_71245 baseEnd_71245 := by
    simpa [prefixWord, tailWord_71245, baseEnd_71245] using wordTrace_append hprefix tailTrace_71245
  have hstable : (prefixWord ++ tailWord_71245).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_71245).length < 2 ^ (prefixWord ++ tailWord_71245).sum := by decide
  have hdescent : baseEnd_71245 < baseStart_71245 := by decide
  rcases family_descends (prefixWord ++ tailWord_71245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_71320 : List Nat := [2, 1, 2, 4, 1, 4, 1, 3, 4]
def baseStart_71320 : Nat := 118140960795 + 71320 * 2 ^ 59
def prefixEnd_71320 : Nat := 4983230072969 + 3 ^ 40 * 71320 * 2
def baseEnd_71320 : Nat := 8138097839725820860447

theorem tailTrace_71320 : CollatzResearch.WordTrace tailWord_71320 prefixEnd_71320 8138097839725820860447 := by
  unfold tailWord_71320
  simp only [CollatzResearch.WordTrace]
  refine ⟨1300627050813647665685707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1734169401084863554247609 1300627050813647665685707)
  ·
    refine ⟨1950940576220471498528561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1300627050813647665685707 1950940576220471498528561)
    ·
      refine ⟨1463205432165353623896421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1950940576220471498528561 1463205432165353623896421)
      ·
        refine ⟨274351018531003804480579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1463205432165353623896421 274351018531003804480579)
        ·
          refine ⟨411526527796505706720869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 274351018531003804480579 411526527796505706720869)
          ·
            refine ⟨77161223961844820010163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 411526527796505706720869 77161223961844820010163)
            ·
              refine ⟨115741835942767230015245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77161223961844820010163 115741835942767230015245)
              ·
                refine ⟨43403188478537711255717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 115741835942767230015245 43403188478537711255717)
                ·
                  refine ⟨8138097839725820860447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 43403188478537711255717 8138097839725820860447)
                  ·
                    rfl

theorem cell22_71320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 4, 1, 3, 4].length) (baseStart_71320 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_71320 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_71320 prefixEnd_71320 := by exact prefixLift 71320
  have htrace : WordTrace (prefixWord ++ tailWord_71320) baseStart_71320 baseEnd_71320 := by
    simpa [prefixWord, tailWord_71320, baseEnd_71320] using wordTrace_append hprefix tailTrace_71320
  have hstable : (prefixWord ++ tailWord_71320).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_71320).length < 2 ^ (prefixWord ++ tailWord_71320).sum := by decide
  have hdescent : baseEnd_71320 < baseStart_71320 := by decide
  rcases family_descends (prefixWord ++ tailWord_71320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_71391 : List Nat := [1, 1, 2, 3, 2, 2, 2, 2, 2, 5]
def baseStart_71391 : Nat := 118140960795 + 71391 * 2 ^ 59
def prefixEnd_71391 : Nat := 4983230072969 + 3 ^ 40 * 71391 * 2
def baseEnd_71391 : Nat := 24438598270156944056123

theorem tailTrace_71391 : CollatzResearch.WordTrace tailWord_71391 prefixEnd_71391 24438598270156944056123 := by
  unfold tailWord_71391
  simp only [CollatzResearch.WordTrace]
  refine ⟨2603843684370074457206027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1735895789580049638137351 2603843684370074457206027)
  ·
    refine ⟨3905765526555111685809041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2603843684370074457206027 3905765526555111685809041)
    ·
      refine ⟨2929324144916333764356781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3905765526555111685809041 2929324144916333764356781)
      ·
        refine ⟨1098496554343625161633793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2929324144916333764356781 1098496554343625161633793)
        ·
          refine ⟨823872415757718871225345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1098496554343625161633793 823872415757718871225345)
          ·
            refine ⟨617904311818289153419009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 823872415757718871225345 617904311818289153419009)
            ·
              refine ⟨463428233863716865064257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 617904311818289153419009 463428233863716865064257)
              ·
                refine ⟨347571175397787648798193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 463428233863716865064257 347571175397787648798193)
                ·
                  refine ⟨260678381548340736598645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 347571175397787648798193 260678381548340736598645)
                  ·
                    refine ⟨24438598270156944056123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 260678381548340736598645 24438598270156944056123)
                    ·
                      rfl

theorem cell22_71391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 2, 2, 5].length) (baseStart_71391 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_71391 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_71391 prefixEnd_71391 := by exact prefixLift 71391
  have htrace : WordTrace (prefixWord ++ tailWord_71391) baseStart_71391 baseEnd_71391 := by
    simpa [prefixWord, tailWord_71391, baseEnd_71391] using wordTrace_append hprefix tailTrace_71391
  have hstable : (prefixWord ++ tailWord_71391).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_71391).length < 2 ^ (prefixWord ++ tailWord_71391).sum := by decide
  have hdescent : baseEnd_71391 < baseStart_71391 := by decide
  rcases family_descends (prefixWord ++ tailWord_71391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_71500 : List Nat := [2, 2, 1, 3, 5, 1, 8]
def baseStart_71500 : Nat := 118140960795 + 71500 * 2 ^ 59
def prefixEnd_71500 : Nat := 4983230072969 + 3 ^ 40 * 71500 * 2
def baseEnd_71500 : Nat := 906515229545073817807

theorem tailTrace_71500 : CollatzResearch.WordTrace tailWord_71500 prefixEnd_71500 906515229545073817807 := by
  unfold tailWord_71500
  simp only [CollatzResearch.WordTrace]
  refine ⟨1303909620487593036461977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1738546160650124048615969 1303909620487593036461977)
  ·
    refine ⟨977932215365694777346483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1303909620487593036461977 977932215365694777346483)
    ·
      refine ⟨1466898323048542166019725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 977932215365694777346483 1466898323048542166019725)
      ·
        refine ⟨550086871143203312257397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1466898323048542166019725 550086871143203312257397)
        ·
          refine ⟨51570644169675310524131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 550086871143203312257397 51570644169675310524131)
          ·
            refine ⟨77355966254512965786197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51570644169675310524131 77355966254512965786197)
            ·
              refine ⟨906515229545073817807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 77355966254512965786197 906515229545073817807)
              ·
                rfl

theorem cell22_71500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 1, 8].length) (baseStart_71500 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_71500 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_71500 prefixEnd_71500 := by exact prefixLift 71500
  have htrace : WordTrace (prefixWord ++ tailWord_71500) baseStart_71500 baseEnd_71500 := by
    simpa [prefixWord, tailWord_71500, baseEnd_71500] using wordTrace_append hprefix tailTrace_71500
  have hstable : (prefixWord ++ tailWord_71500).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_71500).length < 2 ^ (prefixWord ++ tailWord_71500).sum := by decide
  have hdescent : baseEnd_71500 < baseStart_71500 := by decide
  rcases family_descends (prefixWord ++ tailWord_71500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_71562 : List Nat := [3, 1, 2, 4, 2, 1, 2, 2, 5]
def baseStart_71562 : Nat := 118140960795 + 71562 * 2 ^ 59
def prefixEnd_71562 : Nat := 4983230072969 + 3 ^ 40 * 71562 * 2
def baseEnd_71562 : Nat := 8165711688256499343533

theorem tailTrace_71562 : CollatzResearch.WordTrace tailWord_71562 prefixEnd_71562 8165711688256499343533 := by
  unfold tailWord_71562
  simp only [CollatzResearch.WordTrace]
  refine ⟨652520141687642665420235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1740053711167047107787293 652520141687642665420235)
  ·
    refine ⟨978780212531463998130353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 652520141687642665420235 978780212531463998130353)
    ·
      refine ⟨734085159398597998597765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 978780212531463998130353 734085159398597998597765)
      ·
        refine ⟨137640967387237124737081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 734085159398597998597765 137640967387237124737081)
        ·
          refine ⟨103230725540427843552811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 137640967387237124737081 103230725540427843552811)
          ·
            refine ⟨154846088310641765329217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103230725540427843552811 154846088310641765329217)
            ·
              refine ⟨116134566232981323996913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 154846088310641765329217 116134566232981323996913)
              ·
                refine ⟨87100924674735992997685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 116134566232981323996913 87100924674735992997685)
                ·
                  refine ⟨8165711688256499343533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 87100924674735992997685 8165711688256499343533)
                  ·
                    rfl

theorem cell22_71562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 2, 2, 5].length) (baseStart_71562 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_71562 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_71562 prefixEnd_71562 := by exact prefixLift 71562
  have htrace : WordTrace (prefixWord ++ tailWord_71562) baseStart_71562 baseEnd_71562 := by
    simpa [prefixWord, tailWord_71562, baseEnd_71562] using wordTrace_append hprefix tailTrace_71562
  have hstable : (prefixWord ++ tailWord_71562).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_71562).length < 2 ^ (prefixWord ++ tailWord_71562).sum := by decide
  have hdescent : baseEnd_71562 < baseStart_71562 := by decide
  rcases family_descends (prefixWord ++ tailWord_71562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_71566 : List Nat := [4, 1, 1, 5, 1, 1, 1, 4, 1, 3]
def baseStart_71566 : Nat := 118140960795 + 71566 * 2 ^ 59
def prefixEnd_71566 : Nat := 4983230072969 + 3 ^ 40 * 71566 * 2
def baseEnd_71566 : Nat := 24498504346514820930587

theorem tailTrace_71566 : CollatzResearch.WordTrace tailWord_71566 prefixEnd_71566 24498504346514820930587 := by
  unfold tailWord_71566
  simp only [CollatzResearch.WordTrace]
  refine ⟨326278307342009918103319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1740150972490719563217701 326278307342009918103319)
  ·
    refine ⟨489417461013014877154979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 326278307342009918103319 489417461013014877154979)
    ·
      refine ⟨734126191519522315732469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 489417461013014877154979 734126191519522315732469)
      ·
        refine ⟨68824330454955217099919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 734126191519522315732469 68824330454955217099919)
        ·
          refine ⟨103236495682432825649879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68824330454955217099919 103236495682432825649879)
          ·
            refine ⟨154854743523649238474819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103236495682432825649879 154854743523649238474819)
            ·
              refine ⟨232282115285473857712229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 154854743523649238474819 232282115285473857712229)
              ·
                refine ⟨43552896616026348321043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 232282115285473857712229 43552896616026348321043)
                ·
                  refine ⟨65329344924039522481565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43552896616026348321043 65329344924039522481565)
                  ·
                    refine ⟨24498504346514820930587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 65329344924039522481565 24498504346514820930587)
                    ·
                      rfl

theorem cell22_71566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 1, 4, 1, 3].length) (baseStart_71566 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_71566 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_71566 prefixEnd_71566 := by exact prefixLift 71566
  have htrace : WordTrace (prefixWord ++ tailWord_71566) baseStart_71566 baseEnd_71566 := by
    simpa [prefixWord, tailWord_71566, baseEnd_71566] using wordTrace_append hprefix tailTrace_71566
  have hstable : (prefixWord ++ tailWord_71566).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_71566).length < 2 ^ (prefixWord ++ tailWord_71566).sum := by decide
  have hdescent : baseEnd_71566 < baseStart_71566 := by decide
  rcases family_descends (prefixWord ++ tailWord_71566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_71573 : List Nat := [1, 3, 2, 1, 1, 3, 2, 3, 6]
def baseStart_71573 : Nat := 118140960795 + 71573 * 2 ^ 59
def prefixEnd_71573 : Nat := 4983230072969 + 3 ^ 40 * 71573 * 2
def baseEnd_71573 : Nat := 8166966863189712001855

theorem tailTrace_71573 : CollatzResearch.WordTrace tailWord_71573 prefixEnd_71573 8166966863189712001855 := by
  unfold tailWord_71573
  simp only [CollatzResearch.WordTrace]
  refine ⟨2610481769710719540331373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1740321179807146360220915 2610481769710719540331373)
  ·
    refine ⟨978930663641519827624265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2610481769710719540331373 978930663641519827624265)
    ·
      refine ⟨734197997731139870718199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 978930663641519827624265 734197997731139870718199)
      ·
        refine ⟨1101296996596709806077299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 734197997731139870718199 1101296996596709806077299)
        ·
          refine ⟨1651945494895064709115949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1101296996596709806077299 1651945494895064709115949)
          ·
            refine ⟨619479560585649265918481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1651945494895064709115949 619479560585649265918481)
            ·
              refine ⟨464609670439236949438861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 619479560585649265918481 464609670439236949438861)
              ·
                refine ⟨174228626414713856039573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 464609670439236949438861 174228626414713856039573)
                ·
                  refine ⟨8166966863189712001855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 174228626414713856039573 8166966863189712001855)
                  ·
                    rfl

theorem cell22_71573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 3, 6].length) (baseStart_71573 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_71573 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_71573 prefixEnd_71573 := by exact prefixLift 71573
  have htrace : WordTrace (prefixWord ++ tailWord_71573) baseStart_71573 baseEnd_71573 := by
    simpa [prefixWord, tailWord_71573, baseEnd_71573] using wordTrace_append hprefix tailTrace_71573
  have hstable : (prefixWord ++ tailWord_71573).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_71573).length < 2 ^ (prefixWord ++ tailWord_71573).sum := by decide
  have hdescent : baseEnd_71573 < baseStart_71573 := by decide
  rcases family_descends (prefixWord ++ tailWord_71573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_71603 : List Nat := [1, 1, 1, 2, 3, 1, 5, 1, 1, 6]
def baseStart_71603 : Nat := 118140960795 + 71603 * 2 ^ 59
def prefixEnd_71603 : Nat := 4983230072969 + 3 ^ 40 * 71603 * 2
def baseEnd_71603 : Nat := 24511170202659057755473

theorem tailTrace_71603 : CollatzResearch.WordTrace tailWord_71603 prefixEnd_71603 24511170202659057755473 := by
  unfold tailWord_71603
  simp only [CollatzResearch.WordTrace]
  refine ⟨2611575959602034663923463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1741050639734689775948975 2611575959602034663923463)
  ·
    refine ⟨3917363939403051995885195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2611575959602034663923463 3917363939403051995885195)
    ·
      refine ⟨5876045909104577993827793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3917363939403051995885195 5876045909104577993827793)
      ·
        refine ⟨4407034431828433495370845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5876045909104577993827793 4407034431828433495370845)
        ·
          refine ⟨1652637911935662560764067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4407034431828433495370845 1652637911935662560764067)
          ·
            refine ⟨2478956867903493841146101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1652637911935662560764067 2478956867903493841146101)
            ·
              refine ⟨232402206365952547607447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2478956867903493841146101 232402206365952547607447)
              ·
                refine ⟨348603309548928821411171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 232402206365952547607447 348603309548928821411171)
                ·
                  refine ⟨522904964323393232116757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 348603309548928821411171 522904964323393232116757)
                  ·
                    refine ⟨24511170202659057755473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 522904964323393232116757 24511170202659057755473)
                    ·
                      rfl

theorem cell22_71603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 5, 1, 1, 6].length) (baseStart_71603 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_71603 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_71603 prefixEnd_71603 := by exact prefixLift 71603
  have htrace : WordTrace (prefixWord ++ tailWord_71603) baseStart_71603 baseEnd_71603 := by
    simpa [prefixWord, tailWord_71603, baseEnd_71603] using wordTrace_append hprefix tailTrace_71603
  have hstable : (prefixWord ++ tailWord_71603).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_71603).length < 2 ^ (prefixWord ++ tailWord_71603).sum := by decide
  have hdescent : baseEnd_71603 < baseStart_71603 := by decide
  rcases family_descends (prefixWord ++ tailWord_71603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_71605 : List Nat := [1, 3, 3, 2, 1, 2, 2, 2, 1, 5]
def baseStart_71605 : Nat := 118140960795 + 71605 * 2 ^ 59
def prefixEnd_71605 : Nat := 4983230072969 + 3 ^ 40 * 71605 * 2
def baseEnd_71605 : Nat := 24511854843531719205467

theorem tailTrace_71605 : CollatzResearch.WordTrace tailWord_71605 prefixEnd_71605 24511854843531719205467 := by
  unfold tailWord_71605
  simp only [CollatzResearch.WordTrace]
  refine ⟨2611648905594789005496269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1741099270396526003664179 2611648905594789005496269)
  ·
    refine ⟨979368339598045877061101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2611648905594789005496269 979368339598045877061101)
    ·
      refine ⟨367263127349267203897913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 979368339598045877061101 367263127349267203897913)
      ·
        refine ⟨275447345511950402923435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 367263127349267203897913 275447345511950402923435)
        ·
          refine ⟨413171018267925604385153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 275447345511950402923435 413171018267925604385153)
          ·
            refine ⟨309878263700944203288865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 413171018267925604385153 309878263700944203288865)
            ·
              refine ⟨232408697775708152466649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 309878263700944203288865 232408697775708152466649)
              ·
                refine ⟨174306523331781114349987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 232408697775708152466649 174306523331781114349987)
                ·
                  refine ⟨261459784997671671524981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 174306523331781114349987 261459784997671671524981)
                  ·
                    refine ⟨24511854843531719205467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 261459784997671671524981 24511854843531719205467)
                    ·
                      rfl

theorem cell22_71605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 2, 2, 1, 5].length) (baseStart_71605 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_71605 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_71605 prefixEnd_71605 := by exact prefixLift 71605
  have htrace : WordTrace (prefixWord ++ tailWord_71605) baseStart_71605 baseEnd_71605 := by
    simpa [prefixWord, tailWord_71605, baseEnd_71605] using wordTrace_append hprefix tailTrace_71605
  have hstable : (prefixWord ++ tailWord_71605).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_71605).length < 2 ^ (prefixWord ++ tailWord_71605).sum := by decide
  have hdescent : baseEnd_71605 < baseStart_71605 := by decide
  rcases family_descends (prefixWord ++ tailWord_71605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_71648 : List Nat := [2, 1, 1, 3, 1, 1, 1, 4, 2, 6]
def baseStart_71648 : Nat := 118140960795 + 71648 * 2 ^ 59
def prefixEnd_71648 : Nat := 4983230072969 + 3 ^ 40 * 71648 * 2
def baseEnd_71648 : Nat := 24526574622293940380335

theorem tailTrace_71648 : CollatzResearch.WordTrace tailWord_71648 prefixEnd_71648 24526574622293940380335 := by
  unfold tailWord_71648
  simp only [CollatzResearch.WordTrace]
  refine ⟨1306608622219503674655799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1742144829626004899541065 1306608622219503674655799)
  ·
    refine ⟨1959912933329255511983699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1306608622219503674655799 1959912933329255511983699)
    ·
      refine ⟨2939869399993883267975549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1959912933329255511983699 2939869399993883267975549)
      ·
        refine ⟨1102451024997706225490831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2939869399993883267975549 1102451024997706225490831)
        ·
          refine ⟨1653676537496559338236247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1102451024997706225490831 1653676537496559338236247)
          ·
            refine ⟨2480514806244839007354371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1653676537496559338236247 2480514806244839007354371)
            ·
              refine ⟨3720772209367258511031557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2480514806244839007354371 3720772209367258511031557)
              ·
                refine ⟨697644789256360970818417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3720772209367258511031557 697644789256360970818417)
                ·
                  refine ⟨523233591942270728113813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 697644789256360970818417 523233591942270728113813)
                  ·
                    refine ⟨24526574622293940380335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 523233591942270728113813 24526574622293940380335)
                    ·
                      rfl

theorem cell22_71648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 4, 2, 6].length) (baseStart_71648 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_71648 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_71648 prefixEnd_71648 := by exact prefixLift 71648
  have htrace : WordTrace (prefixWord ++ tailWord_71648) baseStart_71648 baseEnd_71648 := by
    simpa [prefixWord, tailWord_71648, baseEnd_71648] using wordTrace_append hprefix tailTrace_71648
  have hstable : (prefixWord ++ tailWord_71648).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_71648).length < 2 ^ (prefixWord ++ tailWord_71648).sum := by decide
  have hdescent : baseEnd_71648 < baseStart_71648 := by decide
  rcases family_descends (prefixWord ++ tailWord_71648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_71663 : List Nat := [1, 1, 2, 1, 4, 2, 1, 1, 9]
def baseStart_71663 : Nat := 118140960795 + 71663 * 2 ^ 59
def prefixEnd_71663 : Nat := 4983230072969 + 3 ^ 40 * 71663 * 2
def baseEnd_71663 : Nat := 8177236476279633751763

theorem tailTrace_71663 : CollatzResearch.WordTrace tailWord_71663 prefixEnd_71663 8177236476279633751763 := by
  unfold tailWord_71663
  simp only [CollatzResearch.WordTrace]
  refine ⟨2613764339384664911107643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1742509559589776607405095 2613764339384664911107643)
  ·
    refine ⟨3920646509076997366661465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2613764339384664911107643 3920646509076997366661465)
    ·
      refine ⟨2940484881807748024996099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3920646509076997366661465 2940484881807748024996099)
      ·
        refine ⟨4410727322711622037494149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2940484881807748024996099 4410727322711622037494149)
        ·
          refine ⟨827011373008429132030153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4410727322711622037494149 827011373008429132030153)
          ·
            refine ⟨620258529756321849022615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 827011373008429132030153 620258529756321849022615)
            ·
              refine ⟨930387794634482773533923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 620258529756321849022615 930387794634482773533923)
              ·
                refine ⟨1395581691951724160300885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 930387794634482773533923 1395581691951724160300885)
                ·
                  refine ⟨8177236476279633751763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 1395581691951724160300885 8177236476279633751763)
                  ·
                    rfl

theorem cell22_71663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 1, 9].length) (baseStart_71663 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_71663 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_71663 prefixEnd_71663 := by exact prefixLift 71663
  have htrace : WordTrace (prefixWord ++ tailWord_71663) baseStart_71663 baseEnd_71663 := by
    simpa [prefixWord, tailWord_71663, baseEnd_71663] using wordTrace_append hprefix tailTrace_71663
  have hstable : (prefixWord ++ tailWord_71663).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_71663).length < 2 ^ (prefixWord ++ tailWord_71663).sum := by decide
  have hdescent : baseEnd_71663 < baseStart_71663 := by decide
  rcases family_descends (prefixWord ++ tailWord_71663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_71740 : List Nat := [2, 2, 2, 2, 2, 1, 1, 2, 3, 5]
def baseStart_71740 : Nat := 118140960795 + 71740 * 2 ^ 59
def prefixEnd_71740 : Nat := 4983230072969 + 3 ^ 40 * 71740 * 2
def baseEnd_71740 : Nat := 24558068102436367080053

theorem tailTrace_71740 : CollatzResearch.WordTrace tailWord_71740 prefixEnd_71740 24558068102436367080053 := by
  unfold tailWord_71740
  simp only [CollatzResearch.WordTrace]
  refine ⟨1308286380052853530830337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1744381840070471374440449 1308286380052853530830337)
  ·
    refine ⟨981214785039640148122753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1308286380052853530830337 981214785039640148122753)
    ·
      refine ⟨735911088779730111092065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 981214785039640148122753 735911088779730111092065)
      ·
        refine ⟨551933316584797583319049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 735911088779730111092065 551933316584797583319049)
        ·
          refine ⟨413949987438598187489287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 551933316584797583319049 413949987438598187489287)
          ·
            refine ⟨620924981157897281233931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 413949987438598187489287 620924981157897281233931)
            ·
              refine ⟨931387471736845921850897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 620924981157897281233931 931387471736845921850897)
              ·
                refine ⟨698540603802634441388173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 931387471736845921850897 698540603802634441388173)
                ·
                  refine ⟨261952726425987915520565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 698540603802634441388173 261952726425987915520565)
                  ·
                    refine ⟨24558068102436367080053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 261952726425987915520565 24558068102436367080053)
                    ·
                      rfl

theorem cell22_71740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 2, 3, 5].length) (baseStart_71740 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_71740 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_71740 prefixEnd_71740 := by exact prefixLift 71740
  have htrace : WordTrace (prefixWord ++ tailWord_71740) baseStart_71740 baseEnd_71740 := by
    simpa [prefixWord, tailWord_71740, baseEnd_71740] using wordTrace_append hprefix tailTrace_71740
  have hstable : (prefixWord ++ tailWord_71740).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_71740).length < 2 ^ (prefixWord ++ tailWord_71740).sum := by decide
  have hdescent : baseEnd_71740 < baseStart_71740 := by decide
  rcases family_descends (prefixWord ++ tailWord_71740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_71772 : List Nat := [2, 2, 4, 1, 1, 3, 1, 1, 1, 6]
def baseStart_71772 : Nat := 118140960795 + 71772 * 2 ^ 59
def prefixEnd_71772 : Nat := 4983230072969 + 3 ^ 40 * 71772 * 2
def baseEnd_71772 : Nat := 24569022356398950279955

theorem tailTrace_71772 : CollatzResearch.WordTrace tailWord_71772 prefixEnd_71772 24569022356398950279955 := by
  unfold tailWord_71772
  simp only [CollatzResearch.WordTrace]
  refine ⟨1308869947994888263412785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1745159930659851017883713 1308869947994888263412785)
  ·
    refine ⟨981652460996166197559589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1308869947994888263412785 981652460996166197559589)
    ·
      refine ⟨184059836436781162042423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 981652460996166197559589 184059836436781162042423)
      ·
        refine ⟨276089754655171743063635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 184059836436781162042423 276089754655171743063635)
        ·
          refine ⟨414134631982757614595453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 276089754655171743063635 414134631982757614595453)
          ·
            refine ⟨155300486993534105473295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 414134631982757614595453 155300486993534105473295)
            ·
              refine ⟨232950730490301158209943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 155300486993534105473295 232950730490301158209943)
              ·
                refine ⟨349426095735451737314915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 232950730490301158209943 349426095735451737314915)
                ·
                  refine ⟨524139143603177605972373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 349426095735451737314915 524139143603177605972373)
                  ·
                    refine ⟨24569022356398950279955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 524139143603177605972373 24569022356398950279955)
                    ·
                      rfl

theorem cell22_71772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 1, 1, 1, 6].length) (baseStart_71772 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_71772 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_71772 prefixEnd_71772 := by exact prefixLift 71772
  have htrace : WordTrace (prefixWord ++ tailWord_71772) baseStart_71772 baseEnd_71772 := by
    simpa [prefixWord, tailWord_71772, baseEnd_71772] using wordTrace_append hprefix tailTrace_71772
  have hstable : (prefixWord ++ tailWord_71772).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_71772).length < 2 ^ (prefixWord ++ tailWord_71772).sum := by decide
  have hdescent : baseEnd_71772 < baseStart_71772 := by decide
  rcases family_descends (prefixWord ++ tailWord_71772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_71778 : List Nat := [3, 3, 2, 2, 2, 2, 2, 1, 1, 4]
def baseStart_71778 : Nat := 118140960795 + 71778 * 2 ^ 59
def prefixEnd_71778 : Nat := 4983230072969 + 3 ^ 40 * 71778 * 2
def baseEnd_71778 : Nat := 24571076279016934629937

theorem tailTrace_71778 : CollatzResearch.WordTrace tailWord_71778 prefixEnd_71778 24571076279016934629937 := by
  unfold tailWord_71778
  simp only [CollatzResearch.WordTrace]
  refine ⟨654489683492009887885997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1745305822645359701029325 654489683492009887885997)
  ·
    refine ⟨245433631309503707957249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 654489683492009887885997 245433631309503707957249)
    ·
      refine ⟨184075223482127780967937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 245433631309503707957249 184075223482127780967937)
      ·
        refine ⟨138056417611595835725953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 184075223482127780967937 138056417611595835725953)
        ·
          refine ⟨103542313208696876794465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 138056417611595835725953 103542313208696876794465)
          ·
            refine ⟨77656734906522657595849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 103542313208696876794465 77656734906522657595849)
            ·
              refine ⟨58242551179891993196887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 77656734906522657595849 58242551179891993196887)
              ·
                refine ⟨87363826769837989795331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58242551179891993196887 87363826769837989795331)
                ·
                  refine ⟨131045740154756984692997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 87363826769837989795331 131045740154756984692997)
                  ·
                    refine ⟨24571076279016934629937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 131045740154756984692997 24571076279016934629937)
                    ·
                      rfl

theorem cell22_71778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 2, 2, 1, 1, 4].length) (baseStart_71778 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_71778 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_71778 prefixEnd_71778 := by exact prefixLift 71778
  have htrace : WordTrace (prefixWord ++ tailWord_71778) baseStart_71778 baseEnd_71778 := by
    simpa [prefixWord, tailWord_71778, baseEnd_71778] using wordTrace_append hprefix tailTrace_71778
  have hstable : (prefixWord ++ tailWord_71778).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_71778).length < 2 ^ (prefixWord ++ tailWord_71778).sum := by decide
  have hdescent : baseEnd_71778 < baseStart_71778 := by decide
  rcases family_descends (prefixWord ++ tailWord_71778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_71896 : List Nat := [2, 1, 2, 2, 4, 2, 3, 1, 1, 4]
def baseStart_71896 : Nat := 118140960795 + 71896 * 2 ^ 59
def prefixEnd_71896 : Nat := 4983230072969 + 3 ^ 40 * 71896 * 2
def baseEnd_71896 : Nat := 24611470090503960179575

theorem tailTrace_71896 : CollatzResearch.WordTrace tailWord_71896 prefixEnd_71896 24611470090503960179575 := by
  unfold tailWord_71896
  simp only [CollatzResearch.WordTrace]
  refine ⟨1311131273770272852169771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1748175031693697136226361 1311131273770272852169771)
  ·
    refine ⟨1966696910655409278254657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1311131273770272852169771 1966696910655409278254657)
    ·
      refine ⟨1475022682991556958690993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1966696910655409278254657 1475022682991556958690993)
      ·
        refine ⟨1106267012243667719018245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1475022682991556958690993 1106267012243667719018245)
        ·
          refine ⟨207425064795687697315921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1106267012243667719018245 207425064795687697315921)
          ·
            refine ⟨155568798596765772986941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 207425064795687697315921 155568798596765772986941)
            ·
              refine ⟨58338299473787164870103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 155568798596765772986941 58338299473787164870103)
              ·
                refine ⟨87507449210680747305155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58338299473787164870103 87507449210680747305155)
                ·
                  refine ⟨131261173816021120957733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 87507449210680747305155 131261173816021120957733)
                  ·
                    refine ⟨24611470090503960179575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 131261173816021120957733 24611470090503960179575)
                    ·
                      rfl

theorem cell22_71896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 3, 1, 1, 4].length) (baseStart_71896 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_71896 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_71896 prefixEnd_71896 := by exact prefixLift 71896
  have htrace : WordTrace (prefixWord ++ tailWord_71896) baseStart_71896 baseEnd_71896 := by
    simpa [prefixWord, tailWord_71896, baseEnd_71896] using wordTrace_append hprefix tailTrace_71896
  have hstable : (prefixWord ++ tailWord_71896).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_71896).length < 2 ^ (prefixWord ++ tailWord_71896).sum := by decide
  have hdescent : baseEnd_71896 < baseStart_71896 := by decide
  rcases family_descends (prefixWord ++ tailWord_71896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_71911 : List Nat := [1, 1, 5, 3, 1, 2, 1, 4, 4]
def baseStart_71911 : Nat := 118140960795 + 71911 * 2 ^ 59
def prefixEnd_71911 : Nat := 4983230072969 + 3 ^ 40 * 71911 * 2
def baseEnd_71911 : Nat := 8205534965682973684843

theorem tailTrace_71911 : CollatzResearch.WordTrace tailWord_71911 prefixEnd_71911 8205534965682973684843 := by
  unfold tailWord_71911
  simp only [CollatzResearch.WordTrace]
  refine ⟨2622809642486203266135587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1748539761657468844090391 2622809642486203266135587)
  ·
    refine ⟨3934214463729304899203381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2622809642486203266135587 3934214463729304899203381)
    ·
      refine ⟨368832605974622334300317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3934214463729304899203381 368832605974622334300317)
      ·
        refine ⟨138312227240483375362619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 368832605974622334300317 138312227240483375362619)
        ·
          refine ⟨207468340860725063043929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138312227240483375362619 207468340860725063043929)
          ·
            refine ⟨155601255645543797282947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 207468340860725063043929 155601255645543797282947)
            ·
              refine ⟨233401883468315695924421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 155601255645543797282947 233401883468315695924421)
              ·
                refine ⟨43762853150309192985829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 233401883468315695924421 43762853150309192985829)
                ·
                  refine ⟨8205534965682973684843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 43762853150309192985829 8205534965682973684843)
                  ·
                    rfl

theorem cell22_71911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 1, 4, 4].length) (baseStart_71911 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_71911 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_71911 prefixEnd_71911 := by exact prefixLift 71911
  have htrace : WordTrace (prefixWord ++ tailWord_71911) baseStart_71911 baseEnd_71911 := by
    simpa [prefixWord, tailWord_71911, baseEnd_71911] using wordTrace_append hprefix tailTrace_71911
  have hstable : (prefixWord ++ tailWord_71911).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_71911).length < 2 ^ (prefixWord ++ tailWord_71911).sum := by decide
  have hdescent : baseEnd_71911 < baseStart_71911 := by decide
  rcases family_descends (prefixWord ++ tailWord_71911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_71926 : List Nat := [5, 1, 1, 1, 1, 1, 4, 3, 2, 3]
def baseStart_71926 : Nat := 118140960795 + 71926 * 2 ^ 59
def prefixEnd_71926 : Nat := 4983230072969 + 3 ^ 40 * 71926 * 2
def baseEnd_71926 : Nat := 24621739703593881929483

theorem tailTrace_71926 : CollatzResearch.WordTrace tailWord_71926 prefixEnd_71926 24621739703593881929483 := by
  unfold tailWord_71926
  simp only [CollatzResearch.WordTrace]
  refine ⟨163959796089491301745727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1748904491621240551954421 163959796089491301745727)
  ·
    refine ⟨245939694134236952618591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163959796089491301745727 245939694134236952618591)
    ·
      refine ⟨368909541201355428927887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 245939694134236952618591 368909541201355428927887)
      ·
        refine ⟨553364311802033143391831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 368909541201355428927887 553364311802033143391831)
        ·
          refine ⟨830046467703049715087747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 553364311802033143391831 830046467703049715087747)
          ·
            refine ⟨1245069701554574572631621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 830046467703049715087747 1245069701554574572631621)
            ·
              refine ⟨233450569041482732368429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1245069701554574572631621 233450569041482732368429)
              ·
                refine ⟨87543963390556024638161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 233450569041482732368429 87543963390556024638161)
                ·
                  refine ⟨65657972542917018478621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 87543963390556024638161 65657972542917018478621)
                  ·
                    refine ⟨24621739703593881929483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 65657972542917018478621 24621739703593881929483)
                    ·
                      rfl

theorem cell22_71926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 4, 3, 2, 3].length) (baseStart_71926 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_71926 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_71926 prefixEnd_71926 := by exact prefixLift 71926
  have htrace : WordTrace (prefixWord ++ tailWord_71926) baseStart_71926 baseEnd_71926 := by
    simpa [prefixWord, tailWord_71926, baseEnd_71926] using wordTrace_append hprefix tailTrace_71926
  have hstable : (prefixWord ++ tailWord_71926).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_71926).length < 2 ^ (prefixWord ++ tailWord_71926).sum := by decide
  have hdescent : baseEnd_71926 < baseStart_71926 := by decide
  rcases family_descends (prefixWord ++ tailWord_71926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_71971 : List Nat := [1, 1, 1, 4, 2, 2, 1, 6, 1, 3]
def baseStart_71971 : Nat := 118140960795 + 71971 * 2 ^ 59
def prefixEnd_71971 : Nat := 4983230072969 + 3 ^ 40 * 71971 * 2
def baseEnd_71971 : Nat := 24637144123228764554345

theorem tailTrace_71971 : CollatzResearch.WordTrace tailWord_71971 prefixEnd_71971 24637144123228764554345 := by
  unfold tailWord_71971
  simp only [CollatzResearch.WordTrace]
  refine ⟨2624998022268833513319767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1749998681512555675546511 2624998022268833513319767)
  ·
    refine ⟨3937497033403250269979651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2624998022268833513319767 3937497033403250269979651)
    ·
      refine ⟨5906245550104875404969477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3937497033403250269979651 5906245550104875404969477)
      ·
        refine ⟨1107421040644664138431777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5906245550104875404969477 1107421040644664138431777)
        ·
          refine ⟨830565780483498103823833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1107421040644664138431777 830565780483498103823833)
          ·
            refine ⟨622924335362623577867875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 830565780483498103823833 622924335362623577867875)
            ·
              refine ⟨934386503043935366801813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 622924335362623577867875 934386503043935366801813)
              ·
                refine ⟨43799367330184470318835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 934386503043935366801813 43799367330184470318835)
                ·
                  refine ⟨65699050995276705478253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43799367330184470318835 65699050995276705478253)
                  ·
                    refine ⟨24637144123228764554345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 65699050995276705478253 24637144123228764554345)
                    ·
                      rfl

theorem cell22_71971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 6, 1, 3].length) (baseStart_71971 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_71971 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_71971 prefixEnd_71971 := by exact prefixLift 71971
  have htrace : WordTrace (prefixWord ++ tailWord_71971) baseStart_71971 baseEnd_71971 := by
    simpa [prefixWord, tailWord_71971, baseEnd_71971] using wordTrace_append hprefix tailTrace_71971
  have hstable : (prefixWord ++ tailWord_71971).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_71971).length < 2 ^ (prefixWord ++ tailWord_71971).sum := by decide
  have hdescent : baseEnd_71971 < baseStart_71971 := by decide
  rcases family_descends (prefixWord ++ tailWord_71971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_72059 : List Nat := [1, 1, 1, 1, 1, 7, 1, 3, 2, 4]
def baseStart_72059 : Nat := 118140960795 + 72059 * 2 ^ 59
def prefixEnd_72059 : Nat := 4983230072969 + 3 ^ 40 * 72059 * 2
def baseEnd_72059 : Nat := 24667268321625868354075

theorem tailTrace_72059 : CollatzResearch.WordTrace tailWord_72059 prefixEnd_72059 24667268321625868354075 := by
  unfold tailWord_72059
  simp only [CollatzResearch.WordTrace]
  refine ⟨2628207645950024542523231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1752138430633349695015487 2628207645950024542523231)
  ·
    refine ⟨3942311468925036813784847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2628207645950024542523231 3942311468925036813784847)
    ·
      refine ⟨5913467203387555220677271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3942311468925036813784847 5913467203387555220677271)
      ·
        refine ⟨8870200805081332831015907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5913467203387555220677271 8870200805081332831015907)
        ·
          refine ⟨13305301207621999246523861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8870200805081332831015907 13305301207621999246523861)
          ·
            refine ⟨311842997053640607340403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 13305301207621999246523861 311842997053640607340403)
            ·
              refine ⟨467764495580460911010605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 311842997053640607340403 467764495580460911010605)
              ·
                refine ⟨175411685842672841628977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 467764495580460911010605 175411685842672841628977)
                ·
                  refine ⟨131558764382004631221733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 175411685842672841628977 131558764382004631221733)
                  ·
                    refine ⟨24667268321625868354075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 131558764382004631221733 24667268321625868354075)
                    ·
                      rfl

theorem cell22_72059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 3, 2, 4].length) (baseStart_72059 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_72059 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_72059 prefixEnd_72059 := by exact prefixLift 72059
  have htrace : WordTrace (prefixWord ++ tailWord_72059) baseStart_72059 baseEnd_72059 := by
    simpa [prefixWord, tailWord_72059, baseEnd_72059] using wordTrace_append hprefix tailTrace_72059
  have hstable : (prefixWord ++ tailWord_72059).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_72059).length < 2 ^ (prefixWord ++ tailWord_72059).sum := by decide
  have hdescent : baseEnd_72059 < baseStart_72059 := by decide
  rcases family_descends (prefixWord ++ tailWord_72059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_72074 : List Nat := [3, 1, 2, 5, 11]
def baseStart_72074 : Nat := 118140960795 + 72074 * 2 ^ 59
def prefixEnd_72074 : Nat := 4983230072969 + 3 ^ 40 * 72074 * 2
def baseEnd_72074 : Nat := 101532523161196828103

theorem tailTrace_72074 : CollatzResearch.WordTrace tailWord_72074 prefixEnd_72074 101532523161196828103 := by
  unfold tailWord_72074
  simp only [CollatzResearch.WordTrace]
  refine ⟨657188685223920526079819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1752503160597121402879517 657188685223920526079819)
  ·
    refine ⟨985783027835880789119729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 657188685223920526079819 985783027835880789119729)
    ·
      refine ⟨739337270876910591839797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 985783027835880789119729 739337270876910591839797)
      ·
        refine ⟨69312869144710367984981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 739337270876910591839797 69312869144710367984981)
        ·
          refine ⟨101532523161196828103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 69312869144710367984981 101532523161196828103)
          ·
            rfl

theorem cell22_72074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 11].length) (baseStart_72074 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_72074 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_72074 prefixEnd_72074 := by exact prefixLift 72074
  have htrace : WordTrace (prefixWord ++ tailWord_72074) baseStart_72074 baseEnd_72074 := by
    simpa [prefixWord, tailWord_72074, baseEnd_72074] using wordTrace_append hprefix tailTrace_72074
  have hstable : (prefixWord ++ tailWord_72074).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_72074).length < 2 ^ (prefixWord ++ tailWord_72074).sum := by decide
  have hdescent : baseEnd_72074 < baseStart_72074 := by decide
  rcases family_descends (prefixWord ++ tailWord_72074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_72078 : List Nat := [4, 1, 1, 4, 1, 1, 1, 4, 2, 3]
def baseStart_72078 : Nat := 118140960795 + 72078 * 2 ^ 59
def prefixEnd_72078 : Nat := 4983230072969 + 3 ^ 40 * 72078 * 2
def baseEnd_72078 : Nat := 24673772409916152129017

theorem tailTrace_72078 : CollatzResearch.WordTrace tailWord_72078 prefixEnd_72078 24673772409916152129017 := by
  unfold tailWord_72078
  simp only [CollatzResearch.WordTrace]
  refine ⟨328612579110148848433111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1752600421920793858309925 328612579110148848433111)
  ·
    refine ⟨492918868665223272649667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 328612579110148848433111 492918868665223272649667)
    ·
      refine ⟨739378302997834908974501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 492918868665223272649667 739378302997834908974501)
      ·
        refine ⟨138633431812094045432719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 739378302997834908974501 138633431812094045432719)
        ·
          refine ⟨207950147718141068149079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138633431812094045432719 207950147718141068149079)
          ·
            refine ⟨311925221577211602223619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 207950147718141068149079 311925221577211602223619)
            ·
              refine ⟨467887832365817403335429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 311925221577211602223619 467887832365817403335429)
              ·
                refine ⟨87728968568590763125393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 467887832365817403335429 87728968568590763125393)
                ·
                  refine ⟨65796726426443072344045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 87728968568590763125393 65796726426443072344045)
                  ·
                    refine ⟨24673772409916152129017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 65796726426443072344045 24673772409916152129017)
                    ·
                      rfl

theorem cell22_72078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 4, 2, 3].length) (baseStart_72078 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_72078 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_72078 prefixEnd_72078 := by exact prefixLift 72078
  have htrace : WordTrace (prefixWord ++ tailWord_72078) baseStart_72078 baseEnd_72078 := by
    simpa [prefixWord, tailWord_72078, baseEnd_72078] using wordTrace_append hprefix tailTrace_72078
  have hstable : (prefixWord ++ tailWord_72078).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_72078).length < 2 ^ (prefixWord ++ tailWord_72078).sum := by decide
  have hdescent : baseEnd_72078 < baseStart_72078 := by decide
  rcases family_descends (prefixWord ++ tailWord_72078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_72129 : List Nat := [1, 2, 7, 1, 1, 2, 1, 2, 2, 3]
def baseStart_72129 : Nat := 118140960795 + 72129 * 2 ^ 59
def prefixEnd_72129 : Nat := 4983230072969 + 3 ^ 40 * 72129 * 2
def baseEnd_72129 : Nat := 24691230752169019103861

theorem tailTrace_72129 : CollatzResearch.WordTrace tailWord_72129 prefixEnd_72129 24691230752169019103861 := by
  unfold tailWord_72129
  simp only [CollatzResearch.WordTrace]
  refine ⟨2630760755696426497571441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1753840503797617665047627 2630760755696426497571441)
  ·
    refine ⟨1973070566772319873178581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2630760755696426497571441 1973070566772319873178581)
    ·
      refine ⟨46243841408726247027623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 1973070566772319873178581 46243841408726247027623)
      ·
        refine ⟨69365762113089370541435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46243841408726247027623 69365762113089370541435)
        ·
          refine ⟨104048643169634055812153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69365762113089370541435 104048643169634055812153)
          ·
            refine ⟨78036482377225541859115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 104048643169634055812153 78036482377225541859115)
            ·
              refine ⟨117054723565838312788673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78036482377225541859115 117054723565838312788673)
              ·
                refine ⟨87791042674378734591505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 117054723565838312788673 87791042674378734591505)
                ·
                  refine ⟨65843282005784050943629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 87791042674378734591505 65843282005784050943629)
                  ·
                    refine ⟨24691230752169019103861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 65843282005784050943629 24691230752169019103861)
                    ·
                      rfl

theorem cell22_72129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 2, 1, 2, 2, 3].length) (baseStart_72129 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_72129 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_72129 prefixEnd_72129 := by exact prefixLift 72129
  have htrace : WordTrace (prefixWord ++ tailWord_72129) baseStart_72129 baseEnd_72129 := by
    simpa [prefixWord, tailWord_72129, baseEnd_72129] using wordTrace_append hprefix tailTrace_72129
  have hstable : (prefixWord ++ tailWord_72129).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_72129).length < 2 ^ (prefixWord ++ tailWord_72129).sum := by decide
  have hdescent : baseEnd_72129 < baseStart_72129 := by decide
  rcases family_descends (prefixWord ++ tailWord_72129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_72136 : List Nat := [2, 1, 3, 1, 3, 2, 3, 2, 5]
def baseStart_72136 : Nat := 118140960795 + 72136 * 2 ^ 59
def prefixEnd_72136 : Nat := 4983230072969 + 3 ^ 40 * 72136 * 2
def baseEnd_72136 : Nat := 8231208998407778059613

theorem tailTrace_72136 : CollatzResearch.WordTrace tailWord_72136 prefixEnd_72136 8231208998407778059613 := by
  unfold tailWord_72136
  simp only [CollatzResearch.WordTrace]
  refine ⟨1315508033335533346538131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1754010711114044462050841 1315508033335533346538131)
  ·
    refine ⟨1973262050003300019807197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1315508033335533346538131 1973262050003300019807197)
    ·
      refine ⟨739973268751237507427699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1973262050003300019807197 739973268751237507427699)
      ·
        refine ⟨1109959903126856261141549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 739973268751237507427699 1109959903126856261141549)
        ·
          refine ⟨416234963672571097928081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1109959903126856261141549 416234963672571097928081)
          ·
            refine ⟨312176222754428323446061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 416234963672571097928081 312176222754428323446061)
            ·
              refine ⟨117066083532910621292273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 312176222754428323446061 117066083532910621292273)
              ·
                refine ⟨87799562649682965969205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 117066083532910621292273 87799562649682965969205)
                ·
                  refine ⟨8231208998407778059613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 87799562649682965969205 8231208998407778059613)
                  ·
                    rfl

theorem cell22_72136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 3, 2, 5].length) (baseStart_72136 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_72136 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_72136 prefixEnd_72136 := by exact prefixLift 72136
  have htrace : WordTrace (prefixWord ++ tailWord_72136) baseStart_72136 baseEnd_72136 := by
    simpa [prefixWord, tailWord_72136, baseEnd_72136] using wordTrace_append hprefix tailTrace_72136
  have hstable : (prefixWord ++ tailWord_72136).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_72136).length < 2 ^ (prefixWord ++ tailWord_72136).sum := by decide
  have hdescent : baseEnd_72136 < baseStart_72136 := by decide
  rcases family_descends (prefixWord ++ tailWord_72136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_72179 : List Nat := [1, 1, 1, 2, 2, 2, 4, 1, 3, 5]
def baseStart_72179 : Nat := 118140960795 + 72179 * 2 ^ 59
def prefixEnd_72179 : Nat := 4983230072969 + 3 ^ 40 * 72179 * 2
def baseEnd_72179 : Nat := 24708346773985555353707

theorem tailTrace_72179 : CollatzResearch.WordTrace tailWord_72179 prefixEnd_72179 24708346773985555353707 := by
  unfold tailWord_72179
  simp only [CollatzResearch.WordTrace]
  refine ⟨2632584405515285036891591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1755056270343523357927727 2632584405515285036891591)
  ·
    refine ⟨3948876608272927555337387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2632584405515285036891591 3948876608272927555337387)
    ·
      refine ⟨5923314912409391333006081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3948876608272927555337387 5923314912409391333006081)
      ·
        refine ⟨4442486184307043499754561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5923314912409391333006081 4442486184307043499754561)
        ·
          refine ⟨3331864638230282624815921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4442486184307043499754561 3331864638230282624815921)
          ·
            refine ⟨2498898478672711968611941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3331864638230282624815921 2498898478672711968611941)
            ·
              refine ⟨468543464751133494114739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2498898478672711968611941 468543464751133494114739)
              ·
                refine ⟨702815197126700241172109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 468543464751133494114739 702815197126700241172109)
                ·
                  refine ⟨263555698922512590439541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 702815197126700241172109 263555698922512590439541)
                  ·
                    refine ⟨24708346773985555353707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 263555698922512590439541 24708346773985555353707)
                    ·
                      rfl

theorem cell22_72179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 1, 3, 5].length) (baseStart_72179 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_72179 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_72179 prefixEnd_72179 := by exact prefixLift 72179
  have htrace : WordTrace (prefixWord ++ tailWord_72179) baseStart_72179 baseEnd_72179 := by
    simpa [prefixWord, tailWord_72179, baseEnd_72179] using wordTrace_append hprefix tailTrace_72179
  have hstable : (prefixWord ++ tailWord_72179).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_72179).length < 2 ^ (prefixWord ++ tailWord_72179).sum := by decide
  have hdescent : baseEnd_72179 < baseStart_72179 := by decide
  rcases family_descends (prefixWord ++ tailWord_72179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_72213 : List Nat := [1, 3, 2, 1, 3, 1, 3, 3, 2, 3]
def baseStart_72213 : Nat := 118140960795 + 72213 * 2 ^ 59
def prefixEnd_72213 : Nat := 4983230072969 + 3 ^ 40 * 72213 * 2
def baseEnd_72213 : Nat := 24719985668820800003603

theorem tailTrace_72213 : CollatzResearch.WordTrace tailWord_72213 prefixEnd_72213 24719985668820800003603 := by
  unfold tailWord_72213
  simp only [CollatzResearch.WordTrace]
  refine ⟨2633824487392108843629293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1755882991594739229086195 2633824487392108843629293)
  ·
    refine ⟨987684182772040816360985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2633824487392108843629293 987684182772040816360985)
    ·
      refine ⟨740763137079030612270739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 987684182772040816360985 740763137079030612270739)
      ·
        refine ⟨1111144705618545918406109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 740763137079030612270739 1111144705618545918406109)
        ·
          refine ⟨416679264606954719402291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1111144705618545918406109 416679264606954719402291)
          ·
            refine ⟨625018896910432079103437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 416679264606954719402291 625018896910432079103437)
            ·
              refine ⟨234382086341412029663789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 625018896910432079103437 234382086341412029663789)
              ·
                refine ⟨87893282378029511123921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 234382086341412029663789 87893282378029511123921)
                ·
                  refine ⟨65919961783522133342941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 87893282378029511123921 65919961783522133342941)
                  ·
                    refine ⟨24719985668820800003603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 65919961783522133342941 24719985668820800003603)
                    ·
                      rfl

theorem cell22_72213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 3, 3, 2, 3].length) (baseStart_72213 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_72213 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_72213 prefixEnd_72213 := by exact prefixLift 72213
  have htrace : WordTrace (prefixWord ++ tailWord_72213) baseStart_72213 baseEnd_72213 := by
    simpa [prefixWord, tailWord_72213, baseEnd_72213] using wordTrace_append hprefix tailTrace_72213
  have hstable : (prefixWord ++ tailWord_72213).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_72213).length < 2 ^ (prefixWord ++ tailWord_72213).sum := by decide
  have hdescent : baseEnd_72213 < baseStart_72213 := by decide
  rcases family_descends (prefixWord ++ tailWord_72213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_72239 : List Nat := [1, 1, 2, 1, 2, 1, 1, 1, 6, 6]
def baseStart_72239 : Nat := 118140960795 + 72239 * 2 ^ 59
def prefixEnd_72239 : Nat := 4983230072969 + 3 ^ 40 * 72239 * 2
def baseEnd_72239 : Nat := 24728886000165398853523

theorem tailTrace_72239 : CollatzResearch.WordTrace tailWord_72239 prefixEnd_72239 24728886000165398853523 := by
  unfold tailWord_72239
  simp only [CollatzResearch.WordTrace]
  refine ⟨2634772785297915284075771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1756515190198610189383847 2634772785297915284075771)
  ·
    refine ⟨3952159177946872926113657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2634772785297915284075771 3952159177946872926113657)
    ·
      refine ⟨2964119383460154694585243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3952159177946872926113657 2964119383460154694585243)
      ·
        refine ⟨4446179075190232041877865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2964119383460154694585243 4446179075190232041877865)
        ·
          refine ⟨3334634306392674031408399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4446179075190232041877865 3334634306392674031408399)
          ·
            refine ⟨5001951459589011047112599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3334634306392674031408399 5001951459589011047112599)
            ·
              refine ⟨7502927189383516570668899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5001951459589011047112599 7502927189383516570668899)
              ·
                refine ⟨11254390784075274856003349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7502927189383516570668899 11254390784075274856003349)
                ·
                  refine ⟨527549568003528508875157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 11254390784075274856003349 527549568003528508875157)
                  ·
                    refine ⟨24728886000165398853523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 527549568003528508875157 24728886000165398853523)
                    ·
                      rfl

theorem cell22_72239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 6, 6].length) (baseStart_72239 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_72239 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_72239 prefixEnd_72239 := by exact prefixLift 72239
  have htrace : WordTrace (prefixWord ++ tailWord_72239) baseStart_72239 baseEnd_72239 := by
    simpa [prefixWord, tailWord_72239, baseEnd_72239] using wordTrace_append hprefix tailTrace_72239
  have hstable : (prefixWord ++ tailWord_72239).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_72239).length < 2 ^ (prefixWord ++ tailWord_72239).sum := by decide
  have hdescent : baseEnd_72239 < baseStart_72239 := by decide
  rcases family_descends (prefixWord ++ tailWord_72239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_72271 : List Nat := [1, 1, 2, 1, 1, 2, 6, 3, 5]
def baseStart_72271 : Nat := 118140960795 + 72271 * 2 ^ 59
def prefixEnd_72271 : Nat := 4983230072969 + 3 ^ 40 * 72271 * 2
def baseEnd_72271 : Nat := 8246613418042660684475

theorem tailTrace_72271 : CollatzResearch.WordTrace tailWord_72271 prefixEnd_72271 8246613418042660684475 := by
  unfold tailWord_72271
  simp only [CollatzResearch.WordTrace]
  refine ⟨2635939921181984749240667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1757293280787989832827111 2635939921181984749240667)
  ·
    refine ⟨3953909881772977123861001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2635939921181984749240667 3953909881772977123861001)
    ·
      refine ⟨2965432411329732842895751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3953909881772977123861001 2965432411329732842895751)
      ·
        refine ⟨4448148616994599264343627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2965432411329732842895751 4448148616994599264343627)
        ·
          refine ⟨6672222925491898896515441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4448148616994599264343627 6672222925491898896515441)
          ·
            refine ⟨5004167194118924172386581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6672222925491898896515441 5004167194118924172386581)
            ·
              refine ⟨234570337224324570580621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 5004167194118924172386581 234570337224324570580621)
              ·
                refine ⟨87963876459121713967733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 234570337224324570580621 87963876459121713967733)
                ·
                  refine ⟨8246613418042660684475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 87963876459121713967733 8246613418042660684475)
                  ·
                    rfl

theorem cell22_72271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 6, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 6, 3, 5].length) (baseStart_72271 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_72271 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_72271 prefixEnd_72271 := by exact prefixLift 72271
  have htrace : WordTrace (prefixWord ++ tailWord_72271) baseStart_72271 baseEnd_72271 := by
    simpa [prefixWord, tailWord_72271, baseEnd_72271] using wordTrace_append hprefix tailTrace_72271
  have hstable : (prefixWord ++ tailWord_72271).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_72271).length < 2 ^ (prefixWord ++ tailWord_72271).sum := by decide
  have hdescent : baseEnd_72271 < baseStart_72271 := by decide
  rcases family_descends (prefixWord ++ tailWord_72271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_72316 : List Nat := [2, 2, 2, 1, 1, 2, 3, 3, 6]
def baseStart_72316 : Nat := 118140960795 + 72316 * 2 ^ 59
def prefixEnd_72316 : Nat := 4983230072969 + 3 ^ 40 * 72316 * 2
def baseEnd_72316 : Nat := 8251748224587621559429

theorem tailTrace_72316 : CollatzResearch.WordTrace tailWord_72316 prefixEnd_72316 8251748224587621559429 := by
  unfold tailWord_72316
  simp only [CollatzResearch.WordTrace]
  refine ⟨1318790603009478717314401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1758387470679304956419201 1318790603009478717314401)
  ·
    refine ⟨989092952257109037985801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1318790603009478717314401 989092952257109037985801)
    ·
      refine ⟨741819714192831778489351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 989092952257109037985801 741819714192831778489351)
      ·
        refine ⟨1112729571289247667734027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 741819714192831778489351 1112729571289247667734027)
        ·
          refine ⟨1669094356933871501601041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1112729571289247667734027 1669094356933871501601041)
          ·
            refine ⟨1251820767700403626200781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1669094356933871501601041 1251820767700403626200781)
            ·
              refine ⟨469432787887651359825293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1251820767700403626200781 469432787887651359825293)
              ·
                refine ⟨176037295457869259934485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 469432787887651359825293 176037295457869259934485)
                ·
                  refine ⟨8251748224587621559429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 176037295457869259934485 8251748224587621559429)
                  ·
                    rfl

theorem cell22_72316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 3, 6].length) (baseStart_72316 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_72316 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_72316 prefixEnd_72316 := by exact prefixLift 72316
  have htrace : WordTrace (prefixWord ++ tailWord_72316) baseStart_72316 baseEnd_72316 := by
    simpa [prefixWord, tailWord_72316, baseEnd_72316] using wordTrace_append hprefix tailTrace_72316
  have hstable : (prefixWord ++ tailWord_72316).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_72316).length < 2 ^ (prefixWord ++ tailWord_72316).sum := by decide
  have hdescent : baseEnd_72316 < baseStart_72316 := by decide
  rcases family_descends (prefixWord ++ tailWord_72316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_72331 : List Nat := [1, 1, 1, 1, 4, 1, 2, 5, 1, 5]
def baseStart_72331 : Nat := 118140960795 + 72331 * 2 ^ 59
def prefixEnd_72331 : Nat := 4983230072969 + 3 ^ 40 * 72331 * 2
def baseEnd_72331 : Nat := 24760379480307825553241

theorem tailTrace_72331 : CollatzResearch.WordTrace tailWord_72331 prefixEnd_72331 24760379480307825553241 := by
  unfold tailWord_72331
  simp only [CollatzResearch.WordTrace]
  refine ⟨2638128300964614996424847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1758752200643076664283231 2638128300964614996424847)
  ·
    refine ⟨3957192451446922494637271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2638128300964614996424847 3957192451446922494637271)
    ·
      refine ⟨5935788677170383741955907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3957192451446922494637271 5935788677170383741955907)
      ·
        refine ⟨8903683015755575612933861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5935788677170383741955907 8903683015755575612933861)
        ·
          refine ⟨1669440565454170427425099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8903683015755575612933861 1669440565454170427425099)
          ·
            refine ⟨2504160848181255641137649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1669440565454170427425099 2504160848181255641137649)
            ·
              refine ⟨1878120636135941730853237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2504160848181255641137649 1878120636135941730853237)
              ·
                refine ⟨176073809637744537267491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1878120636135941730853237 176073809637744537267491)
                ·
                  refine ⟨264110714456616805901237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 176073809637744537267491 264110714456616805901237)
                  ·
                    refine ⟨24760379480307825553241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 264110714456616805901237 24760379480307825553241)
                    ·
                      rfl

theorem cell22_72331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 5, 1, 5].length) (baseStart_72331 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_72331 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_72331 prefixEnd_72331 := by exact prefixLift 72331
  have htrace : WordTrace (prefixWord ++ tailWord_72331) baseStart_72331 baseEnd_72331 := by
    simpa [prefixWord, tailWord_72331, baseEnd_72331] using wordTrace_append hprefix tailTrace_72331
  have hstable : (prefixWord ++ tailWord_72331).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_72331).length < 2 ^ (prefixWord ++ tailWord_72331).sum := by decide
  have hdescent : baseEnd_72331 < baseStart_72331 := by decide
  rcases family_descends (prefixWord ++ tailWord_72331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_72365 : List Nat := [1, 5, 2, 1, 1, 2, 2, 1, 4, 3]
def baseStart_72365 : Nat := 118140960795 + 72365 * 2 ^ 59
def prefixEnd_72365 : Nat := 4983230072969 + 3 ^ 40 * 72365 * 2
def baseEnd_72365 : Nat := 24772018375143070203137

theorem tailTrace_72365 : CollatzResearch.WordTrace tailWord_72365 prefixEnd_72365 24772018375143070203137 := by
  unfold tailWord_72365
  simp only [CollatzResearch.WordTrace]
  refine ⟨2639368382841438803162549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1759578921894292535441699 2639368382841438803162549)
  ·
    refine ⟨247440785891384887796489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2639368382841438803162549 247440785891384887796489)
    ·
      refine ⟨185580589418538665847367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 247440785891384887796489 185580589418538665847367)
      ·
        refine ⟨278370884127807998771051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 185580589418538665847367 278370884127807998771051)
        ·
          refine ⟨417556326191711998156577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 278370884127807998771051 417556326191711998156577)
          ·
            refine ⟨313167244643783998617433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 417556326191711998156577 313167244643783998617433)
            ·
              refine ⟨234875433482837998963075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 313167244643783998617433 234875433482837998963075)
              ·
                refine ⟨352313150224256998444613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 234875433482837998963075 352313150224256998444613)
                ·
                  refine ⟨66058715667048187208365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 352313150224256998444613 66058715667048187208365)
                  ·
                    refine ⟨24772018375143070203137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 66058715667048187208365 24772018375143070203137)
                    ·
                      rfl

theorem cell22_72365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 2, 1, 4, 3].length) (baseStart_72365 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_72365 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_72365 prefixEnd_72365 := by exact prefixLift 72365
  have htrace : WordTrace (prefixWord ++ tailWord_72365) baseStart_72365 baseEnd_72365 := by
    simpa [prefixWord, tailWord_72365, baseEnd_72365] using wordTrace_append hprefix tailTrace_72365
  have hstable : (prefixWord ++ tailWord_72365).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_72365).length < 2 ^ (prefixWord ++ tailWord_72365).sum := by decide
  have hdescent : baseEnd_72365 < baseStart_72365 := by decide
  rcases family_descends (prefixWord ++ tailWord_72365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_72391 : List Nat := [1, 1, 4, 1, 1, 1, 2, 1, 4, 6]
def baseStart_72391 : Nat := 118140960795 + 72391 * 2 ^ 59
def prefixEnd_72391 : Nat := 4983230072969 + 3 ^ 40 * 72391 * 2
def baseEnd_72391 : Nat := 24780918706487669053057

theorem tailTrace_72391 : CollatzResearch.WordTrace tailWord_72391 prefixEnd_72391 24780918706487669053057 := by
  unfold tailWord_72391
  simp only [CollatzResearch.WordTrace]
  refine ⟨2640316680747245243609027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1760211120498163495739351 2640316680747245243609027)
  ·
    refine ⟨3960475021120867865413541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2640316680747245243609027 3960475021120867865413541)
    ·
      refine ⟨742589066460162724765039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3960475021120867865413541 742589066460162724765039)
      ·
        refine ⟨1113883599690244087147559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 742589066460162724765039 1113883599690244087147559)
        ·
          refine ⟨1670825399535366130721339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1113883599690244087147559 1670825399535366130721339)
          ·
            refine ⟨2506238099303049196082009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1670825399535366130721339 2506238099303049196082009)
            ·
              refine ⟨1879678574477286897061507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2506238099303049196082009 1879678574477286897061507)
              ·
                refine ⟨2819517861715930345592261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1879678574477286897061507 2819517861715930345592261)
                ·
                  refine ⟨528659599071736939798549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2819517861715930345592261 528659599071736939798549)
                  ·
                    refine ⟨24780918706487669053057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 528659599071736939798549 24780918706487669053057)
                    ·
                      rfl

theorem cell22_72391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 1, 4, 6].length) (baseStart_72391 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_72391 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_72391 prefixEnd_72391 := by exact prefixLift 72391
  have htrace : WordTrace (prefixWord ++ tailWord_72391) baseStart_72391 baseEnd_72391 := by
    simpa [prefixWord, tailWord_72391, baseEnd_72391] using wordTrace_append hprefix tailTrace_72391
  have hstable : (prefixWord ++ tailWord_72391).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_72391).length < 2 ^ (prefixWord ++ tailWord_72391).sum := by decide
  have hdescent : baseEnd_72391 < baseStart_72391 := by decide
  rcases family_descends (prefixWord ++ tailWord_72391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_72485 : List Nat := [1, 3, 1, 2, 3, 1, 1, 6, 4]
def baseStart_72485 : Nat := 118140960795 + 72485 * 2 ^ 59
def prefixEnd_72485 : Nat := 4983230072969 + 3 ^ 40 * 72485 * 2
def baseEnd_72485 : Nat := 8271032275834252400923

theorem tailTrace_72485 : CollatzResearch.WordTrace tailWord_72485 prefixEnd_72485 8271032275834252400923 := by
  unfold tailWord_72485
  simp only [CollatzResearch.WordTrace]
  refine ⟨2643745142406699297530909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1762496761604466198353939 2643745142406699297530909)
  ·
    refine ⟨991404428402512236574091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2643745142406699297530909 991404428402512236574091)
    ·
      refine ⟨1487106642603768354861137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 991404428402512236574091 1487106642603768354861137)
      ·
        refine ⟨1115329981952826266145853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1487106642603768354861137 1115329981952826266145853)
        ·
          refine ⟨418248743232309849804695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1115329981952826266145853 418248743232309849804695)
          ·
            refine ⟨627373114848464774707043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 418248743232309849804695 627373114848464774707043)
            ·
              refine ⟨941059672272697162060565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 627373114848464774707043 941059672272697162060565)
              ·
                refine ⟨44112172137782679471589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 941059672272697162060565 44112172137782679471589)
                ·
                  refine ⟨8271032275834252400923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 44112172137782679471589 8271032275834252400923)
                  ·
                    rfl

theorem cell22_72485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 6, 4].length) (baseStart_72485 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_72485 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_72485 prefixEnd_72485 := by exact prefixLift 72485
  have htrace : WordTrace (prefixWord ++ tailWord_72485) baseStart_72485 baseEnd_72485 := by
    simpa [prefixWord, tailWord_72485, baseEnd_72485] using wordTrace_append hprefix tailTrace_72485
  have hstable : (prefixWord ++ tailWord_72485).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_72485).length < 2 ^ (prefixWord ++ tailWord_72485).sum := by decide
  have hdescent : baseEnd_72485 < baseStart_72485 := by decide
  rcases family_descends (prefixWord ++ tailWord_72485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_72498 : List Nat := [3, 2, 1, 1, 3, 1, 1, 1, 3, 6]
def baseStart_72498 : Nat := 118140960795 + 72498 * 2 ^ 59
def prefixEnd_72498 : Nat := 4983230072969 + 3 ^ 40 * 72498 * 2
def baseEnd_72498 : Nat := 24817546993175056627729

theorem tailTrace_72498 : CollatzResearch.WordTrace tailWord_72498 prefixEnd_72498 24817546993175056627729 := by
  unfold tailWord_72498
  simp only [CollatzResearch.WordTrace]
  refine ⟨661054822839900629438537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1762812860906401678502765 661054822839900629438537)
  ·
    refine ⟨495791117129925472078903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 661054822839900629438537 495791117129925472078903)
    ·
      refine ⟨743686675694888208118355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 495791117129925472078903 743686675694888208118355)
      ·
        refine ⟨1115530013542332312177533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 743686675694888208118355 1115530013542332312177533)
        ·
          refine ⟨418323755078374617066575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1115530013542332312177533 418323755078374617066575)
          ·
            refine ⟨627485632617561925599863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 418323755078374617066575 627485632617561925599863)
            ·
              refine ⟨941228448926342888399795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 627485632617561925599863 941228448926342888399795)
              ·
                refine ⟨1411842673389514332599693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 941228448926342888399795 1411842673389514332599693)
                ·
                  refine ⟨529441002521067874724885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1411842673389514332599693 529441002521067874724885)
                  ·
                    refine ⟨24817546993175056627729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 529441002521067874724885 24817546993175056627729)
                    ·
                      rfl

theorem cell22_72498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 1, 3, 6].length) (baseStart_72498 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_72498 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_72498 prefixEnd_72498 := by exact prefixLift 72498
  have htrace : WordTrace (prefixWord ++ tailWord_72498) baseStart_72498 baseEnd_72498 := by
    simpa [prefixWord, tailWord_72498, baseEnd_72498] using wordTrace_append hprefix tailTrace_72498
  have hstable : (prefixWord ++ tailWord_72498).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_72498).length < 2 ^ (prefixWord ++ tailWord_72498).sum := by decide
  have hdescent : baseEnd_72498 < baseStart_72498 := by decide
  rcases family_descends (prefixWord ++ tailWord_72498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_72532 : List Nat := [2, 4, 1, 1, 4, 1, 1, 2, 2, 4]
def baseStart_72532 : Nat := 118140960795 + 72532 * 2 ^ 59
def prefixEnd_72532 : Nat := 4983230072969 + 3 ^ 40 * 72532 * 2
def baseEnd_72532 : Nat := 24829185888010301277625

theorem tailTrace_72532 : CollatzResearch.WordTrace tailWord_72532 prefixEnd_72532 24829185888010301277625 := by
  unfold tailWord_72532
  simp only [CollatzResearch.WordTrace]
  refine ⟨1322729686618213162245925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1763639582157617549661233 1322729686618213162245925)
  ·
    refine ⟨248011816240914967921111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1322729686618213162245925 248011816240914967921111)
    ·
      refine ⟨372017724361372451881667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 248011816240914967921111 372017724361372451881667)
      ·
        refine ⟨558026586542058677822501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 372017724361372451881667 558026586542058677822501)
        ·
          refine ⟨104629984976636002091719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 558026586542058677822501 104629984976636002091719)
          ·
            refine ⟨156944977464954003137579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104629984976636002091719 156944977464954003137579)
            ·
              refine ⟨235417466197431004706369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 156944977464954003137579 235417466197431004706369)
              ·
                refine ⟨176563099648073253529777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 235417466197431004706369 176563099648073253529777)
                ·
                  refine ⟨132422324736054940147333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 176563099648073253529777 132422324736054940147333)
                  ·
                    refine ⟨24829185888010301277625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 132422324736054940147333 24829185888010301277625)
                    ·
                      rfl

theorem cell22_72532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 1, 2, 2, 4].length) (baseStart_72532 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_72532 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_72532 prefixEnd_72532 := by exact prefixLift 72532
  have htrace : WordTrace (prefixWord ++ tailWord_72532) baseStart_72532 baseEnd_72532 := by
    simpa [prefixWord, tailWord_72532, baseEnd_72532] using wordTrace_append hprefix tailTrace_72532
  have hstable : (prefixWord ++ tailWord_72532).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_72532).length < 2 ^ (prefixWord ++ tailWord_72532).sum := by decide
  have hdescent : baseEnd_72532 < baseStart_72532 := by decide
  rcases family_descends (prefixWord ++ tailWord_72532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_72543 : List Nat := [1, 1, 2, 3, 1, 3, 2, 1, 2, 6]
def baseStart_72543 : Nat := 118140960795 + 72543 * 2 ^ 59
def prefixEnd_72543 : Nat := 4983230072969 + 3 ^ 40 * 72543 * 2
def baseEnd_72543 : Nat := 24832951412809939252591

theorem tailTrace_72543 : CollatzResearch.WordTrace tailWord_72543 prefixEnd_72543 24832951412809939252591 := by
  unfold tailWord_72543
  simp only [CollatzResearch.WordTrace]
  refine ⟨2645860576196575203142283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1763907050797716802094855 2645860576196575203142283)
  ·
    refine ⟨3968790864294862804713425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2645860576196575203142283 3968790864294862804713425)
    ·
      refine ⟨2976593148221147103535069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3968790864294862804713425 2976593148221147103535069)
      ·
        refine ⟨1116222430582930163825651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2976593148221147103535069 1116222430582930163825651)
        ·
          refine ⟨1674333645874395245738477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1116222430582930163825651 1674333645874395245738477)
          ·
            refine ⟨627875117202898217151929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1674333645874395245738477 627875117202898217151929)
            ·
              refine ⟨470906337902173662863947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 627875117202898217151929 470906337902173662863947)
              ·
                refine ⟨706359506853260494295921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 470906337902173662863947 706359506853260494295921)
                ·
                  refine ⟨529769630139945370721941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 706359506853260494295921 529769630139945370721941)
                  ·
                    refine ⟨24832951412809939252591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 529769630139945370721941 24832951412809939252591)
                    ·
                      rfl

theorem cell22_72543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 1, 2, 6].length) (baseStart_72543 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_72543 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_72543 prefixEnd_72543 := by exact prefixLift 72543
  have htrace : WordTrace (prefixWord ++ tailWord_72543) baseStart_72543 baseEnd_72543 := by
    simpa [prefixWord, tailWord_72543, baseEnd_72543] using wordTrace_append hprefix tailTrace_72543
  have hstable : (prefixWord ++ tailWord_72543).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_72543).length < 2 ^ (prefixWord ++ tailWord_72543).sum := by decide
  have hdescent : baseEnd_72543 < baseStart_72543 := by decide
  rcases family_descends (prefixWord ++ tailWord_72543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_72545 : List Nat := [1, 2, 3, 1, 1, 1, 2, 5, 3, 3]
def baseStart_72545 : Nat := 118140960795 + 72545 * 2 ^ 59
def prefixEnd_72545 : Nat := 4983230072969 + 3 ^ 40 * 72545 * 2
def baseEnd_72545 : Nat := 24833636053682600702585

theorem tailTrace_72545 : CollatzResearch.WordTrace tailWord_72545 prefixEnd_72545 24833636053682600702585 := by
  unfold tailWord_72545
  simp only [CollatzResearch.WordTrace]
  refine ⟨2645933522189329544715089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1763955681459553029810059 2645933522189329544715089)
  ·
    refine ⟨1984450141641997158536317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2645933522189329544715089 1984450141641997158536317)
    ·
      refine ⟨744168803115748934451119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1984450141641997158536317 744168803115748934451119)
      ·
        refine ⟨1116253204673623401676679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 744168803115748934451119 1116253204673623401676679)
        ·
          refine ⟨1674379807010435102515019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1116253204673623401676679 1674379807010435102515019)
          ·
            refine ⟨2511569710515652653772529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1674379807010435102515019 2511569710515652653772529)
            ·
              refine ⟨1883677282886739490329397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2511569710515652653772529 1883677282886739490329397)
              ·
                refine ⟨176594745270631827218381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1883677282886739490329397 176594745270631827218381)
                ·
                  refine ⟨66223029476486935206893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 176594745270631827218381 66223029476486935206893)
                  ·
                    refine ⟨24833636053682600702585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 66223029476486935206893 24833636053682600702585)
                    ·
                      rfl

theorem cell22_72545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 5, 3, 3].length) (baseStart_72545 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_72545 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_72545 prefixEnd_72545 := by exact prefixLift 72545
  have htrace : WordTrace (prefixWord ++ tailWord_72545) baseStart_72545 baseEnd_72545 := by
    simpa [prefixWord, tailWord_72545, baseEnd_72545] using wordTrace_append hprefix tailTrace_72545
  have hstable : (prefixWord ++ tailWord_72545).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_72545).length < 2 ^ (prefixWord ++ tailWord_72545).sum := by decide
  have hdescent : baseEnd_72545 < baseStart_72545 := by decide
  rcases family_descends (prefixWord ++ tailWord_72545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_72605 : List Nat := [1, 4, 2, 1, 2, 1, 1, 1, 5, 4]
def baseStart_72605 : Nat := 118140960795 + 72605 * 2 ^ 59
def prefixEnd_72605 : Nat := 4983230072969 + 3 ^ 40 * 72605 * 2
def baseEnd_72605 : Nat := 24854175279862444202401

theorem tailTrace_72605 : CollatzResearch.WordTrace tailWord_72605 prefixEnd_72605 24854175279862444202401 := by
  unfold tailWord_72605
  simp only [CollatzResearch.WordTrace]
  refine ⟨2648121901971959791899269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1765414601314639861266179 2648121901971959791899269)
  ·
    refine ⟨496522856619742460981113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2648121901971959791899269 496522856619742460981113)
    ·
      refine ⟨372392142464806845735835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 496522856619742460981113 372392142464806845735835)
      ·
        refine ⟨558588213697210268603753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 372392142464806845735835 558588213697210268603753)
        ·
          refine ⟨418941160272907701452815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 558588213697210268603753 418941160272907701452815)
          ·
            refine ⟨628411740409361552179223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 418941160272907701452815 628411740409361552179223)
            ·
              refine ⟨942617610614042328268835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 628411740409361552179223 942617610614042328268835)
              ·
                refine ⟨1413926415921063492403253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 942617610614042328268835 1413926415921063492403253)
                ·
                  refine ⟨132555601492599702412805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1413926415921063492403253 132555601492599702412805)
                  ·
                    refine ⟨24854175279862444202401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 132555601492599702412805 24854175279862444202401)
                    ·
                      rfl

theorem cell22_72605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 1, 5, 4].length) (baseStart_72605 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_72605 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_72605 prefixEnd_72605 := by exact prefixLift 72605
  have htrace : WordTrace (prefixWord ++ tailWord_72605) baseStart_72605 baseEnd_72605 := by
    simpa [prefixWord, tailWord_72605, baseEnd_72605] using wordTrace_append hprefix tailTrace_72605
  have hstable : (prefixWord ++ tailWord_72605).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_72605).length < 2 ^ (prefixWord ++ tailWord_72605).sum := by decide
  have hdescent : baseEnd_72605 < baseStart_72605 := by decide
  rcases family_descends (prefixWord ++ tailWord_72605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_72650 : List Nat := [3, 1, 2, 1, 2, 1, 1, 3, 4, 4]
def baseStart_72650 : Nat := 118140960795 + 72650 * 2 ^ 59
def prefixEnd_72650 : Nat := 4983230072969 + 3 ^ 40 * 72650 * 2
def baseEnd_72650 : Nat := 24869579699497326827263

theorem tailTrace_72650 : CollatzResearch.WordTrace tailWord_72650 prefixEnd_72650 24869579699497326827263 := by
  unfold tailWord_72650
  simp only [CollatzResearch.WordTrace]
  refine ⟨662440796702233119321851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1766508791205954984858269 662440796702233119321851)
  ·
    refine ⟨993661195053349678982777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 662440796702233119321851 993661195053349678982777)
    ·
      refine ⟨745245896290012259237083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 993661195053349678982777 745245896290012259237083)
      ·
        refine ⟨1117868844435018388855625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 745245896290012259237083 1117868844435018388855625)
        ·
          refine ⟨838401633326263791641719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1117868844435018388855625 838401633326263791641719)
          ·
            refine ⟨1257602449989395687462579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 838401633326263791641719 1257602449989395687462579)
            ·
              refine ⟨1886403674984093531193869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1257602449989395687462579 1886403674984093531193869)
              ·
                refine ⟨707401378119035074197701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1886403674984093531193869 707401378119035074197701)
                ·
                  refine ⟨132637758397319076412069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 707401378119035074197701 132637758397319076412069)
                  ·
                    refine ⟨24869579699497326827263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 132637758397319076412069 24869579699497326827263)
                    ·
                      rfl

theorem cell22_72650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 3, 4, 4].length) (baseStart_72650 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_72650 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_72650 prefixEnd_72650 := by exact prefixLift 72650
  have htrace : WordTrace (prefixWord ++ tailWord_72650) baseStart_72650 baseEnd_72650 := by
    simpa [prefixWord, tailWord_72650, baseEnd_72650] using wordTrace_append hprefix tailTrace_72650
  have hstable : (prefixWord ++ tailWord_72650).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_72650).length < 2 ^ (prefixWord ++ tailWord_72650).sum := by decide
  have hdescent : baseEnd_72650 < baseStart_72650 := by decide
  rcases family_descends (prefixWord ++ tailWord_72650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_72652 : List Nat := [2, 2, 1, 4, 1, 1, 3, 1, 4, 3]
def baseStart_72652 : Nat := 118140960795 + 72652 * 2 ^ 59
def prefixEnd_72652 : Nat := 4983230072969 + 3 ^ 40 * 72652 * 2
def baseEnd_72652 : Nat := 24870264340369988277257

theorem tailTrace_72652 : CollatzResearch.WordTrace tailWord_72652 prefixEnd_72652 24870264340369988277257 := by
  unfold tailWord_72652
  simp only [CollatzResearch.WordTrace]
  refine ⟨1324918066400843409430105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1766557421867791212573473 1324918066400843409430105)
  ·
    refine ⟨993688549800632557072579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1324918066400843409430105 993688549800632557072579)
    ·
      refine ⟨1490532824700948835608869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 993688549800632557072579 1490532824700948835608869)
      ·
        refine ⟨279474904631427906676663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1490532824700948835608869 279474904631427906676663)
        ·
          refine ⟨419212356947141860014995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 279474904631427906676663 419212356947141860014995)
          ·
            refine ⟨628818535420712790022493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 419212356947141860014995 628818535420712790022493)
            ·
              refine ⟨235806950782767296258435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 628818535420712790022493 235806950782767296258435)
              ·
                refine ⟨353710426174150944387653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 235806950782767296258435 353710426174150944387653)
                ·
                  refine ⟨66320704907653302072685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 353710426174150944387653 66320704907653302072685)
                  ·
                    refine ⟨24870264340369988277257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 66320704907653302072685 24870264340369988277257)
                    ·
                      rfl

theorem cell22_72652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 3, 1, 4, 3].length) (baseStart_72652 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_72652 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_72652 prefixEnd_72652 := by exact prefixLift 72652
  have htrace : WordTrace (prefixWord ++ tailWord_72652) baseStart_72652 baseEnd_72652 := by
    simpa [prefixWord, tailWord_72652, baseEnd_72652] using wordTrace_append hprefix tailTrace_72652
  have hstable : (prefixWord ++ tailWord_72652).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_72652).length < 2 ^ (prefixWord ++ tailWord_72652).sum := by decide
  have hdescent : baseEnd_72652 < baseStart_72652 := by decide
  rcases family_descends (prefixWord ++ tailWord_72652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_72669 : List Nat := [1, 4, 3, 1, 2, 3, 1, 1, 1, 5]
def baseStart_72669 : Nat := 118140960795 + 72669 * 2 ^ 59
def prefixEnd_72669 : Nat := 4983230072969 + 3 ^ 40 * 72669 * 2
def baseEnd_72669 : Nat := 24876083787787610602205

theorem tailTrace_72669 : CollatzResearch.WordTrace tailWord_72669 prefixEnd_72669 24876083787787610602205 := by
  unfold tailWord_72669
  simp only [CollatzResearch.WordTrace]
  refine ⟨2650456173740098722229061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1766970782493399148152707 2650456173740098722229061)
  ·
    refine ⟨496960532576268510417949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2650456173740098722229061 496960532576268510417949)
    ·
      refine ⟨186360199716100691406731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 496960532576268510417949 186360199716100691406731)
      ·
        refine ⟨279540299574151037110097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 186360199716100691406731 279540299574151037110097)
        ·
          refine ⟨209655224680613277832573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 279540299574151037110097 209655224680613277832573)
          ·
            refine ⟨78620709255229979187215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 209655224680613277832573 78620709255229979187215)
            ·
              refine ⟨117931063882844968780823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78620709255229979187215 117931063882844968780823)
              ·
                refine ⟨176896595824267453171235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 117931063882844968780823 176896595824267453171235)
                ·
                  refine ⟨265344893736401179756853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 176896595824267453171235 265344893736401179756853)
                  ·
                    refine ⟨24876083787787610602205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 265344893736401179756853 24876083787787610602205)
                    ·
                      rfl

theorem cell22_72669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 3, 1, 1, 1, 5].length) (baseStart_72669 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_72669 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_72669 prefixEnd_72669 := by exact prefixLift 72669
  have htrace : WordTrace (prefixWord ++ tailWord_72669) baseStart_72669 baseEnd_72669 := by
    simpa [prefixWord, tailWord_72669, baseEnd_72669] using wordTrace_append hprefix tailTrace_72669
  have hstable : (prefixWord ++ tailWord_72669).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_72669).length < 2 ^ (prefixWord ++ tailWord_72669).sum := by decide
  have hdescent : baseEnd_72669 < baseStart_72669 := by decide
  rcases family_descends (prefixWord ++ tailWord_72669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_72682 : List Nat := [3, 1, 3, 1, 2, 2, 4, 6]
def baseStart_72682 : Nat := 118140960795 + 72682 * 2 ^ 59
def prefixEnd_72682 : Nat := 4983230072969 + 3 ^ 40 * 72682 * 2
def baseEnd_72682 : Nat := 2764503772606656669685

theorem tailTrace_72682 : CollatzResearch.WordTrace tailWord_72682 prefixEnd_72682 2764503772606656669685 := by
  unfold tailWord_72682
  simp only [CollatzResearch.WordTrace]
  refine ⟨662732580673250485613075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1767286881795334628301533 662732580673250485613075)
  ·
    refine ⟨994098871009875728419613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 662732580673250485613075 994098871009875728419613)
    ·
      refine ⟨372787076628703398157355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 994098871009875728419613 372787076628703398157355)
      ·
        refine ⟨559180614943055097236033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 372787076628703398157355 559180614943055097236033)
        ·
          refine ⟨419385461207291322927025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 559180614943055097236033 419385461207291322927025)
          ·
            refine ⟨314539095905468492195269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 419385461207291322927025 314539095905468492195269)
            ·
              refine ⟨58976080482275342286613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 314539095905468492195269 58976080482275342286613)
              ·
                refine ⟨2764503772606656669685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 58976080482275342286613 2764503772606656669685)
                ·
                  rfl

theorem cell22_72682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 4, 6].length) (baseStart_72682 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_72682 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_72682 prefixEnd_72682 := by exact prefixLift 72682
  have htrace : WordTrace (prefixWord ++ tailWord_72682) baseStart_72682 baseEnd_72682 := by
    simpa [prefixWord, tailWord_72682, baseEnd_72682] using wordTrace_append hprefix tailTrace_72682
  have hstable : (prefixWord ++ tailWord_72682).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_72682).length < 2 ^ (prefixWord ++ tailWord_72682).sum := by decide
  have hdescent : baseEnd_72682 < baseStart_72682 := by decide
  rcases family_descends (prefixWord ++ tailWord_72682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_72714 : List Nat := [3, 1, 2, 2, 3, 1, 3, 1, 3, 3]
def baseStart_72714 : Nat := 118140960795 + 72714 * 2 ^ 59
def prefixEnd_72714 : Nat := 4983230072969 + 3 ^ 40 * 72714 * 2
def baseEnd_72714 : Nat := 24891488207422493227067

theorem tailTrace_72714 : CollatzResearch.WordTrace tailWord_72714 prefixEnd_72714 24891488207422493227067 := by
  unfold tailWord_72714
  simp only [CollatzResearch.WordTrace]
  refine ⟨663024364644267851904299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1768064972384714271744797 663024364644267851904299)
  ·
    refine ⟨994536546966401777856449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 663024364644267851904299 994536546966401777856449)
    ·
      refine ⟨745902410224801333392337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 994536546966401777856449 745902410224801333392337)
      ·
        refine ⟨559426807668601000044253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 745902410224801333392337 559426807668601000044253)
        ·
          refine ⟨209785052875725375016595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 559426807668601000044253 209785052875725375016595)
          ·
            refine ⟨314677579313588062524893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 209785052875725375016595 314677579313588062524893)
            ·
              refine ⟨118004092242595523446835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 314677579313588062524893 118004092242595523446835)
              ·
                refine ⟨177006138363893285170253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 118004092242595523446835 177006138363893285170253)
                ·
                  refine ⟨66377301886459981938845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 177006138363893285170253 66377301886459981938845)
                  ·
                    refine ⟨24891488207422493227067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 66377301886459981938845 24891488207422493227067)
                    ·
                      rfl

theorem cell22_72714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 3, 1, 3, 3].length) (baseStart_72714 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_72714 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_72714 prefixEnd_72714 := by exact prefixLift 72714
  have htrace : WordTrace (prefixWord ++ tailWord_72714) baseStart_72714 baseEnd_72714 := by
    simpa [prefixWord, tailWord_72714, baseEnd_72714] using wordTrace_append hprefix tailTrace_72714
  have hstable : (prefixWord ++ tailWord_72714).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_72714).length < 2 ^ (prefixWord ++ tailWord_72714).sum := by decide
  have hdescent : baseEnd_72714 < baseStart_72714 := by decide
  rcases family_descends (prefixWord ++ tailWord_72714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_72956 : List Nat := [2, 2, 2, 1, 5, 1, 2, 1, 1, 5]
def baseStart_72956 : Nat := 118140960795 + 72956 * 2 ^ 59
def prefixEnd_72956 : Nat := 4983230072969 + 3 ^ 40 * 72956 * 2
def baseEnd_72956 : Nat := 24974329753014528676325

theorem tailTrace_72956 : CollatzResearch.WordTrace tailWord_72956 prefixEnd_72956 24974329753014528676325 := by
  unfold tailWord_72956
  simp only [CollatzResearch.WordTrace]
  refine ⟨1330461961850173368963361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1773949282466897825284481 1330461961850173368963361)
  ·
    refine ⟨997846471387630026722521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1330461961850173368963361 997846471387630026722521)
    ·
      refine ⟨748384853540722520041891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 997846471387630026722521 748384853540722520041891)
      ·
        refine ⟨1122577280311083780062837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 748384853540722520041891 1122577280311083780062837)
        ·
          refine ⟨105241620029164104380891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1122577280311083780062837 105241620029164104380891)
          ·
            refine ⟨157862430043746156571337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105241620029164104380891 157862430043746156571337)
            ·
              refine ⟨118396822532809617428503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 157862430043746156571337 118396822532809617428503)
              ·
                refine ⟨177595233799214426142755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 118396822532809617428503 177595233799214426142755)
                ·
                  refine ⟨266392850698821639214133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 177595233799214426142755 266392850698821639214133)
                  ·
                    refine ⟨24974329753014528676325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 266392850698821639214133 24974329753014528676325)
                    ·
                      rfl

theorem cell22_72956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 2, 1, 1, 5].length) (baseStart_72956 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_72956 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_72956 prefixEnd_72956 := by exact prefixLift 72956
  have htrace : WordTrace (prefixWord ++ tailWord_72956) baseStart_72956 baseEnd_72956 := by
    simpa [prefixWord, tailWord_72956, baseEnd_72956] using wordTrace_append hprefix tailTrace_72956
  have hstable : (prefixWord ++ tailWord_72956).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_72956).length < 2 ^ (prefixWord ++ tailWord_72956).sum := by decide
  have hdescent : baseEnd_72956 < baseStart_72956 := by decide
  rcases family_descends (prefixWord ++ tailWord_72956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_72969 : List Nat := [1, 2, 1, 1, 3, 3, 5, 6]
def baseStart_72969 : Nat := 118140960795 + 72969 * 2 ^ 59
def prefixEnd_72969 : Nat := 4983230072969 + 3 ^ 40 * 72969 * 2
def baseEnd_72969 : Nat := 2775419990965203122365

theorem tailTrace_72969 : CollatzResearch.WordTrace tailWord_72969 prefixEnd_72969 2775419990965203122365 := by
  unfold tailWord_72969
  simp only [CollatzResearch.WordTrace]
  refine ⟨2661398072653249958149961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1774265381768833305433307 2661398072653249958149961)
  ·
    refine ⟨1996048554489937468612471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2661398072653249958149961 1996048554489937468612471)
    ·
      refine ⟨2994072831734906202918707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1996048554489937468612471 2994072831734906202918707)
      ·
        refine ⟨4491109247602359304378061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2994072831734906202918707 4491109247602359304378061)
        ·
          refine ⟨1684165967850884739141773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4491109247602359304378061 1684165967850884739141773)
          ·
            refine ⟨631562237944081777178165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1684165967850884739141773 631562237944081777178165)
            ·
              refine ⟨59208959807257666610453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 631562237944081777178165 59208959807257666610453)
              ·
                refine ⟨2775419990965203122365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 59208959807257666610453 2775419990965203122365)
                ·
                  rfl

theorem cell22_72969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 5, 6].length) (baseStart_72969 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_72969 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_72969 prefixEnd_72969 := by exact prefixLift 72969
  have htrace : WordTrace (prefixWord ++ tailWord_72969) baseStart_72969 baseEnd_72969 := by
    simpa [prefixWord, tailWord_72969, baseEnd_72969] using wordTrace_append hprefix tailTrace_72969
  have hstable : (prefixWord ++ tailWord_72969).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_72969).length < 2 ^ (prefixWord ++ tailWord_72969).sum := by decide
  have hdescent : baseEnd_72969 < baseStart_72969 := by decide
  rcases family_descends (prefixWord ++ tailWord_72969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_72971 : List Nat := [1, 1, 1, 1, 5, 5, 1, 1, 2, 4]
def baseStart_72971 : Nat := 118140960795 + 72971 * 2 ^ 59
def prefixEnd_72971 : Nat := 4983230072969 + 3 ^ 40 * 72971 * 2
def baseEnd_72971 : Nat := 24979464559559489551279

theorem tailTrace_72971 : CollatzResearch.WordTrace tailWord_72971 prefixEnd_72971 24979464559559489551279 := by
  unfold tailWord_72971
  simp only [CollatzResearch.WordTrace]
  refine ⟨2661471018646004299722767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1774314012430669533148511 2661471018646004299722767)
  ·
    refine ⟨3992206527969006449584151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2661471018646004299722767 3992206527969006449584151)
    ·
      refine ⟨5988309791953509674376227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3992206527969006449584151 5988309791953509674376227)
      ·
        refine ⟨8982464687930264511564341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5988309791953509674376227 8982464687930264511564341)
        ·
          refine ⟨842106064493462297959157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8982464687930264511564341 842106064493462297959157)
          ·
            refine ⟨78947443546262090433671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 842106064493462297959157 78947443546262090433671)
            ·
              refine ⟨118421165319393135650507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78947443546262090433671 118421165319393135650507)
              ·
                refine ⟨177631747979089703475761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 118421165319393135650507 177631747979089703475761)
                ·
                  refine ⟨133223810984317277606821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 177631747979089703475761 133223810984317277606821)
                  ·
                    refine ⟨24979464559559489551279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 133223810984317277606821 24979464559559489551279)
                    ·
                      rfl

theorem cell22_72971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 5, 1, 1, 2, 4].length) (baseStart_72971 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_72971 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_72971 prefixEnd_72971 := by exact prefixLift 72971
  have htrace : WordTrace (prefixWord ++ tailWord_72971) baseStart_72971 baseEnd_72971 := by
    simpa [prefixWord, tailWord_72971, baseEnd_72971] using wordTrace_append hprefix tailTrace_72971
  have hstable : (prefixWord ++ tailWord_72971).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_72971).length < 2 ^ (prefixWord ++ tailWord_72971).sum := by decide
  have hdescent : baseEnd_72971 < baseStart_72971 := by decide
  rcases family_descends (prefixWord ++ tailWord_72971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_72990 : List Nat := [4, 3, 2, 1, 2, 1, 1, 1, 4, 3]
def baseStart_72990 : Nat := 118140960795 + 72990 * 2 ^ 59
def prefixEnd_72990 : Nat := 4983230072969 + 3 ^ 40 * 72990 * 2
def baseEnd_72990 : Nat := 24985968647849773326221

theorem tailTrace_72990 : CollatzResearch.WordTrace tailWord_72990 prefixEnd_72990 24985968647849773326221 := by
  unfold tailWord_72990
  simp only [CollatzResearch.WordTrace]
  refine ⟨332770500697146318083053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1774776003718113696442949 332770500697146318083053)
  ·
    refine ⟨124788937761429869281145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 332770500697146318083053 124788937761429869281145)
    ·
      refine ⟨93591703321072401960859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124788937761429869281145 93591703321072401960859)
      ·
        refine ⟨140387554981608602941289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93591703321072401960859 140387554981608602941289)
        ·
          refine ⟨105290666236206452205967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 140387554981608602941289 105290666236206452205967)
          ·
            refine ⟨157935999354309678308951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105290666236206452205967 157935999354309678308951)
            ·
              refine ⟨236903999031464517463427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 157935999354309678308951 236903999031464517463427)
              ·
                refine ⟨355355998547196776195141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 236903999031464517463427 355355998547196776195141)
                ·
                  refine ⟨66629249727599395536589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 355355998547196776195141 66629249727599395536589)
                  ·
                    refine ⟨24985968647849773326221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 66629249727599395536589 24985968647849773326221)
                    ·
                      rfl

theorem cell22_72990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 1, 1, 4, 3].length) (baseStart_72990 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_72990 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_72990 prefixEnd_72990 := by exact prefixLift 72990
  have htrace : WordTrace (prefixWord ++ tailWord_72990) baseStart_72990 baseEnd_72990 := by
    simpa [prefixWord, tailWord_72990, baseEnd_72990] using wordTrace_append hprefix tailTrace_72990
  have hstable : (prefixWord ++ tailWord_72990).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_72990).length < 2 ^ (prefixWord ++ tailWord_72990).sum := by decide
  have hdescent : baseEnd_72990 < baseStart_72990 := by decide
  rcases family_descends (prefixWord ++ tailWord_72990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_73091 : List Nat := [1, 1, 1, 3, 5, 2, 1, 2, 1, 5]
def baseStart_73091 : Nat := 118140960795 + 73091 * 2 ^ 59
def prefixEnd_73091 : Nat := 4983230072969 + 3 ^ 40 * 73091 * 2
def baseEnd_73091 : Nat := 25020543011919176550911

theorem tailTrace_73091 : CollatzResearch.WordTrace tailWord_73091 prefixEnd_73091 25020543011919176550911 := by
  unfold tailWord_73091
  simp only [CollatzResearch.WordTrace]
  refine ⟨2665847778211264794091127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1777231852140843196060751 2665847778211264794091127)
  ·
    refine ⟨3998771667316897191136691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2665847778211264794091127 3998771667316897191136691)
    ·
      refine ⟨5998157500975345786705037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3998771667316897191136691 5998157500975345786705037)
      ·
        refine ⟨2249309062865754670014389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5998157500975345786705037 2249309062865754670014389)
        ·
          refine ⟨210872724643664500313849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2249309062865754670014389 210872724643664500313849)
          ·
            refine ⟨158154543482748375235387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 210872724643664500313849 158154543482748375235387)
            ·
              refine ⟨237231815224122562853081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 158154543482748375235387 237231815224122562853081)
              ·
                refine ⟨177923861418091922139811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 237231815224122562853081 177923861418091922139811)
                ·
                  refine ⟨266885792127137883209717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 177923861418091922139811 266885792127137883209717)
                  ·
                    refine ⟨25020543011919176550911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 266885792127137883209717 25020543011919176550911)
                    ·
                      rfl

theorem cell22_73091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 1, 2, 1, 5].length) (baseStart_73091 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_73091 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_73091 prefixEnd_73091 := by exact prefixLift 73091
  have htrace : WordTrace (prefixWord ++ tailWord_73091) baseStart_73091 baseEnd_73091 := by
    simpa [prefixWord, tailWord_73091, baseEnd_73091] using wordTrace_append hprefix tailTrace_73091
  have hstable : (prefixWord ++ tailWord_73091).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_73091).length < 2 ^ (prefixWord ++ tailWord_73091).sum := by decide
  have hdescent : baseEnd_73091 < baseStart_73091 := by decide
  rcases family_descends (prefixWord ++ tailWord_73091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_73183 : List Nat := [1, 1, 2, 3, 3, 1, 5, 1, 5]
def baseStart_73183 : Nat := 118140960795 + 73183 * 2 ^ 59
def prefixEnd_73183 : Nat := 4983230072969 + 3 ^ 40 * 73183 * 2
def baseEnd_73183 : Nat := 8350678830687201083543

theorem tailTrace_73183 : CollatzResearch.WordTrace tailWord_73183 prefixEnd_73183 8350678830687201083543 := by
  unfold tailWord_73183
  simp only [CollatzResearch.WordTrace]
  refine ⟨2669203293877964506440203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1779468862585309670960135 2669203293877964506440203)
  ·
    refine ⟨4003804940816946759660305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2669203293877964506440203 4003804940816946759660305)
    ·
      refine ⟨3002853705612710069745229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4003804940816946759660305 3002853705612710069745229)
      ·
        refine ⟨1126070139604766276154461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3002853705612710069745229 1126070139604766276154461)
        ·
          refine ⟨422276302351787353557923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1126070139604766276154461 422276302351787353557923)
          ·
            refine ⟨633414453527681030336885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 422276302351787353557923 633414453527681030336885)
            ·
              refine ⟨59382605018220096594083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 633414453527681030336885 59382605018220096594083)
              ·
                refine ⟨89073907527330144891125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59382605018220096594083 89073907527330144891125)
                ·
                  refine ⟨8350678830687201083543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 89073907527330144891125 8350678830687201083543)
                  ·
                    rfl

theorem cell22_73183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 5, 1, 5].length) (baseStart_73183 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_73183 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_73183 prefixEnd_73183 := by exact prefixLift 73183
  have htrace : WordTrace (prefixWord ++ tailWord_73183) baseStart_73183 baseEnd_73183 := by
    simpa [prefixWord, tailWord_73183, baseEnd_73183] using wordTrace_append hprefix tailTrace_73183
  have hstable : (prefixWord ++ tailWord_73183).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_73183).length < 2 ^ (prefixWord ++ tailWord_73183).sum := by decide
  have hdescent : baseEnd_73183 < baseStart_73183 := by decide
  rcases family_descends (prefixWord ++ tailWord_73183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_73213 : List Nat := [1, 4, 1, 1, 1, 4, 2, 3, 1, 4]
def baseStart_73213 : Nat := 118140960795 + 73213 * 2 ^ 59
def prefixEnd_73213 : Nat := 4983230072969 + 3 ^ 40 * 73213 * 2
def baseEnd_73213 : Nat := 25062306105151525000537

theorem tailTrace_73213 : CollatzResearch.WordTrace tailWord_73213 prefixEnd_73213 25062306105151525000537 := by
  unfold tailWord_73213
  simp only [CollatzResearch.WordTrace]
  refine ⟨2670297483769279630032293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1780198322512853086688195 2670297483769279630032293)
  ·
    refine ⟨500680778206739930631055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2670297483769279630032293 500680778206739930631055)
    ·
      refine ⟨751021167310109895946583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 500680778206739930631055 751021167310109895946583)
      ·
        refine ⟨1126531750965164843919875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 751021167310109895946583 1126531750965164843919875)
        ·
          refine ⟨1689797626447747265879813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1126531750965164843919875 1689797626447747265879813)
          ·
            refine ⟨316837054958952612352465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1689797626447747265879813 316837054958952612352465)
            ·
              refine ⟨237627791219214459264349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 316837054958952612352465 237627791219214459264349)
              ·
                refine ⟨89110421707205422224131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 237627791219214459264349 89110421707205422224131)
                ·
                  refine ⟨133665632560808133336197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 89110421707205422224131 133665632560808133336197)
                  ·
                    refine ⟨25062306105151525000537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 133665632560808133336197 25062306105151525000537)
                    ·
                      rfl

theorem cell22_73213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 2, 3, 1, 4].length) (baseStart_73213 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_73213 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_73213 prefixEnd_73213 := by exact prefixLift 73213
  have htrace : WordTrace (prefixWord ++ tailWord_73213) baseStart_73213 baseEnd_73213 := by
    simpa [prefixWord, tailWord_73213, baseEnd_73213] using wordTrace_append hprefix tailTrace_73213
  have hstable : (prefixWord ++ tailWord_73213).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_73213).length < 2 ^ (prefixWord ++ tailWord_73213).sum := by decide
  have hdescent : baseEnd_73213 < baseStart_73213 := by decide
  rcases family_descends (prefixWord ++ tailWord_73213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_73277 : List Nat := [1, 4, 1, 3, 3, 1, 2, 2, 2, 3]
def baseStart_73277 : Nat := 118140960795 + 73277 * 2 ^ 59
def prefixEnd_73277 : Nat := 4983230072969 + 3 ^ 40 * 73277 * 2
def baseEnd_73277 : Nat := 25084214613076691400341

theorem tailTrace_73277 : CollatzResearch.WordTrace tailWord_73277 prefixEnd_73277 25084214613076691400341 := by
  unfold tailWord_73277
  simp only [CollatzResearch.WordTrace]
  refine ⟨2672631755537418560362085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1781754503691612373574723 2672631755537418560362085)
  ·
    refine ⟨501118454163265980067891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2672631755537418560362085 501118454163265980067891)
    ·
      refine ⟨751677681244898970101837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 501118454163265980067891 751677681244898970101837)
      ·
        refine ⟨281879130466837113788189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 751677681244898970101837 281879130466837113788189)
        ·
          refine ⟨105704673925063917670571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 281879130466837113788189 105704673925063917670571)
          ·
            refine ⟨158557010887595876505857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105704673925063917670571 158557010887595876505857)
            ·
              refine ⟨118917758165696907379393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 158557010887595876505857 118917758165696907379393)
              ·
                refine ⟨89188318624272680534545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 118917758165696907379393 89188318624272680534545)
                ·
                  refine ⟨66891238968204510400909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 89188318624272680534545 66891238968204510400909)
                  ·
                    refine ⟨25084214613076691400341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 66891238968204510400909 25084214613076691400341)
                    ·
                      rfl

theorem cell22_73277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 2, 2, 2, 3].length) (baseStart_73277 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_73277 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_73277 prefixEnd_73277 := by exact prefixLift 73277
  have htrace : WordTrace (prefixWord ++ tailWord_73277) baseStart_73277 baseEnd_73277 := by
    simpa [prefixWord, tailWord_73277, baseEnd_73277] using wordTrace_append hprefix tailTrace_73277
  have hstable : (prefixWord ++ tailWord_73277).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_73277).length < 2 ^ (prefixWord ++ tailWord_73277).sum := by decide
  have hdescent : baseEnd_73277 < baseStart_73277 := by decide
  rcases family_descends (prefixWord ++ tailWord_73277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_73301 : List Nat := [1, 3, 2, 2, 1, 1, 1, 2, 9]
def baseStart_73301 : Nat := 118140960795 + 73301 * 2 ^ 59
def prefixEnd_73301 : Nat := 4983230072969 + 3 ^ 40 * 73301 * 2
def baseEnd_73301 : Nat := 8364143434516209600089

theorem tailTrace_73301 : CollatzResearch.WordTrace tailWord_73301 prefixEnd_73301 8364143434516209600089 := by
  unfold tailWord_73301
  simp only [CollatzResearch.WordTrace]
  refine ⟨2673507107450470659235757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1782338071633647106157171 2673507107450470659235757)
  ·
    refine ⟨1002565165293926497213409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2673507107450470659235757 1002565165293926497213409)
    ·
      refine ⟨751923873970444872910057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1002565165293926497213409 751923873970444872910057)
      ·
        refine ⟨563942905477833654682543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 751923873970444872910057 563942905477833654682543)
        ·
          refine ⟨845914358216750482023815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 563942905477833654682543 845914358216750482023815)
          ·
            refine ⟨1268871537325125723035723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 845914358216750482023815 1268871537325125723035723)
            ·
              refine ⟨1903307305987688584553585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1268871537325125723035723 1903307305987688584553585)
              ·
                refine ⟨1427480479490766438415189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1903307305987688584553585 1427480479490766438415189)
                ·
                  refine ⟨8364143434516209600089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 1427480479490766438415189 8364143434516209600089)
                  ·
                    rfl

theorem cell22_73301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 2, 9].length) (baseStart_73301 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_73301 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_73301 prefixEnd_73301 := by exact prefixLift 73301
  have htrace : WordTrace (prefixWord ++ tailWord_73301) baseStart_73301 baseEnd_73301 := by
    simpa [prefixWord, tailWord_73301, baseEnd_73301] using wordTrace_append hprefix tailTrace_73301
  have hstable : (prefixWord ++ tailWord_73301).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_73301).length < 2 ^ (prefixWord ++ tailWord_73301).sum := by decide
  have hdescent : baseEnd_73301 < baseStart_73301 := by decide
  rcases family_descends (prefixWord ++ tailWord_73301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_73309 : List Nat := [1, 4, 4, 2, 1, 2, 1, 1, 2, 4]
def baseStart_73309 : Nat := 118140960795 + 73309 * 2 ^ 59
def prefixEnd_73309 : Nat := 4983230072969 + 3 ^ 40 * 73309 * 2
def baseEnd_73309 : Nat := 25095168867039274600243

theorem tailTrace_73309 : CollatzResearch.WordTrace tailWord_73309 prefixEnd_73309 25095168867039274600243 := by
  unfold tailWord_73309
  simp only [CollatzResearch.WordTrace]
  refine ⟨2673798891421488025526981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1782532594280992017017987 2673798891421488025526981)
  ·
    refine ⟨501337292141529004786309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2673798891421488025526981 501337292141529004786309)
    ·
      refine ⟨94000742276536688397433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 501337292141529004786309 94000742276536688397433)
      ·
        refine ⟨70500556707402516298075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94000742276536688397433 70500556707402516298075)
        ·
          refine ⟨105750835061103774447113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70500556707402516298075 105750835061103774447113)
          ·
            refine ⟨79313126295827830835335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 105750835061103774447113 79313126295827830835335)
            ·
              refine ⟨118969689443741746253003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79313126295827830835335 118969689443741746253003)
              ·
                refine ⟨178454534165612619379505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 118969689443741746253003 178454534165612619379505)
                ·
                  refine ⟨133840900624209464534629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 178454534165612619379505 133840900624209464534629)
                  ·
                    refine ⟨25095168867039274600243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 133840900624209464534629 25095168867039274600243)
                    ·
                      rfl

theorem cell22_73309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 2, 1, 1, 2, 4].length) (baseStart_73309 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_73309 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_73309 prefixEnd_73309 := by exact prefixLift 73309
  have htrace : WordTrace (prefixWord ++ tailWord_73309) baseStart_73309 baseEnd_73309 := by
    simpa [prefixWord, tailWord_73309, baseEnd_73309] using wordTrace_append hprefix tailTrace_73309
  have hstable : (prefixWord ++ tailWord_73309).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_73309).length < 2 ^ (prefixWord ++ tailWord_73309).sum := by decide
  have hdescent : baseEnd_73309 < baseStart_73309 := by decide
  rcases family_descends (prefixWord ++ tailWord_73309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_73322 : List Nat := [3, 1, 3, 2, 1, 2, 1, 5, 1, 3]
def baseStart_73322 : Nat := 118140960795 + 73322 * 2 ^ 59
def prefixEnd_73322 : Nat := 4983230072969 + 3 ^ 40 * 73322 * 2
def baseEnd_73322 : Nat := 25099619032711574025203

theorem tailTrace_73322 : CollatzResearch.WordTrace tailWord_73322 prefixEnd_73322 25099619032711574025203 := by
  unfold tailWord_73322
  simp only [CollatzResearch.WordTrace]
  refine ⟨668568260093597811437555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1782848693582927497166813 668568260093597811437555)
  ·
    refine ⟨1002852390140396717156333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 668568260093597811437555 1002852390140396717156333)
    ·
      refine ⟨376069646302648768933625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1002852390140396717156333 376069646302648768933625)
      ·
        refine ⟨282052234726986576700219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 376069646302648768933625 282052234726986576700219)
        ·
          refine ⟨423078352090479865050329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 282052234726986576700219 423078352090479865050329)
          ·
            refine ⟨317308764067859898787747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 423078352090479865050329 317308764067859898787747)
            ·
              refine ⟨475963146101789848181621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 317308764067859898787747 475963146101789848181621)
              ·
                refine ⟨44621544947042798267027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 475963146101789848181621 44621544947042798267027)
                ·
                  refine ⟨66932317420564197400541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44621544947042798267027 66932317420564197400541)
                  ·
                    refine ⟨25099619032711574025203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 66932317420564197400541 25099619032711574025203)
                    ·
                      rfl

theorem cell22_73322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 5, 1, 3].length) (baseStart_73322 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_73322 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_73322 prefixEnd_73322 := by exact prefixLift 73322
  have htrace : WordTrace (prefixWord ++ tailWord_73322) baseStart_73322 baseEnd_73322 := by
    simpa [prefixWord, tailWord_73322, baseEnd_73322] using wordTrace_append hprefix tailTrace_73322
  have hstable : (prefixWord ++ tailWord_73322).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_73322).length < 2 ^ (prefixWord ++ tailWord_73322).sum := by decide
  have hdescent : baseEnd_73322 < baseStart_73322 := by decide
  rcases family_descends (prefixWord ++ tailWord_73322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_73395 : List Nat := [1, 1, 1, 2, 3, 3, 2, 4, 2, 3]
def baseStart_73395 : Nat := 118140960795 + 73395 * 2 ^ 59
def prefixEnd_73395 : Nat := 4983230072969 + 3 ^ 40 * 73395 * 2
def baseEnd_73395 : Nat := 25124608424563716949979

theorem tailTrace_73395 : CollatzResearch.WordTrace tailWord_73395 prefixEnd_73395 25124608424563716949979 := by
  unfold tailWord_73395
  simp only [CollatzResearch.WordTrace]
  refine ⟨2676935569109924713157639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1784623712739949808771759 2676935569109924713157639)
  ·
    refine ⟨4015403353664887069736459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2676935569109924713157639 4015403353664887069736459)
    ·
      refine ⟨6023105030497330604604689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4015403353664887069736459 6023105030497330604604689)
      ·
        refine ⟨4517328772872997953453517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6023105030497330604604689 4517328772872997953453517)
        ·
          refine ⟨1693998289827374232545069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4517328772872997953453517 1693998289827374232545069)
          ·
            refine ⟨635249358685265337204401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1693998289827374232545069 635249358685265337204401)
            ·
              refine ⟨476437019013949002903301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 635249358685265337204401 476437019013949002903301)
              ·
                refine ⟨89331941065115438044369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 476437019013949002903301 89331941065115438044369)
                ·
                  refine ⟨66998955798836578533277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 89331941065115438044369 66998955798836578533277)
                  ·
                    refine ⟨25124608424563716949979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 66998955798836578533277 25124608424563716949979)
                    ·
                      rfl

theorem cell22_73395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 4, 2, 3].length) (baseStart_73395 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_73395 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_73395 prefixEnd_73395 := by exact prefixLift 73395
  have htrace : WordTrace (prefixWord ++ tailWord_73395) baseStart_73395 baseEnd_73395 := by
    simpa [prefixWord, tailWord_73395, baseEnd_73395] using wordTrace_append hprefix tailTrace_73395
  have hstable : (prefixWord ++ tailWord_73395).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_73395).length < 2 ^ (prefixWord ++ tailWord_73395).sum := by decide
  have hdescent : baseEnd_73395 < baseStart_73395 := by decide
  rcases family_descends (prefixWord ++ tailWord_73395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_73397 : List Nat := [1, 3, 3, 3, 2, 2, 1, 1, 6]
def baseStart_73397 : Nat := 118140960795 + 73397 * 2 ^ 59
def prefixEnd_73397 : Nat := 4983230072969 + 3 ^ 40 * 73397 * 2
def baseEnd_73397 : Nat := 8375097688478792799991

theorem tailTrace_73397 : CollatzResearch.WordTrace tailWord_73397 prefixEnd_73397 8375097688478792799991 := by
  unfold tailWord_73397
  simp only [CollatzResearch.WordTrace]
  refine ⟨2677008515102679054730445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1784672343401786036486963 2677008515102679054730445)
  ·
    refine ⟨1003878193163504645523917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2677008515102679054730445 1003878193163504645523917)
    ·
      refine ⟨376454322436314242071469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1003878193163504645523917 376454322436314242071469)
      ·
        refine ⟨141170370913617840776801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 376454322436314242071469 141170370913617840776801)
        ·
          refine ⟨105877778185213380582601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 141170370913617840776801 105877778185213380582601)
          ·
            refine ⟨79408333638910035436951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 105877778185213380582601 79408333638910035436951)
            ·
              refine ⟨119112500458365053155427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79408333638910035436951 119112500458365053155427)
              ·
                refine ⟨178668750687547579733141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 119112500458365053155427 178668750687547579733141)
                ·
                  refine ⟨8375097688478792799991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 178668750687547579733141 8375097688478792799991)
                  ·
                    rfl

theorem cell22_73397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 2, 1, 1, 6].length) (baseStart_73397 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_73397 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_73397 prefixEnd_73397 := by exact prefixLift 73397
  have htrace : WordTrace (prefixWord ++ tailWord_73397) baseStart_73397 baseEnd_73397 := by
    simpa [prefixWord, tailWord_73397, baseEnd_73397] using wordTrace_append hprefix tailTrace_73397
  have hstable : (prefixWord ++ tailWord_73397).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_73397).length < 2 ^ (prefixWord ++ tailWord_73397).sum := by decide
  have hdescent : baseEnd_73397 < baseStart_73397 := by decide
  rcases family_descends (prefixWord ++ tailWord_73397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_73408 : List Nat := [2, 1, 1, 2, 4, 1, 4, 7]
def baseStart_73408 : Nat := 118140960795 + 73408 * 2 ^ 59
def prefixEnd_73408 : Nat := 4983230072969 + 3 ^ 40 * 73408 * 2
def baseEnd_73408 : Nat := 2792117621137335152771

theorem tailTrace_73408 : CollatzResearch.WordTrace tailWord_73408 prefixEnd_73408 2792117621137335152771 := by
  unfold tailWord_73408
  simp only [CollatzResearch.WordTrace]
  refine ⟨1338704859031413966690439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1784939812041885288920585 1338704859031413966690439)
  ·
    refine ⟨2008057288547120950035659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1338704859031413966690439 2008057288547120950035659)
    ·
      refine ⟨3012085932820681425053489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2008057288547120950035659 3012085932820681425053489)
      ·
        refine ⟨2259064449615511068790117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3012085932820681425053489 2259064449615511068790117)
        ·
          refine ⟨423574584302908325398147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2259064449615511068790117 423574584302908325398147)
          ·
            refine ⟨635361876454362488097221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 423574584302908325398147 635361876454362488097221)
            ·
              refine ⟨119130351835192966518229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 635361876454362488097221 119130351835192966518229)
              ·
                refine ⟨2792117621137335152771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 119130351835192966518229 2792117621137335152771)
                ·
                  rfl

theorem cell22_73408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 4, 7].length) (baseStart_73408 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_73408 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_73408 prefixEnd_73408 := by exact prefixLift 73408
  have htrace : WordTrace (prefixWord ++ tailWord_73408) baseStart_73408 baseEnd_73408 := by
    simpa [prefixWord, tailWord_73408, baseEnd_73408] using wordTrace_append hprefix tailTrace_73408
  have hstable : (prefixWord ++ tailWord_73408).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_73408).length < 2 ^ (prefixWord ++ tailWord_73408).sum := by decide
  have hdescent : baseEnd_73408 < baseStart_73408 := by decide
  rcases family_descends (prefixWord ++ tailWord_73408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_73412 : List Nat := [2, 3, 3, 1, 1, 1, 3, 3, 2, 3]
def baseStart_73412 : Nat := 118140960795 + 73412 * 2 ^ 59
def prefixEnd_73412 : Nat := 4983230072969 + 3 ^ 40 * 73412 * 2
def baseEnd_73412 : Nat := 25130427871981339274927

theorem tailTrace_73412 : CollatzResearch.WordTrace tailWord_73412 prefixEnd_73412 25130427871981339274927 := by
  unfold tailWord_73412
  simp only [CollatzResearch.WordTrace]
  refine ⟨1338777805024168308263245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1785037073365557744350993 1338777805024168308263245)
  ·
    refine ⟨502041676884063115598717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1338777805024168308263245 502041676884063115598717)
    ·
      refine ⟨188265628831523668349519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 502041676884063115598717 188265628831523668349519)
      ·
        refine ⟨282398443247285502524279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 188265628831523668349519 282398443247285502524279)
        ·
          refine ⟨423597664870928253786419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 282398443247285502524279 423597664870928253786419)
          ·
            refine ⟨635396497306392380679629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 423597664870928253786419 635396497306392380679629)
            ·
              refine ⟨238273686489897142754861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 635396497306392380679629 238273686489897142754861)
              ·
                refine ⟨89352632433711428533073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 238273686489897142754861 89352632433711428533073)
                ·
                  refine ⟨67014474325283571399805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 89352632433711428533073 67014474325283571399805)
                  ·
                    refine ⟨25130427871981339274927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 67014474325283571399805 25130427871981339274927)
                    ·
                      rfl

theorem cell22_73412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 3, 3, 2, 3].length) (baseStart_73412 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_73412 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_73412 prefixEnd_73412 := by exact prefixLift 73412
  have htrace : WordTrace (prefixWord ++ tailWord_73412) baseStart_73412 baseEnd_73412 := by
    simpa [prefixWord, tailWord_73412, baseEnd_73412] using wordTrace_append hprefix tailTrace_73412
  have hstable : (prefixWord ++ tailWord_73412).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_73412).length < 2 ^ (prefixWord ++ tailWord_73412).sum := by decide
  have hdescent : baseEnd_73412 < baseStart_73412 := by decide
  rcases family_descends (prefixWord ++ tailWord_73412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_73478 : List Nat := [6, 2, 2, 1, 1, 1, 1, 1, 1, 6]
def baseStart_73478 : Nat := 118140960795 + 73478 * 2 ^ 59
def prefixEnd_73478 : Nat := 4983230072969 + 3 ^ 40 * 73478 * 2
def baseEnd_73478 : Nat := 25153021020779167124725

theorem tailTrace_73478 : CollatzResearch.WordTrace tailWord_73478 prefixEnd_73478 25153021020779167124725 := by
  unfold tailWord_73478
  simp only [CollatzResearch.WordTrace]
  refine ⟨83748838369038434013409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 1786641885206153258952725 83748838369038434013409)
  ·
    refine ⟨62811628776778825510057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83748838369038434013409 62811628776778825510057)
    ·
      refine ⟨47108721582584119132543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62811628776778825510057 47108721582584119132543)
      ·
        refine ⟨70663082373876178698815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47108721582584119132543 70663082373876178698815)
        ·
          refine ⟨105994623560814268048223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70663082373876178698815 105994623560814268048223)
          ·
            refine ⟨158991935341221402072335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105994623560814268048223 158991935341221402072335)
            ·
              refine ⟨238487903011832103108503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 158991935341221402072335 238487903011832103108503)
              ·
                refine ⟨357731854517748154662755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 238487903011832103108503 357731854517748154662755)
                ·
                  refine ⟨536597781776622231994133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 357731854517748154662755 536597781776622231994133)
                  ·
                    refine ⟨25153021020779167124725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 536597781776622231994133 25153021020779167124725)
                    ·
                      rfl

theorem cell22_73478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 1, 1, 1, 6].length) (baseStart_73478 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_73478 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_73478 prefixEnd_73478 := by exact prefixLift 73478
  have htrace : WordTrace (prefixWord ++ tailWord_73478) baseStart_73478 baseEnd_73478 := by
    simpa [prefixWord, tailWord_73478, baseEnd_73478] using wordTrace_append hprefix tailTrace_73478
  have hstable : (prefixWord ++ tailWord_73478).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_73478).length < 2 ^ (prefixWord ++ tailWord_73478).sum := by decide
  have hdescent : baseEnd_73478 < baseStart_73478 := by decide
  rcases family_descends (prefixWord ++ tailWord_73478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_73534 : List Nat := [4, 2, 1, 2, 2, 2, 2, 2, 1, 4]
def baseStart_73534 : Nat := 118140960795 + 73534 * 2 ^ 59
def prefixEnd_73534 : Nat := 4983230072969 + 3 ^ 40 * 73534 * 2
def baseEnd_73534 : Nat := 25172190965213687724553

theorem tailTrace_73534 : CollatzResearch.WordTrace tailWord_73534 prefixEnd_73534 25172190965213687724553 := by
  unfold tailWord_73534
  simp only [CollatzResearch.WordTrace]
  refine ⟨335250664450793931558457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1788003543737567634978437 335250664450793931558457)
  ·
    refine ⟨251437998338095448668843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 335250664450793931558457 251437998338095448668843)
    ·
      refine ⟨377156997507143173003265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 251437998338095448668843 377156997507143173003265)
      ·
        refine ⟨282867748130357379752449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 377156997507143173003265 282867748130357379752449)
        ·
          refine ⟨212150811097768034814337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 282867748130357379752449 212150811097768034814337)
          ·
            refine ⟨159113108323326026110753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 212150811097768034814337 159113108323326026110753)
            ·
              refine ⟨119334831242494519583065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 159113108323326026110753 119334831242494519583065)
              ·
                refine ⟨89501123431870889687299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 119334831242494519583065 89501123431870889687299)
                ·
                  refine ⟨134251685147806334530949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 89501123431870889687299 134251685147806334530949)
                  ·
                    refine ⟨25172190965213687724553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 134251685147806334530949 25172190965213687724553)
                    ·
                      rfl

theorem cell22_73534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 2, 2, 1, 4].length) (baseStart_73534 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_73534 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_73534 prefixEnd_73534 := by exact prefixLift 73534
  have htrace : WordTrace (prefixWord ++ tailWord_73534) baseStart_73534 baseEnd_73534 := by
    simpa [prefixWord, tailWord_73534, baseEnd_73534] using wordTrace_append hprefix tailTrace_73534
  have hstable : (prefixWord ++ tailWord_73534).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_73534).length < 2 ^ (prefixWord ++ tailWord_73534).sum := by decide
  have hdescent : baseEnd_73534 < baseStart_73534 := by decide
  rcases family_descends (prefixWord ++ tailWord_73534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_73545 : List Nat := [1, 2, 1, 1, 2, 4, 2, 3, 2, 4]
def baseStart_73545 : Nat := 118140960795 + 73545 * 2 ^ 59
def prefixEnd_73545 : Nat := 4983230072969 + 3 ^ 40 * 73545 * 2
def baseEnd_73545 : Nat := 25175956490013325699519

theorem tailTrace_73545 : CollatzResearch.WordTrace tailWord_73545 prefixEnd_73545 25175956490013325699519 := by
  unfold tailWord_73545
  simp only [CollatzResearch.WordTrace]
  refine ⟨2682406518566500331118089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1788271012377666887412059 2682406518566500331118089)
  ·
    refine ⟨2011804888924875248338567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2682406518566500331118089 2011804888924875248338567)
    ·
      refine ⟨3017707333387312872507851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2011804888924875248338567 3017707333387312872507851)
      ·
        refine ⟨4526561000080969308761777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3017707333387312872507851 4526561000080969308761777)
        ·
          refine ⟨3394920750060726981571333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4526561000080969308761777 3394920750060726981571333)
          ·
            refine ⟨636547640636386309044625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3394920750060726981571333 636547640636386309044625)
            ·
              refine ⟨477410730477289731783469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 636547640636386309044625 477410730477289731783469)
              ·
                refine ⟨179029023928983649418801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 477410730477289731783469 179029023928983649418801)
                ·
                  refine ⟨134271767946737737064101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 179029023928983649418801 134271767946737737064101)
                  ·
                    refine ⟨25175956490013325699519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 134271767946737737064101 25175956490013325699519)
                    ·
                      rfl

theorem cell22_73545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 3, 2, 4].length) (baseStart_73545 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_73545 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_73545 prefixEnd_73545 := by exact prefixLift 73545
  have htrace : WordTrace (prefixWord ++ tailWord_73545) baseStart_73545 baseEnd_73545 := by
    simpa [prefixWord, tailWord_73545, baseEnd_73545] using wordTrace_append hprefix tailTrace_73545
  have hstable : (prefixWord ++ tailWord_73545).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_73545).length < 2 ^ (prefixWord ++ tailWord_73545).sum := by decide
  have hdescent : baseEnd_73545 < baseStart_73545 := by decide
  rcases family_descends (prefixWord ++ tailWord_73545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_73609 : List Nat := [1, 2, 1, 1, 5, 1, 2, 5, 1, 3]
def baseStart_73609 : Nat := 118140960795 + 73609 * 2 ^ 59
def prefixEnd_73609 : Nat := 4983230072969 + 3 ^ 40 * 73609 * 2
def baseEnd_73609 : Nat := 25197864997938492099323

theorem tailTrace_73609 : CollatzResearch.WordTrace tailWord_73609 prefixEnd_73609 25197864997938492099323 := by
  unfold tailWord_73609
  simp only [CollatzResearch.WordTrace]
  refine ⟨2684740790334639261447881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1789827193556426174298587 2684740790334639261447881)
  ·
    refine ⟨2013555592750979446085911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2684740790334639261447881 2013555592750979446085911)
    ·
      refine ⟨3020333389126469169128867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2013555592750979446085911 3020333389126469169128867)
      ·
        refine ⟨4530500083689703753693301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3020333389126469169128867 4530500083689703753693301)
        ·
          refine ⟨424734382845909726908747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4530500083689703753693301 424734382845909726908747)
          ·
            refine ⟨637101574268864590363121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 424734382845909726908747 637101574268864590363121)
            ·
              refine ⟨477826180701648442772341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 637101574268864590363121 477826180701648442772341)
              ·
                refine ⟨44796204440779541509907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 477826180701648442772341 44796204440779541509907)
                ·
                  refine ⟨67194306661169312264861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44796204440779541509907 67194306661169312264861)
                  ·
                    refine ⟨25197864997938492099323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 67194306661169312264861 25197864997938492099323)
                    ·
                      rfl

theorem cell22_73609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 5, 1, 3].length) (baseStart_73609 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_73609 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_73609 prefixEnd_73609 := by exact prefixLift 73609
  have htrace : WordTrace (prefixWord ++ tailWord_73609) baseStart_73609 baseEnd_73609 := by
    simpa [prefixWord, tailWord_73609, baseEnd_73609] using wordTrace_append hprefix tailTrace_73609
  have hstable : (prefixWord ++ tailWord_73609).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_73609).length < 2 ^ (prefixWord ++ tailWord_73609).sum := by decide
  have hdescent : baseEnd_73609 < baseStart_73609 := by decide
  rcases family_descends (prefixWord ++ tailWord_73609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_73626 : List Nat := [3, 1, 1, 4, 2, 2, 1, 4, 1, 3]
def baseStart_73626 : Nat := 118140960795 + 73626 * 2 ^ 59
def prefixEnd_73626 : Nat := 4983230072969 + 3 ^ 40 * 73626 * 2
def baseEnd_73626 : Nat := 25203684445356114424271

theorem tailTrace_73626 : CollatzResearch.WordTrace tailWord_73626 prefixEnd_73626 25203684445356114424271 := by
  unfold tailWord_73626
  simp only [CollatzResearch.WordTrace]
  refine ⟨671340207818262791204183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1790240554182034109877821 671340207818262791204183)
  ·
    refine ⟨1007010311727394186806275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 671340207818262791204183 1007010311727394186806275)
    ·
      refine ⟨1510515467591091280209413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1007010311727394186806275 1510515467591091280209413)
      ·
        refine ⟨283221650173329615039265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1510515467591091280209413 283221650173329615039265)
        ·
          refine ⟨212416237629997211279449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 283221650173329615039265 212416237629997211279449)
          ·
            refine ⟨159312178222497908459587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 212416237629997211279449 159312178222497908459587)
            ·
              refine ⟨238968267333746862689381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 159312178222497908459587 238968267333746862689381)
              ·
                refine ⟨44806550125077536754259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 238968267333746862689381 44806550125077536754259)
                ·
                  refine ⟨67209825187616305131389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44806550125077536754259 67209825187616305131389)
                  ·
                    refine ⟨25203684445356114424271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 67209825187616305131389 25203684445356114424271)
                    ·
                      rfl

theorem cell22_73626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 1, 4, 1, 3].length) (baseStart_73626 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_73626 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_73626 prefixEnd_73626 := by exact prefixLift 73626
  have htrace : WordTrace (prefixWord ++ tailWord_73626) baseStart_73626 baseEnd_73626 := by
    simpa [prefixWord, tailWord_73626, baseEnd_73626] using wordTrace_append hprefix tailTrace_73626
  have hstable : (prefixWord ++ tailWord_73626).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_73626).length < 2 ^ (prefixWord ++ tailWord_73626).sum := by decide
  have hdescent : baseEnd_73626 < baseStart_73626 := by decide
  rcases family_descends (prefixWord ++ tailWord_73626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_73684 : List Nat := [2, 4, 1, 2, 1, 1, 1, 6, 4]
def baseStart_73684 : Nat := 118140960795 + 73684 * 2 ^ 59
def prefixEnd_73684 : Nat := 4983230072969 + 3 ^ 40 * 73684 * 2
def baseEnd_73684 : Nat := 8407846343554432158031

theorem tailTrace_73684 : CollatzResearch.WordTrace tailWord_73684 prefixEnd_73684 8407846343554432158031 := by
  unfold tailWord_73684
  simp only [CollatzResearch.WordTrace]
  refine ⟨1343738132531463535214053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1791650843375284713618737 1343738132531463535214053)
  ·
    refine ⟨251950899849649412852635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1343738132531463535214053 251950899849649412852635)
    ·
      refine ⟨377926349774474119278953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 251950899849649412852635 377926349774474119278953)
      ·
        refine ⟨283444762330855589459215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 377926349774474119278953 283444762330855589459215)
        ·
          refine ⟨425167143496283384188823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 283444762330855589459215 425167143496283384188823)
          ·
            refine ⟨637750715244425076283235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 425167143496283384188823 637750715244425076283235)
            ·
              refine ⟨956626072866637614424853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 637750715244425076283235 956626072866637614424853)
              ·
                refine ⟨44841847165623638176165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 956626072866637614424853 44841847165623638176165)
                ·
                  refine ⟨8407846343554432158031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 44841847165623638176165 8407846343554432158031)
                  ·
                    rfl

theorem cell22_73684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 6, 4].length) (baseStart_73684 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_73684 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_73684 prefixEnd_73684 := by exact prefixLift 73684
  have htrace : WordTrace (prefixWord ++ tailWord_73684) baseStart_73684 baseEnd_73684 := by
    simpa [prefixWord, tailWord_73684, baseEnd_73684] using wordTrace_append hprefix tailTrace_73684
  have hstable : (prefixWord ++ tailWord_73684).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_73684).length < 2 ^ (prefixWord ++ tailWord_73684).sum := by decide
  have hdescent : baseEnd_73684 < baseStart_73684 := by decide
  rcases family_descends (prefixWord ++ tailWord_73684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_73699 : List Nat := [1, 1, 1, 6, 1, 4, 1, 1, 1, 5]
def baseStart_73699 : Nat := 118140960795 + 73699 * 2 ^ 59
def prefixEnd_73699 : Nat := 4983230072969 + 3 ^ 40 * 73699 * 2
def baseEnd_73699 : Nat := 25228673837208257349047

theorem tailTrace_73699 : CollatzResearch.WordTrace tailWord_73699 prefixEnd_73699 25228673837208257349047 := by
  unfold tailWord_73699
  simp only [CollatzResearch.WordTrace]
  refine ⟨2688023360008584632224151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1792015573339056421482767 2688023360008584632224151)
  ·
    refine ⟨4032035040012876948336227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2688023360008584632224151 4032035040012876948336227)
    ·
      refine ⟨6048052560019315422504341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4032035040012876948336227 6048052560019315422504341)
      ·
        refine ⟨283502463750905410429891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 6048052560019315422504341 283502463750905410429891)
        ·
          refine ⟨425253695626358115644837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 283502463750905410429891 425253695626358115644837)
          ·
            refine ⟨79735067929942146683407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 425253695626358115644837 79735067929942146683407)
            ·
              refine ⟨119602601894913220025111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79735067929942146683407 119602601894913220025111)
              ·
                refine ⟨179403902842369830037667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 119602601894913220025111 179403902842369830037667)
                ·
                  refine ⟨269105854263554745056501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 179403902842369830037667 269105854263554745056501)
                  ·
                    refine ⟨25228673837208257349047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 269105854263554745056501 25228673837208257349047)
                    ·
                      rfl

theorem cell22_73699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 4, 1, 1, 1, 5].length) (baseStart_73699 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_73699 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_73699 prefixEnd_73699 := by exact prefixLift 73699
  have htrace : WordTrace (prefixWord ++ tailWord_73699) baseStart_73699 baseEnd_73699 := by
    simpa [prefixWord, tailWord_73699, baseEnd_73699] using wordTrace_append hprefix tailTrace_73699
  have hstable : (prefixWord ++ tailWord_73699).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_73699).length < 2 ^ (prefixWord ++ tailWord_73699).sum := by decide
  have hdescent : baseEnd_73699 < baseStart_73699 := by decide
  rcases family_descends (prefixWord ++ tailWord_73699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_73712 : List Nat := [2, 1, 1, 1, 3, 2, 6, 6]
def baseStart_73712 : Nat := 118140960795 + 73712 * 2 ^ 59
def prefixEnd_73712 : Nat := 4983230072969 + 3 ^ 40 * 73712 * 2
def baseEnd_73712 : Nat := 2803680444764506308223

theorem tailTrace_73712 : CollatzResearch.WordTrace tailWord_73712 prefixEnd_73712 2803680444764506308223 := by
  unfold tailWord_73712
  simp only [CollatzResearch.WordTrace]
  refine ⟨1344248754480743926223695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1792331672640991901631593 1344248754480743926223695)
  ·
    refine ⟨2016373131721115889335543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1344248754480743926223695 2016373131721115889335543)
    ·
      refine ⟨3024559697581673834003315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2016373131721115889335543 3024559697581673834003315)
      ·
        refine ⟨4536839546372510751004973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3024559697581673834003315 4536839546372510751004973)
        ·
          refine ⟨1701314829889691531626865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4536839546372510751004973 1701314829889691531626865)
          ·
            refine ⟨1275986122417268648720149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1701314829889691531626865 1275986122417268648720149)
            ·
              refine ⟨59811849488309467908757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1275986122417268648720149 59811849488309467908757)
              ·
                refine ⟨2803680444764506308223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 59811849488309467908757 2803680444764506308223)
                ·
                  rfl

theorem cell22_73712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 6, 6].length) (baseStart_73712 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_73712 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_73712 prefixEnd_73712 := by exact prefixLift 73712
  have htrace : WordTrace (prefixWord ++ tailWord_73712) baseStart_73712 baseEnd_73712 := by
    simpa [prefixWord, tailWord_73712, baseEnd_73712] using wordTrace_append hprefix tailTrace_73712
  have hstable : (prefixWord ++ tailWord_73712).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_73712).length < 2 ^ (prefixWord ++ tailWord_73712).sum := by decide
  have hdescent : baseEnd_73712 < baseStart_73712 := by decide
  rcases family_descends (prefixWord ++ tailWord_73712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_73718 : List Nat := [5, 1, 1, 1, 4, 2, 1, 3, 4]
def baseStart_73718 : Nat := 118140960795 + 73718 * 2 ^ 59
def prefixEnd_73718 : Nat := 4983230072969 + 3 ^ 40 * 73718 * 2
def baseEnd_73718 : Nat := 8411725975166180374663

theorem tailTrace_73718 : CollatzResearch.WordTrace tailWord_73718 prefixEnd_73718 8411725975166180374663 := by
  unfold tailWord_73718
  simp only [CollatzResearch.WordTrace]
  refine ⟨168044771683734429822863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1792477564626500584777205 168044771683734429822863)
  ·
    refine ⟨252067157525601644734295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168044771683734429822863 252067157525601644734295)
    ·
      refine ⟨378100736288402467101443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 252067157525601644734295 378100736288402467101443)
      ·
        refine ⟨567151104432603700652165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 378100736288402467101443 567151104432603700652165)
        ·
          refine ⟨106340832081113193872281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 567151104432603700652165 106340832081113193872281)
          ·
            refine ⟨79755624060834895404211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 106340832081113193872281 79755624060834895404211)
            ·
              refine ⟨119633436091252343106317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79755624060834895404211 119633436091252343106317)
              ·
                refine ⟨44862538534219628664869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 119633436091252343106317 44862538534219628664869)
                ·
                  refine ⟨8411725975166180374663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 44862538534219628664869 8411725975166180374663)
                  ·
                    rfl

theorem cell22_73718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 2, 1, 3, 4].length) (baseStart_73718 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_73718 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_73718 prefixEnd_73718 := by exact prefixLift 73718
  have htrace : WordTrace (prefixWord ++ tailWord_73718) baseStart_73718 baseEnd_73718 := by
    simpa [prefixWord, tailWord_73718, baseEnd_73718] using wordTrace_append hprefix tailTrace_73718
  have hstable : (prefixWord ++ tailWord_73718).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_73718).length < 2 ^ (prefixWord ++ tailWord_73718).sum := by decide
  have hdescent : baseEnd_73718 < baseStart_73718 := by decide
  rcases family_descends (prefixWord ++ tailWord_73718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_73727 : List Nat := [1, 1, 2, 2, 1, 2, 1, 4, 5, 3]
def baseStart_73727 : Nat := 118140960795 + 73727 * 2 ^ 59
def prefixEnd_73727 : Nat := 4983230072969 + 3 ^ 40 * 73727 * 2
def baseEnd_73727 : Nat := 25238258809425517648961

theorem tailTrace_73727 : CollatzResearch.WordTrace tailWord_73727 prefixEnd_73727 25238258809425517648961 := by
  unfold tailWord_73727
  simp only [CollatzResearch.WordTrace]
  refine ⟨2689044603907145414243435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1792696402604763609495623 2689044603907145414243435)
  ·
    refine ⟨4033566905860718121365153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2689044603907145414243435 4033566905860718121365153)
    ·
      refine ⟨3025175179395538591023865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4033566905860718121365153 3025175179395538591023865)
      ·
        refine ⟨2268881384546653943267899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3025175179395538591023865 2268881384546653943267899)
        ·
          refine ⟨3403322076819980914901849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2268881384546653943267899 3403322076819980914901849)
          ·
            refine ⟨2552491557614985686176387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3403322076819980914901849 2552491557614985686176387)
            ·
              refine ⟨3828737336422478529264581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2552491557614985686176387 3828737336422478529264581)
              ·
                refine ⟨717888250579214724237109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3828737336422478529264581 717888250579214724237109)
                ·
                  refine ⟨67302023491801380397229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 717888250579214724237109 67302023491801380397229)
                  ·
                    refine ⟨25238258809425517648961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 67302023491801380397229 25238258809425517648961)
                    ·
                      rfl

theorem cell22_73727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 4, 5, 3].length) (baseStart_73727 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_73727 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_73727 prefixEnd_73727 := by exact prefixLift 73727
  have htrace : WordTrace (prefixWord ++ tailWord_73727) baseStart_73727 baseEnd_73727 := by
    simpa [prefixWord, tailWord_73727, baseEnd_73727] using wordTrace_append hprefix tailTrace_73727
  have hstable : (prefixWord ++ tailWord_73727).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_73727).length < 2 ^ (prefixWord ++ tailWord_73727).sum := by decide
  have hdescent : baseEnd_73727 < baseStart_73727 := by decide
  rcases family_descends (prefixWord ++ tailWord_73727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_73742 : List Nat := [4, 1, 1, 2, 2, 1, 2, 1, 2, 6]
def baseStart_73742 : Nat := 118140960795 + 73742 * 2 ^ 59
def prefixEnd_73742 : Nat := 4983230072969 + 3 ^ 40 * 73742 * 2
def baseEnd_73742 : Nat := 25243393615970478523915

theorem tailTrace_73742 : CollatzResearch.WordTrace tailWord_73742 prefixEnd_73742 25243393615970478523915 := by
  unfold tailWord_73742
  simp only [CollatzResearch.WordTrace]
  refine ⟨336198962356600372004935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1793061132568535317359653 336198962356600372004935)
  ·
    refine ⟨504298443534900558007403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 336198962356600372004935 504298443534900558007403)
    ·
      refine ⟨756447665302350837011105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 504298443534900558007403 756447665302350837011105)
      ·
        refine ⟨567335748976763127758329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 756447665302350837011105 567335748976763127758329)
        ·
          refine ⟨425501811732572345818747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 567335748976763127758329 425501811732572345818747)
          ·
            refine ⟨638252717598858518728121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 425501811732572345818747 638252717598858518728121)
            ·
              refine ⟨478689538199143889046091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 638252717598858518728121 478689538199143889046091)
              ·
                refine ⟨718034307298715833569137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 478689538199143889046091 718034307298715833569137)
                ·
                  refine ⟨538525730474036875176853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 718034307298715833569137 538525730474036875176853)
                  ·
                    refine ⟨25243393615970478523915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 538525730474036875176853 25243393615970478523915)
                    ·
                      rfl

theorem cell22_73742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 1, 2, 6].length) (baseStart_73742 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_73742 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_73742 prefixEnd_73742 := by exact prefixLift 73742
  have htrace : WordTrace (prefixWord ++ tailWord_73742) baseStart_73742 baseEnd_73742 := by
    simpa [prefixWord, tailWord_73742, baseEnd_73742] using wordTrace_append hprefix tailTrace_73742
  have hstable : (prefixWord ++ tailWord_73742).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_73742).length < 2 ^ (prefixWord ++ tailWord_73742).sum := by decide
  have hdescent : baseEnd_73742 < baseStart_73742 := by decide
  rcases family_descends (prefixWord ++ tailWord_73742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_73802 : List Nat := [3, 1, 2, 1, 1, 2, 1, 5, 6]
def baseStart_73802 : Nat := 118140960795 + 73802 * 2 ^ 59
def prefixEnd_73802 : Nat := 4983230072969 + 3 ^ 40 * 73802 * 2
def baseEnd_73802 : Nat := 8421310947383440674577

theorem tailTrace_73802 : CollatzResearch.WordTrace tailWord_73802 prefixEnd_73802 8421310947383440674577 := by
  unfold tailWord_73802
  simp only [CollatzResearch.WordTrace]
  refine ⟨672945019658858305805915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1794520052423622148815773 672945019658858305805915)
  ·
    refine ⟨1009417529488287458708873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 672945019658858305805915 1009417529488287458708873)
    ·
      refine ⟨757063147116215594031655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1009417529488287458708873 757063147116215594031655)
      ·
        refine ⟨1135594720674323391047483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 757063147116215594031655 1135594720674323391047483)
        ·
          refine ⟨1703392081011485086571225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1135594720674323391047483 1703392081011485086571225)
          ·
            refine ⟨1277544060758613814928419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1703392081011485086571225 1277544060758613814928419)
            ·
              refine ⟨1916316091137920722392629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1277544060758613814928419 1916316091137920722392629)
              ·
                refine ⟨179654633544180067724309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1916316091137920722392629 179654633544180067724309)
                ·
                  refine ⟨8421310947383440674577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 179654633544180067724309 8421310947383440674577)
                  ·
                    rfl

theorem cell22_73802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 5, 6].length) (baseStart_73802 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_73802 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_73802 prefixEnd_73802 := by exact prefixLift 73802
  have htrace : WordTrace (prefixWord ++ tailWord_73802) baseStart_73802 baseEnd_73802 := by
    simpa [prefixWord, tailWord_73802, baseEnd_73802] using wordTrace_append hprefix tailTrace_73802
  have hstable : (prefixWord ++ tailWord_73802).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_73802).length < 2 ^ (prefixWord ++ tailWord_73802).sum := by decide
  have hdescent : baseEnd_73802 < baseStart_73802 := by decide
  rcases family_descends (prefixWord ++ tailWord_73802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_73821 : List Nat := [1, 4, 4, 1, 1, 1, 2, 1, 3, 4]
def baseStart_73821 : Nat := 118140960795 + 73821 * 2 ^ 59
def prefixEnd_73821 : Nat := 4983230072969 + 3 ^ 40 * 73821 * 2
def baseEnd_73821 : Nat := 25270436930440605798673

theorem tailTrace_73821 : CollatzResearch.WordTrace tailWord_73821 prefixEnd_73821 25270436930440605798673 := by
  unfold tailWord_73821
  simp only [CollatzResearch.WordTrace]
  refine ⟨2692473065566599468165317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1794982043711066312110211 2692473065566599468165317)
  ·
    refine ⟨504838699793737400280997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2692473065566599468165317 504838699793737400280997)
    ·
      refine ⟨94657256211325762552687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 504838699793737400280997 94657256211325762552687)
      ·
        refine ⟨141985884316988643829031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94657256211325762552687 141985884316988643829031)
        ·
          refine ⟨212978826475482965743547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 141985884316988643829031 212978826475482965743547)
          ·
            refine ⟨319468239713224448615321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 212978826475482965743547 319468239713224448615321)
            ·
              refine ⟨239601179784918336461491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 319468239713224448615321 239601179784918336461491)
              ·
                refine ⟨359401769677377504692237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 239601179784918336461491 359401769677377504692237)
                ·
                  refine ⟨134775663629016564259589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 359401769677377504692237 134775663629016564259589)
                  ·
                    refine ⟨25270436930440605798673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 134775663629016564259589 25270436930440605798673)
                    ·
                      rfl

theorem cell22_73821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 2, 1, 3, 4].length) (baseStart_73821 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_73821 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_73821 prefixEnd_73821 := by exact prefixLift 73821
  have htrace : WordTrace (prefixWord ++ tailWord_73821) baseStart_73821 baseEnd_73821 := by
    simpa [prefixWord, tailWord_73821, baseEnd_73821] using wordTrace_append hprefix tailTrace_73821
  have hstable : (prefixWord ++ tailWord_73821).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_73821).length < 2 ^ (prefixWord ++ tailWord_73821).sum := by decide
  have hdescent : baseEnd_73821 < baseStart_73821 := by decide
  rcases family_descends (prefixWord ++ tailWord_73821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_73836 : List Nat := [2, 2, 1, 1, 3, 4, 2, 3, 4]
def baseStart_73836 : Nat := 118140960795 + 73836 * 2 ^ 59
def prefixEnd_73836 : Nat := 4983230072969 + 3 ^ 40 * 73836 * 2
def baseEnd_73836 : Nat := 8425190578995188891209

theorem tailTrace_73836 : CollatzResearch.WordTrace tailWord_73836 prefixEnd_73836 8425190578995188891209 := by
  unfold tailWord_73836
  simp only [CollatzResearch.WordTrace]
  refine ⟨1346510080256128514980681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1795346773674838019974241 1346510080256128514980681)
  ·
    refine ⟨1009882560192096386235511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1346510080256128514980681 1009882560192096386235511)
    ·
      refine ⟨1514823840288144579353267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1009882560192096386235511 1514823840288144579353267)
      ·
        refine ⟨2272235760432216869029901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1514823840288144579353267 2272235760432216869029901)
        ·
          refine ⟨852088410162081325886213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2272235760432216869029901 852088410162081325886213)
          ·
            refine ⟨159766576905390248603665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 852088410162081325886213 159766576905390248603665)
            ·
              refine ⟨119824932679042686452749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 159766576905390248603665 119824932679042686452749)
              ·
                refine ⟨44934349754641007419781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 119824932679042686452749 44934349754641007419781)
                ·
                  refine ⟨8425190578995188891209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 44934349754641007419781 8425190578995188891209)
                  ·
                    rfl

theorem cell22_73836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 2, 3, 4].length) (baseStart_73836 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_73836 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_73836 prefixEnd_73836 := by exact prefixLift 73836
  have htrace : WordTrace (prefixWord ++ tailWord_73836) baseStart_73836 baseEnd_73836 := by
    simpa [prefixWord, tailWord_73836, baseEnd_73836] using wordTrace_append hprefix tailTrace_73836
  have hstable : (prefixWord ++ tailWord_73836).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_73836).length < 2 ^ (prefixWord ++ tailWord_73836).sum := by decide
  have hdescent : baseEnd_73836 < baseStart_73836 := by decide
  rcases family_descends (prefixWord ++ tailWord_73836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_73847 : List Nat := [1, 1, 3, 1, 1, 6, 9]
def baseStart_73847 : Nat := 118140960795 + 73847 * 2 ^ 59
def prefixEnd_73847 : Nat := 4983230072969 + 3 ^ 40 * 73847 * 2
def baseEnd_73847 : Nat := 936271750436489061059

theorem tailTrace_73847 : CollatzResearch.WordTrace tailWord_73847 prefixEnd_73847 936271750436489061059 := by
  unfold tailWord_73847
  simp only [CollatzResearch.WordTrace]
  refine ⟨2693421363472405908611795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1795614242314937272407863 2693421363472405908611795)
  ·
    refine ⟨4040132045208608862917693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2693421363472405908611795 4040132045208608862917693)
    ·
      refine ⟨1515049516953228323594135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4040132045208608862917693 1515049516953228323594135)
      ·
        refine ⟨2272574275429842485391203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1515049516953228323594135 2272574275429842485391203)
        ·
          refine ⟨3408861413144763728086805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2272574275429842485391203 3408861413144763728086805)
          ·
            refine ⟨159790378741160799754069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 3408861413144763728086805 159790378741160799754069)
            ·
              refine ⟨936271750436489061059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 159790378741160799754069 936271750436489061059)
              ·
                rfl

theorem cell22_73847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 9].length) (baseStart_73847 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_73847 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_73847 prefixEnd_73847 := by exact prefixLift 73847
  have htrace : WordTrace (prefixWord ++ tailWord_73847) baseStart_73847 baseEnd_73847 := by
    simpa [prefixWord, tailWord_73847, baseEnd_73847] using wordTrace_append hprefix tailTrace_73847
  have hstable : (prefixWord ++ tailWord_73847).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_73847).length < 2 ^ (prefixWord ++ tailWord_73847).sum := by decide
  have hdescent : baseEnd_73847 < baseStart_73847 := by decide
  rcases family_descends (prefixWord ++ tailWord_73847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_73898 : List Nat := [3, 1, 5, 1, 3, 1, 8]
def baseStart_73898 : Nat := 118140960795 + 73898 * 2 ^ 59
def prefixEnd_73898 : Nat := 4983230072969 + 3 ^ 40 * 73898 * 2
def baseEnd_73898 : Nat := 936918355705113763831

theorem tailTrace_73898 : CollatzResearch.WordTrace tailWord_73898 prefixEnd_73898 936918355705113763831 := by
  unfold tailWord_73898
  simp only [CollatzResearch.WordTrace]
  refine ⟨673820371571910404679587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1796854324191761079145565 673820371571910404679587)
  ·
    refine ⟨1010730557357865607019381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 673820371571910404679587 1010730557357865607019381)
    ·
      refine ⟨94755989752299900658067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1010730557357865607019381 94755989752299900658067)
      ·
        refine ⟨142133984628449850987101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94755989752299900658067 142133984628449850987101)
        ·
          refine ⟨53300244235668694120163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 142133984628449850987101 53300244235668694120163)
          ·
            refine ⟨79950366353503041180245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53300244235668694120163 79950366353503041180245)
            ·
              refine ⟨936918355705113763831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 79950366353503041180245 936918355705113763831)
              ·
                rfl

theorem cell22_73898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 1, 8].length) (baseStart_73898 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_73898 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_73898 prefixEnd_73898 := by exact prefixLift 73898
  have htrace : WordTrace (prefixWord ++ tailWord_73898) baseStart_73898 baseEnd_73898 := by
    simpa [prefixWord, tailWord_73898, baseEnd_73898] using wordTrace_append hprefix tailTrace_73898
  have hstable : (prefixWord ++ tailWord_73898).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_73898).length < 2 ^ (prefixWord ++ tailWord_73898).sum := by decide
  have hdescent : baseEnd_73898 < baseStart_73898 := by decide
  rcases family_descends (prefixWord ++ tailWord_73898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_73971 : List Nat := [1, 1, 1, 2, 2, 4, 3, 4, 4]
def baseStart_73971 : Nat := 118140960795 + 73971 * 2 ^ 59
def prefixEnd_73971 : Nat := 4983230072969 + 3 ^ 40 * 73971 * 2
def baseEnd_73971 : Nat := 8440594998630071516071

theorem tailTrace_73971 : CollatzResearch.WordTrace tailWord_73971 prefixEnd_73971 8440594998630071516071 := by
  unfold tailWord_73971
  simp only [CollatzResearch.WordTrace]
  refine ⟨2697944015023175086125767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1798629343348783390750511 2697944015023175086125767)
  ·
    refine ⟨4046916022534762629188651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2697944015023175086125767 4046916022534762629188651)
    ·
      refine ⟨6070374033802143943782977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4046916022534762629188651 6070374033802143943782977)
      ·
        refine ⟨4552780525351607957837233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6070374033802143943782977 4552780525351607957837233)
        ·
          refine ⟨3414585394013705968377925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4552780525351607957837233 3414585394013705968377925)
          ·
            refine ⟨640234761377569869070861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3414585394013705968377925 640234761377569869070861)
            ·
              refine ⟨240088035516588700901573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 640234761377569869070861 240088035516588700901573)
              ·
                refine ⟨45016506659360381419045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 240088035516588700901573 45016506659360381419045)
                ·
                  refine ⟨8440594998630071516071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 45016506659360381419045 8440594998630071516071)
                  ·
                    rfl

theorem cell22_73971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 3, 4, 4].length) (baseStart_73971 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_73971 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_73971 prefixEnd_73971 := by exact prefixLift 73971
  have htrace : WordTrace (prefixWord ++ tailWord_73971) baseStart_73971 baseEnd_73971 := by
    simpa [prefixWord, tailWord_73971, baseEnd_73971] using wordTrace_append hprefix tailTrace_73971
  have hstable : (prefixWord ++ tailWord_73971).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_73971).length < 2 ^ (prefixWord ++ tailWord_73971).sum := by decide
  have hdescent : baseEnd_73971 < baseStart_73971 := by decide
  rcases family_descends (prefixWord ++ tailWord_73971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_73984 : List Nat := [2, 1, 1, 2, 1, 1, 4, 2, 4, 4]
def baseStart_73984 : Nat := 118140960795 + 73984 * 2 ^ 59
def prefixEnd_73984 : Nat := 4983230072969 + 3 ^ 40 * 73984 * 2
def baseEnd_73984 : Nat := 25326235161562513973173

theorem tailTrace_73984 : CollatzResearch.WordTrace tailWord_73984 prefixEnd_73984 25326235161562513973173 := by
  unfold tailWord_73984
  simp only [CollatzResearch.WordTrace]
  refine ⟨1349209081988039153174503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1798945442650718870899337 1349209081988039153174503)
  ·
    refine ⟨2023813622982058729761755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1349209081988039153174503 2023813622982058729761755)
    ·
      refine ⟨3035720434473088094642633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2023813622982058729761755 3035720434473088094642633)
      ·
        refine ⟨2276790325854816070981975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3035720434473088094642633 2276790325854816070981975)
        ·
          refine ⟨3415185488782224106472963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2276790325854816070981975 3415185488782224106472963)
          ·
            refine ⟨5122778233173336159709445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3415185488782224106472963 5122778233173336159709445)
            ·
              refine ⟨960520918720000529945521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5122778233173336159709445 960520918720000529945521)
              ·
                refine ⟨720390689040000397459141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 960520918720000529945521 720390689040000397459141)
                ·
                  refine ⟨135073254195000074523589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 720390689040000397459141 135073254195000074523589)
                  ·
                    refine ⟨25326235161562513973173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 135073254195000074523589 25326235161562513973173)
                    ·
                      rfl

theorem cell22_73984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 2, 4, 4].length) (baseStart_73984 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_73984 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_73984 prefixEnd_73984 := by exact prefixLift 73984
  have htrace : WordTrace (prefixWord ++ tailWord_73984) baseStart_73984 baseEnd_73984 := by
    simpa [prefixWord, tailWord_73984, baseEnd_73984] using wordTrace_append hprefix tailTrace_73984
  have hstable : (prefixWord ++ tailWord_73984).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_73984).length < 2 ^ (prefixWord ++ tailWord_73984).sum := by decide
  have hdescent : baseEnd_73984 < baseStart_73984 := by decide
  rcases family_descends (prefixWord ++ tailWord_73984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74001 : List Nat := [1, 2, 2, 1, 1, 5, 3, 1, 2, 4]
def baseStart_74001 : Nat := 118140960795 + 74001 * 2 ^ 59
def prefixEnd_74001 : Nat := 4983230072969 + 3 ^ 40 * 74001 * 2
def baseEnd_74001 : Nat := 25332054608980136298121

theorem tailTrace_74001 : CollatzResearch.WordTrace tailWord_74001 prefixEnd_74001 25332054608980136298121 := by
  unfold tailWord_74001
  simp only [CollatzResearch.WordTrace]
  refine ⟨2699038204914490209717857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1799358803276326806478571 2699038204914490209717857)
  ·
    refine ⟨2024278653685867657288393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2699038204914490209717857 2024278653685867657288393)
    ·
      refine ⟨1518208990264400742966295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2024278653685867657288393 1518208990264400742966295)
      ·
        refine ⟨2277313485396601114449443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1518208990264400742966295 2277313485396601114449443)
        ·
          refine ⟨3415970228094901671674165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2277313485396601114449443 3415970228094901671674165)
          ·
            refine ⟨320247208883897031719453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3415970228094901671674165 320247208883897031719453)
            ·
              refine ⟨120092703331461386894795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 320247208883897031719453 120092703331461386894795)
              ·
                refine ⟨180139054997192080342193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 120092703331461386894795 180139054997192080342193)
                ·
                  refine ⟨135104291247894060256645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 180139054997192080342193 135104291247894060256645)
                  ·
                    refine ⟨25332054608980136298121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 135104291247894060256645 25332054608980136298121)
                    ·
                      rfl

theorem cell22_74001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 4].length) (baseStart_74001 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_74001 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_74001 prefixEnd_74001 := by exact prefixLift 74001
  have htrace : WordTrace (prefixWord ++ tailWord_74001) baseStart_74001 baseEnd_74001 := by
    simpa [prefixWord, tailWord_74001, baseEnd_74001] using wordTrace_append hprefix tailTrace_74001
  have hstable : (prefixWord ++ tailWord_74001).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74001).length < 2 ^ (prefixWord ++ tailWord_74001).sum := by decide
  have hdescent : baseEnd_74001 < baseStart_74001 := by decide
  rcases family_descends (prefixWord ++ tailWord_74001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74020 : List Nat := [2, 3, 1, 3, 1, 4, 1, 2, 2, 3]
def baseStart_74020 : Nat := 118140960795 + 74020 * 2 ^ 59
def prefixEnd_74020 : Nat := 4983230072969 + 3 ^ 40 * 74020 * 2
def baseEnd_74020 : Nat := 25338558697270420073063

theorem tailTrace_74020 : CollatzResearch.WordTrace tailWord_74020 prefixEnd_74020 25338558697270420073063 := by
  unfold tailWord_74020
  simp only [CollatzResearch.WordTrace]
  refine ⟨1349865595922828227329757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1799820794563770969773009 1349865595922828227329757)
  ·
    refine ⟨506199598471060585248659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1349865595922828227329757 506199598471060585248659)
    ·
      refine ⟨759299397706590877872989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 506199598471060585248659 759299397706590877872989)
      ·
        refine ⟨284737274139971579202371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 759299397706590877872989 284737274139971579202371)
        ·
          refine ⟨427105911209957368803557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 284737274139971579202371 427105911209957368803557)
          ·
            refine ⟨80082358351867006650667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 427105911209957368803557 80082358351867006650667)
            ·
              refine ⟨120123537527800509976001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80082358351867006650667 120123537527800509976001)
              ·
                refine ⟨90092653145850382482001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 120123537527800509976001 90092653145850382482001)
                ·
                  refine ⟨67569489859387786861501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 90092653145850382482001 67569489859387786861501)
                  ·
                    refine ⟨25338558697270420073063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 67569489859387786861501 25338558697270420073063)
                    ·
                      rfl

theorem cell22_74020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 4, 1, 2, 2, 3].length) (baseStart_74020 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_74020 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_74020 prefixEnd_74020 := by exact prefixLift 74020
  have htrace : WordTrace (prefixWord ++ tailWord_74020) baseStart_74020 baseEnd_74020 := by
    simpa [prefixWord, tailWord_74020, baseEnd_74020] using wordTrace_append hprefix tailTrace_74020
  have hstable : (prefixWord ++ tailWord_74020).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74020).length < 2 ^ (prefixWord ++ tailWord_74020).sum := by decide
  have hdescent : baseEnd_74020 < baseStart_74020 := by decide
  rcases family_descends (prefixWord ++ tailWord_74020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74031 : List Nat := [1, 1, 2, 1, 2, 1, 5, 3, 3, 3]
def baseStart_74031 : Nat := 118140960795 + 74031 * 2 ^ 59
def prefixEnd_74031 : Nat := 4983230072969 + 3 ^ 40 * 74031 * 2
def baseEnd_74031 : Nat := 25342324222070058048029

theorem tailTrace_74031 : CollatzResearch.WordTrace tailWord_74031 prefixEnd_74031 25342324222070058048029 := by
  unfold tailWord_74031
  simp only [CollatzResearch.WordTrace]
  refine ⟨2700132394805805333309947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1800088263203870222206631 2700132394805805333309947)
  ·
    refine ⟨4050198592208707999964921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2700132394805805333309947 4050198592208707999964921)
    ·
      refine ⟨3037648944156530999973691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4050198592208707999964921 3037648944156530999973691)
      ·
        refine ⟨4556473416234796499960537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3037648944156530999973691 4556473416234796499960537)
        ·
          refine ⟨3417355062176097374970403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4556473416234796499960537 3417355062176097374970403)
          ·
            refine ⟨5126032593264146062455605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3417355062176097374970403 5126032593264146062455605)
            ·
              refine ⟨480565555618513693355213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5126032593264146062455605 480565555618513693355213)
              ·
                refine ⟨180212083356942635008205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 480565555618513693355213 180212083356942635008205)
                ·
                  refine ⟨67579531258853488128077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 180212083356942635008205 67579531258853488128077)
                  ·
                    refine ⟨25342324222070058048029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 67579531258853488128077 25342324222070058048029)
                    ·
                      rfl

theorem cell22_74031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 3, 3, 3].length) (baseStart_74031 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_74031 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_74031 prefixEnd_74031 := by exact prefixLift 74031
  have htrace : WordTrace (prefixWord ++ tailWord_74031) baseStart_74031 baseEnd_74031 := by
    simpa [prefixWord, tailWord_74031, baseEnd_74031] using wordTrace_append hprefix tailTrace_74031
  have hstable : (prefixWord ++ tailWord_74031).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74031).length < 2 ^ (prefixWord ++ tailWord_74031).sum := by decide
  have hdescent : baseEnd_74031 < baseStart_74031 := by decide
  rcases family_descends (prefixWord ++ tailWord_74031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74059 : List Nat := [1, 1, 1, 1, 3, 1, 1, 4, 4, 5]
def baseStart_74059 : Nat := 118140960795 + 74059 * 2 ^ 59
def prefixEnd_74059 : Nat := 4983230072969 + 3 ^ 40 * 74059 * 2
def baseEnd_74059 : Nat := 25351909194287318347943

theorem tailTrace_74059 : CollatzResearch.WordTrace tailWord_74059 prefixEnd_74059 25351909194287318347943 := by
  unfold tailWord_74059
  simp only [CollatzResearch.WordTrace]
  refine ⟨2701153638704366115329231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1800769092469577410219487 2701153638704366115329231)
  ·
    refine ⟨4051730458056549172993847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2701153638704366115329231 4051730458056549172993847)
    ·
      refine ⟨6077595687084823759490771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4051730458056549172993847 6077595687084823759490771)
      ·
        refine ⟨9116393530627235639236157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6077595687084823759490771 9116393530627235639236157)
        ·
          refine ⟨3418647573985213364713559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9116393530627235639236157 3418647573985213364713559)
          ·
            refine ⟨5127971360977820047070339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3418647573985213364713559 5127971360977820047070339)
            ·
              refine ⟨7691957041466730070605509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5127971360977820047070339 7691957041466730070605509)
              ·
                refine ⟨1442241945275011888238533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7691957041466730070605509 1442241945275011888238533)
                ·
                  refine ⟨270420364739064729044725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1442241945275011888238533 270420364739064729044725)
                  ·
                    refine ⟨25351909194287318347943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 270420364739064729044725 25351909194287318347943)
                    ·
                      rfl

theorem cell22_74059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 4, 4, 5].length) (baseStart_74059 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_74059 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_74059 prefixEnd_74059 := by exact prefixLift 74059
  have htrace : WordTrace (prefixWord ++ tailWord_74059) baseStart_74059 baseEnd_74059 := by
    simpa [prefixWord, tailWord_74059, baseEnd_74059] using wordTrace_append hprefix tailTrace_74059
  have hstable : (prefixWord ++ tailWord_74059).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74059).length < 2 ^ (prefixWord ++ tailWord_74059).sum := by decide
  have hdescent : baseEnd_74059 < baseStart_74059 := by decide
  rcases family_descends (prefixWord ++ tailWord_74059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74065 : List Nat := [1, 2, 2, 1, 4, 2, 3, 3, 1, 3]
def baseStart_74065 : Nat := 118140960795 + 74065 * 2 ^ 59
def prefixEnd_74065 : Nat := 4983230072969 + 3 ^ 40 * 74065 * 2
def baseEnd_74065 : Nat := 25353963116905302697925

theorem tailTrace_74065 : CollatzResearch.WordTrace tailWord_74065 prefixEnd_74065 25353963116905302697925 := by
  unfold tailWord_74065
  simp only [CollatzResearch.WordTrace]
  refine ⟨2701372476682629140047649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1800914984455086093365099 2701372476682629140047649)
  ·
    refine ⟨2026029357511971855035737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2701372476682629140047649 2026029357511971855035737)
    ·
      refine ⟨1519522018133978891276803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2026029357511971855035737 1519522018133978891276803)
      ·
        refine ⟨2279283027200968336915205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1519522018133978891276803 2279283027200968336915205)
        ·
          refine ⟨427365567600181563171601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2279283027200968336915205 427365567600181563171601)
          ·
            refine ⟨320524175700136172378701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 427365567600181563171601 320524175700136172378701)
            ·
              refine ⟨120196565887551064642013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 320524175700136172378701 120196565887551064642013)
              ·
                refine ⟨45073712207831649240755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 120196565887551064642013 45073712207831649240755)
                ·
                  refine ⟨67610568311747473861133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45073712207831649240755 67610568311747473861133)
                  ·
                    refine ⟨25353963116905302697925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 67610568311747473861133 25353963116905302697925)
                    ·
                      rfl

theorem cell22_74065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 3, 3, 1, 3].length) (baseStart_74065 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_74065 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_74065 prefixEnd_74065 := by exact prefixLift 74065
  have htrace : WordTrace (prefixWord ++ tailWord_74065) baseStart_74065 baseEnd_74065 := by
    simpa [prefixWord, tailWord_74065, baseEnd_74065] using wordTrace_append hprefix tailTrace_74065
  have hstable : (prefixWord ++ tailWord_74065).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74065).length < 2 ^ (prefixWord ++ tailWord_74065).sum := by decide
  have hdescent : baseEnd_74065 < baseStart_74065 := by decide
  rcases family_descends (prefixWord ++ tailWord_74065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74121 : List Nat := [1, 2, 1, 1, 6, 1, 1, 1, 3, 5]
def baseStart_74121 : Nat := 118140960795 + 74121 * 2 ^ 59
def prefixEnd_74121 : Nat := 4983230072969 + 3 ^ 40 * 74121 * 2
def baseEnd_74121 : Nat := 25373133061339823297753

theorem tailTrace_74121 : CollatzResearch.WordTrace tailWord_74121 prefixEnd_74121 25373133061339823297753 := by
  unfold tailWord_74121
  simp only [CollatzResearch.WordTrace]
  refine ⟨2703414964479750704086217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1802276642986500469390811 2703414964479750704086217)
  ·
    refine ⟨2027561223359813028064663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2703414964479750704086217 2027561223359813028064663)
    ·
      refine ⟨3041341835039719542096995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2027561223359813028064663 3041341835039719542096995)
      ·
        refine ⟨4562012752559579313145493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3041341835039719542096995 4562012752559579313145493)
        ·
          refine ⟨213844347776230280303695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 4562012752559579313145493 213844347776230280303695)
          ·
            refine ⟨320766521664345420455543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 213844347776230280303695 320766521664345420455543)
            ·
              refine ⟨481149782496518130683315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 320766521664345420455543 481149782496518130683315)
              ·
                refine ⟨721724673744777196024973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 481149782496518130683315 721724673744777196024973)
                ·
                  refine ⟨270646752654291448509365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 721724673744777196024973 270646752654291448509365)
                  ·
                    refine ⟨25373133061339823297753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 270646752654291448509365 25373133061339823297753)
                    ·
                      rfl

theorem cell22_74121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 1, 3, 5].length) (baseStart_74121 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_74121 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_74121 prefixEnd_74121 := by exact prefixLift 74121
  have htrace : WordTrace (prefixWord ++ tailWord_74121) baseStart_74121 baseEnd_74121 := by
    simpa [prefixWord, tailWord_74121, baseEnd_74121] using wordTrace_append hprefix tailTrace_74121
  have hstable : (prefixWord ++ tailWord_74121).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74121).length < 2 ^ (prefixWord ++ tailWord_74121).sum := by decide
  have hdescent : baseEnd_74121 < baseStart_74121 := by decide
  rcases family_descends (prefixWord ++ tailWord_74121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74243 : List Nat := [1, 1, 1, 3, 2, 1, 3, 5, 1, 4]
def baseStart_74243 : Nat := 118140960795 + 74243 * 2 ^ 59
def prefixEnd_74243 : Nat := 4983230072969 + 3 ^ 40 * 74243 * 2
def baseEnd_74243 : Nat := 25414896154572171747379

theorem tailTrace_74243 : CollatzResearch.WordTrace tailWord_74243 prefixEnd_74243 25414896154572171747379 := by
  unfold tailWord_74243
  simp only [CollatzResearch.WordTrace]
  refine ⟨2707864670037765540027383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1805243113358510360018255 2707864670037765540027383)
  ·
    refine ⟨4061797005056648310041075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2707864670037765540027383 4061797005056648310041075)
    ·
      refine ⟨6092695507584972465061613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4061797005056648310041075 6092695507584972465061613)
      ·
        refine ⟨2284760815344364674398105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6092695507584972465061613 2284760815344364674398105)
        ·
          refine ⟨1713570611508273505798579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2284760815344364674398105 1713570611508273505798579)
          ·
            refine ⟨2570355917262410258697869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1713570611508273505798579 2570355917262410258697869)
            ·
              refine ⟨963883468973403847011701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2570355917262410258697869 963883468973403847011701)
              ·
                refine ⟨90364075216256610657347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 963883468973403847011701 90364075216256610657347)
                ·
                  refine ⟨135546112824384915986021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 90364075216256610657347 135546112824384915986021)
                  ·
                    refine ⟨25414896154572171747379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 135546112824384915986021 25414896154572171747379)
                    ·
                      rfl

theorem cell22_74243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 5, 1, 4].length) (baseStart_74243 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_74243 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_74243 prefixEnd_74243 := by exact prefixLift 74243
  have htrace : WordTrace (prefixWord ++ tailWord_74243) baseStart_74243 baseEnd_74243 := by
    simpa [prefixWord, tailWord_74243, baseEnd_74243] using wordTrace_append hprefix tailTrace_74243
  have hstable : (prefixWord ++ tailWord_74243).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74243).length < 2 ^ (prefixWord ++ tailWord_74243).sum := by decide
  have hdescent : baseEnd_74243 < baseStart_74243 := by decide
  rcases family_descends (prefixWord ++ tailWord_74243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74273 : List Nat := [1, 2, 3, 2, 2, 1, 2, 3, 1, 5]
def baseStart_74273 : Nat := 118140960795 + 74273 * 2 ^ 59
def prefixEnd_74273 : Nat := 4983230072969 + 3 ^ 40 * 74273 * 2
def baseEnd_74273 : Nat := 25425165767662093497287

theorem tailTrace_74273 : CollatzResearch.WordTrace tailWord_74273 prefixEnd_74273 25425165767662093497287 := by
  unfold tailWord_74273
  simp only [CollatzResearch.WordTrace]
  refine ⟨2708958859929080663619473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1805972573286053775746315 2708958859929080663619473)
  ·
    refine ⟨2031719144946810497714605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2708958859929080663619473 2031719144946810497714605)
    ·
      refine ⟨761894679355053936642977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2031719144946810497714605 761894679355053936642977)
      ·
        refine ⟨571421009516290452482233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 761894679355053936642977 571421009516290452482233)
        ·
          refine ⟨428565757137217839361675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 571421009516290452482233 428565757137217839361675)
          ·
            refine ⟨642848635705826759042513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 428565757137217839361675 642848635705826759042513)
            ·
              refine ⟨482136476779370069281885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 642848635705826759042513 482136476779370069281885)
              ·
                refine ⟨180801178792263775980707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 482136476779370069281885 180801178792263775980707)
                ·
                  refine ⟨271201768188395663971061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 180801178792263775980707 271201768188395663971061)
                  ·
                    refine ⟨25425165767662093497287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 271201768188395663971061 25425165767662093497287)
                    ·
                      rfl

theorem cell22_74273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 3, 1, 5].length) (baseStart_74273 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_74273 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_74273 prefixEnd_74273 := by exact prefixLift 74273
  have htrace : WordTrace (prefixWord ++ tailWord_74273) baseStart_74273 baseEnd_74273 := by
    simpa [prefixWord, tailWord_74273, baseEnd_74273] using wordTrace_append hprefix tailTrace_74273
  have hstable : (prefixWord ++ tailWord_74273).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74273).length < 2 ^ (prefixWord ++ tailWord_74273).sum := by decide
  have hdescent : baseEnd_74273 < baseStart_74273 := by decide
  rcases family_descends (prefixWord ++ tailWord_74273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74288 : List Nat := [2, 1, 1, 1, 2, 3, 3, 3, 2, 4]
def baseStart_74288 : Nat := 118140960795 + 74288 * 2 ^ 59
def prefixEnd_74288 : Nat := 4983230072969 + 3 ^ 40 * 74288 * 2
def baseEnd_74288 : Nat := 25430300574207054372241

theorem tailTrace_74288 : CollatzResearch.WordTrace tailWord_74288 prefixEnd_74288 25430300574207054372241 := by
  unfold tailWord_74288
  simp only [CollatzResearch.WordTrace]
  refine ⟨1354752977437369112707759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1806337303249825483610345 1354752977437369112707759)
  ·
    refine ⟨2032129466156053669061639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1354752977437369112707759 2032129466156053669061639)
    ·
      refine ⟨3048194199234080503592459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2032129466156053669061639 3048194199234080503592459)
      ·
        refine ⟨4572291298851120755388689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3048194199234080503592459 4572291298851120755388689)
        ·
          refine ⟨3429218474138340566541517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4572291298851120755388689 3429218474138340566541517)
          ·
            refine ⟨1285956927801877712453069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3429218474138340566541517 1285956927801877712453069)
            ·
              refine ⟨482233847925704142169901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1285956927801877712453069 482233847925704142169901)
              ·
                refine ⟨180837692972139053313713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 482233847925704142169901 180837692972139053313713)
                ·
                  refine ⟨135628269729104289985285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 180837692972139053313713 135628269729104289985285)
                  ·
                    refine ⟨25430300574207054372241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 135628269729104289985285 25430300574207054372241)
                    ·
                      rfl

theorem cell22_74288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 3, 2, 4].length) (baseStart_74288 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_74288 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_74288 prefixEnd_74288 := by exact prefixLift 74288
  have htrace : WordTrace (prefixWord ++ tailWord_74288) baseStart_74288 baseEnd_74288 := by
    simpa [prefixWord, tailWord_74288, baseEnd_74288] using wordTrace_append hprefix tailTrace_74288
  have hstable : (prefixWord ++ tailWord_74288).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74288).length < 2 ^ (prefixWord ++ tailWord_74288).sum := by decide
  have hdescent : baseEnd_74288 < baseStart_74288 := by decide
  rcases family_descends (prefixWord ++ tailWord_74288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74294 : List Nat := [5, 1, 2, 1, 2, 2, 3, 1, 1, 4]
def baseStart_74294 : Nat := 118140960795 + 74294 * 2 ^ 59
def prefixEnd_74294 : Nat := 4983230072969 + 3 ^ 40 * 74294 * 2
def baseEnd_74294 : Nat := 25432354496825038722223

theorem tailTrace_74294 : CollatzResearch.WordTrace tailWord_74294 prefixEnd_74294 25432354496825038722223 := by
  unfold tailWord_74294
  simp only [CollatzResearch.WordTrace]
  refine ⟨169357799553312578133371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1806483195235334166755957 169357799553312578133371)
  ·
    refine ⟨254036699329968867200057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169357799553312578133371 254036699329968867200057)
    ·
      refine ⟨190527524497476650400043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 254036699329968867200057 190527524497476650400043)
      ·
        refine ⟨285791286746214975600065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 190527524497476650400043 285791286746214975600065)
        ·
          refine ⟨214343465059661231700049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 285791286746214975600065 214343465059661231700049)
          ·
            refine ⟨160757598794745923775037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 214343465059661231700049 160757598794745923775037)
            ·
              refine ⟨60284099548029721415639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 160757598794745923775037 60284099548029721415639)
              ·
                refine ⟨90426149322044582123459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60284099548029721415639 90426149322044582123459)
                ·
                  refine ⟨135639223983066873185189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 90426149322044582123459 135639223983066873185189)
                  ·
                    refine ⟨25432354496825038722223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 135639223983066873185189 25432354496825038722223)
                    ·
                      rfl

theorem cell22_74294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 3, 1, 1, 4].length) (baseStart_74294 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_74294 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_74294 prefixEnd_74294 := by exact prefixLift 74294
  have htrace : WordTrace (prefixWord ++ tailWord_74294) baseStart_74294 baseEnd_74294 := by
    simpa [prefixWord, tailWord_74294, baseEnd_74294] using wordTrace_append hprefix tailTrace_74294
  have hstable : (prefixWord ++ tailWord_74294).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74294).length < 2 ^ (prefixWord ++ tailWord_74294).sum := by decide
  have hdescent : baseEnd_74294 < baseStart_74294 := by decide
  rcases family_descends (prefixWord ++ tailWord_74294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74305 : List Nat := [1, 2, 5, 1, 1, 2, 2, 2, 2, 4]
def baseStart_74305 : Nat := 118140960795 + 74305 * 2 ^ 59
def prefixEnd_74305 : Nat := 4983230072969 + 3 ^ 40 * 74305 * 2
def baseEnd_74305 : Nat := 25436120021624676697189

theorem tailTrace_74305 : CollatzResearch.WordTrace tailWord_74305 prefixEnd_74305 25436120021624676697189 := by
  unfold tailWord_74305
  simp only [CollatzResearch.WordTrace]
  refine ⟨2710125995813150128784369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1806750663875433419189579 2710125995813150128784369)
  ·
    refine ⟨2032594496859862596588277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2710125995813150128784369 2032594496859862596588277)
    ·
      refine ⟨190555734080612118430151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2032594496859862596588277 190555734080612118430151)
      ·
        refine ⟨285833601120918177645227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 190555734080612118430151 285833601120918177645227)
        ·
          refine ⟨428750401681377266467841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 285833601120918177645227 428750401681377266467841)
          ·
            refine ⟨321562801261032949850881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 428750401681377266467841 321562801261032949850881)
            ·
              refine ⟨241172100945774712388161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 321562801261032949850881 241172100945774712388161)
              ·
                refine ⟨180879075709331034291121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 241172100945774712388161 180879075709331034291121)
                ·
                  refine ⟨135659306781998275718341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 180879075709331034291121 135659306781998275718341)
                  ·
                    refine ⟨25436120021624676697189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 135659306781998275718341 25436120021624676697189)
                    ·
                      rfl

theorem cell22_74305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 2, 2, 2, 4].length) (baseStart_74305 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_74305 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_74305 prefixEnd_74305 := by exact prefixLift 74305
  have htrace : WordTrace (prefixWord ++ tailWord_74305) baseStart_74305 baseEnd_74305 := by
    simpa [prefixWord, tailWord_74305, baseEnd_74305] using wordTrace_append hprefix tailTrace_74305
  have hstable : (prefixWord ++ tailWord_74305).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74305).length < 2 ^ (prefixWord ++ tailWord_74305).sum := by decide
  have hdescent : baseEnd_74305 < baseStart_74305 := by decide
  rcases family_descends (prefixWord ++ tailWord_74305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74365 : List Nat := [1, 4, 1, 1, 5, 1, 1, 1, 7]
def baseStart_74365 : Nat := 118140960795 + 74365 * 2 ^ 59
def prefixEnd_74365 : Nat := 4983230072969 + 3 ^ 40 * 74365 * 2
def baseEnd_74365 : Nat := 8485553082601506732335

theorem tailTrace_74365 : CollatzResearch.WordTrace tailWord_74365 prefixEnd_74365 8485553082601506732335 := by
  unfold tailWord_74365
  simp only [CollatzResearch.WordTrace]
  refine ⟨2712314375595780375968549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1808209583730520250645699 2712314375595780375968549)
  ·
    refine ⟨508558945424208820494103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2712314375595780375968549 508558945424208820494103)
    ·
      refine ⟨762838418136313230741155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 508558945424208820494103 762838418136313230741155)
      ·
        refine ⟨1144257627204469846111733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 762838418136313230741155 1144257627204469846111733)
        ·
          refine ⟨107274152550419048072975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1144257627204469846111733 107274152550419048072975)
          ·
            refine ⟨160911228825628572109463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107274152550419048072975 160911228825628572109463)
            ·
              refine ⟨241366843238442858164195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 160911228825628572109463 241366843238442858164195)
              ·
                refine ⟨362050264857664287246293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 241366843238442858164195 362050264857664287246293)
                ·
                  refine ⟨8485553082601506732335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 362050264857664287246293 8485553082601506732335)
                  ·
                    rfl

theorem cell22_74365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 1, 1, 7].length) (baseStart_74365 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_74365 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_74365 prefixEnd_74365 := by exact prefixLift 74365
  have htrace : WordTrace (prefixWord ++ tailWord_74365) baseStart_74365 baseEnd_74365 := by
    simpa [prefixWord, tailWord_74365, baseEnd_74365] using wordTrace_append hprefix tailTrace_74365
  have hstable : (prefixWord ++ tailWord_74365).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74365).length < 2 ^ (prefixWord ++ tailWord_74365).sum := by decide
  have hdescent : baseEnd_74365 < baseStart_74365 := by decide
  rcases family_descends (prefixWord ++ tailWord_74365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74382 : List Nat := [4, 1, 1, 3, 1, 1, 5, 1, 5]
def baseStart_74382 : Nat := 118140960795 + 74382 * 2 ^ 59
def prefixEnd_74382 : Nat := 4983230072969 + 3 ^ 40 * 74382 * 2
def baseEnd_74382 : Nat := 8487492898407380840651

theorem tailTrace_74382 : CollatzResearch.WordTrace tailWord_74382 prefixEnd_74382 8487492898407380840651 := by
  unfold tailWord_74382
  simp only [CollatzResearch.WordTrace]
  refine ⟨339116802066774034917175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1808622944356128186224933 339116802066774034917175)
  ·
    refine ⟨508675203100161052375763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 339116802066774034917175 508675203100161052375763)
    ·
      refine ⟨763012804650241578563645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 508675203100161052375763 763012804650241578563645)
      ·
        refine ⟨286129801743840591961367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 763012804650241578563645 286129801743840591961367)
        ·
          refine ⟨429194702615760887942051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 286129801743840591961367 429194702615760887942051)
          ·
            refine ⟨643792053923641331913077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 429194702615760887942051 643792053923641331913077)
            ·
              refine ⟨60355505055341374866851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 643792053923641331913077 60355505055341374866851)
              ·
                refine ⟨90533257583012062300277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60355505055341374866851 90533257583012062300277)
                ·
                  refine ⟨8487492898407380840651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 90533257583012062300277 8487492898407380840651)
                  ·
                    rfl

theorem cell22_74382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 5, 1, 5].length) (baseStart_74382 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_74382 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_74382 prefixEnd_74382 := by exact prefixLift 74382
  have htrace : WordTrace (prefixWord ++ tailWord_74382) baseStart_74382 baseEnd_74382 := by
    simpa [prefixWord, tailWord_74382, baseEnd_74382] using wordTrace_append hprefix tailTrace_74382
  have hstable : (prefixWord ++ tailWord_74382).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74382).length < 2 ^ (prefixWord ++ tailWord_74382).sum := by decide
  have hdescent : baseEnd_74382 < baseStart_74382 := by decide
  rcases family_descends (prefixWord ++ tailWord_74382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74393 : List Nat := [1, 2, 1, 2, 1, 2, 3, 4, 6]
def baseStart_74393 : Nat := 118140960795 + 74393 * 2 ^ 59
def prefixEnd_74393 : Nat := 4983230072969 + 3 ^ 40 * 74393 * 2
def baseEnd_74393 : Nat := 8488748073340593498973

theorem tailTrace_74393 : CollatzResearch.WordTrace tailWord_74393 prefixEnd_74393 8488748073340593498973 := by
  unfold tailWord_74393
  simp only [CollatzResearch.WordTrace]
  refine ⟨2713335619494341157987833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1808890412996227438658555 2713335619494341157987833)
  ·
    refine ⟨2035001714620755868490875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2713335619494341157987833 2035001714620755868490875)
    ·
      refine ⟨3052502571931133802736313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2035001714620755868490875 3052502571931133802736313)
      ·
        refine ⟨2289376928948350352052235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3052502571931133802736313 2289376928948350352052235)
        ·
          refine ⟨3434065393422525528078353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2289376928948350352052235 3434065393422525528078353)
          ·
            refine ⟨2575549045066894146058765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3434065393422525528078353 2575549045066894146058765)
            ·
              refine ⟨965830891900085304772037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2575549045066894146058765 965830891900085304772037)
              ·
                refine ⟨181093292231265994644757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 965830891900085304772037 181093292231265994644757)
                ·
                  refine ⟨8488748073340593498973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 181093292231265994644757 8488748073340593498973)
                  ·
                    rfl

theorem cell22_74393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 4, 6].length) (baseStart_74393 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_74393 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_74393 prefixEnd_74393 := by exact prefixLift 74393
  have htrace : WordTrace (prefixWord ++ tailWord_74393) baseStart_74393 baseEnd_74393 := by
    simpa [prefixWord, tailWord_74393, baseEnd_74393] using wordTrace_append hprefix tailTrace_74393
  have hstable : (prefixWord ++ tailWord_74393).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74393).length < 2 ^ (prefixWord ++ tailWord_74393).sum := by decide
  have hdescent : baseEnd_74393 < baseStart_74393 := by decide
  rcases family_descends (prefixWord ++ tailWord_74393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74433 : List Nat := [1, 2, 6, 2, 2, 1, 2, 1, 5]
def baseStart_74433 : Nat := 118140960795 + 74433 * 2 ^ 59
def prefixEnd_74433 : Nat := 4983230072969 + 3 ^ 40 * 74433 * 2
def baseEnd_74433 : Nat := 8493312345825003165599

theorem tailTrace_74433 : CollatzResearch.WordTrace tailWord_74433 prefixEnd_74433 8493312345825003165599 := by
  unfold tailWord_74433
  simp only [CollatzResearch.WordTrace]
  refine ⟨2714794539349427989443953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1809863026232951992962635 2714794539349427989443953)
  ·
    refine ⟨2036095904512070992082965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2714794539349427989443953 2036095904512070992082965)
    ·
      refine ⟨95441995524003327753889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 2036095904512070992082965 95441995524003327753889)
      ·
        refine ⟨71581496643002495815417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95441995524003327753889 71581496643002495815417)
        ·
          refine ⟨53686122482251871861563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71581496643002495815417 53686122482251871861563)
          ·
            refine ⟨80529183723377807792345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53686122482251871861563 80529183723377807792345)
            ·
              refine ⟨60396887792533355844259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 80529183723377807792345 60396887792533355844259)
              ·
                refine ⟨90595331688800033766389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60396887792533355844259 90595331688800033766389)
                ·
                  refine ⟨8493312345825003165599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 90595331688800033766389 8493312345825003165599)
                  ·
                    rfl

theorem cell22_74433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 1, 2, 1, 5].length) (baseStart_74433 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_74433 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_74433 prefixEnd_74433 := by exact prefixLift 74433
  have htrace : WordTrace (prefixWord ++ tailWord_74433) baseStart_74433 baseEnd_74433 := by
    simpa [prefixWord, tailWord_74433, baseEnd_74433] using wordTrace_append hprefix tailTrace_74433
  have hstable : (prefixWord ++ tailWord_74433).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74433).length < 2 ^ (prefixWord ++ tailWord_74433).sum := by decide
  have hdescent : baseEnd_74433 < baseStart_74433 := by decide
  rcases family_descends (prefixWord ++ tailWord_74433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74575 : List Nat := [1, 1, 2, 1, 1, 2, 1, 1, 8, 4]
def baseStart_74575 : Nat := 118140960795 + 74575 * 2 ^ 59
def prefixEnd_74575 : Nat := 4983230072969 + 3 ^ 40 * 74575 * 2
def baseEnd_74575 : Nat := 25528546539433972446361

theorem tailTrace_74575 : CollatzResearch.WordTrace tailWord_74575 prefixEnd_74575 25528546539433972446361 := by
  unfold tailWord_74575
  simp only [CollatzResearch.WordTrace]
  refine ⟨2719973704834986241113179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1813315803223324160742119 2719973704834986241113179)
  ·
    refine ⟨4079960557252479361669769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2719973704834986241113179 4079960557252479361669769)
    ·
      refine ⟨3059970417939359521252327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4079960557252479361669769 3059970417939359521252327)
      ·
        refine ⟨4589955626909039281878491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3059970417939359521252327 4589955626909039281878491)
        ·
          refine ⟨6884933440363558922817737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4589955626909039281878491 6884933440363558922817737)
          ·
            refine ⟨5163700080272669192113303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6884933440363558922817737 5163700080272669192113303)
            ·
              refine ⟨7745550120409003788169955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5163700080272669192113303 7745550120409003788169955)
              ·
                refine ⟨11618325180613505682254933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7745550120409003788169955 11618325180613505682254933)
                ·
                  refine ⟨136152248210314519713925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 11618325180613505682254933 136152248210314519713925)
                  ·
                    refine ⟨25528546539433972446361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 136152248210314519713925 25528546539433972446361)
                    ·
                      rfl

theorem cell22_74575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 8, 4].length) (baseStart_74575 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_74575 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_74575 prefixEnd_74575 := by exact prefixLift 74575
  have htrace : WordTrace (prefixWord ++ tailWord_74575) baseStart_74575 baseEnd_74575 := by
    simpa [prefixWord, tailWord_74575, baseEnd_74575] using wordTrace_append hprefix tailTrace_74575
  have hstable : (prefixWord ++ tailWord_74575).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74575).length < 2 ^ (prefixWord ++ tailWord_74575).sum := by decide
  have hdescent : baseEnd_74575 < baseStart_74575 := by decide
  rcases family_descends (prefixWord ++ tailWord_74575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74592 : List Nat := [2, 1, 1, 3, 3, 1, 3, 2, 2, 4]
def baseStart_74592 : Nat := 118140960795 + 74592 * 2 ^ 59
def prefixEnd_74592 : Nat := 4983230072969 + 3 ^ 40 * 74592 * 2
def baseEnd_74592 : Nat := 25534365986851594771309

theorem tailTrace_74592 : CollatzResearch.WordTrace tailWord_74592 prefixEnd_74592 25534365986851594771309 := by
  unfold tailWord_74592
  simp only [CollatzResearch.WordTrace]
  refine ⟨1360296872886699072241015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1813729163848932096321353 1360296872886699072241015)
  ·
    refine ⟨2040445309330048608361523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1360296872886699072241015 2040445309330048608361523)
    ·
      refine ⟨3060667963995072912542285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2040445309330048608361523 3060667963995072912542285)
      ·
        refine ⟨1147750486498152342203357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3060667963995072912542285 1147750486498152342203357)
        ·
          refine ⟨430406432436807128326259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1147750486498152342203357 430406432436807128326259)
          ·
            refine ⟨645609648655210692489389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 430406432436807128326259 645609648655210692489389)
            ·
              refine ⟨242103618245704009683521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 645609648655210692489389 242103618245704009683521)
              ·
                refine ⟨181577713684278007262641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 242103618245704009683521 181577713684278007262641)
                ·
                  refine ⟨136183285263208505446981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 181577713684278007262641 136183285263208505446981)
                  ·
                    refine ⟨25534365986851594771309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 136183285263208505446981 25534365986851594771309)
                    ·
                      rfl

theorem cell22_74592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 3, 2, 2, 4].length) (baseStart_74592 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_74592 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_74592 prefixEnd_74592 := by exact prefixLift 74592
  have htrace : WordTrace (prefixWord ++ tailWord_74592) baseStart_74592 baseEnd_74592 := by
    simpa [prefixWord, tailWord_74592, baseEnd_74592] using wordTrace_append hprefix tailTrace_74592
  have hstable : (prefixWord ++ tailWord_74592).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74592).length < 2 ^ (prefixWord ++ tailWord_74592).sum := by decide
  have hdescent : baseEnd_74592 < baseStart_74592 := by decide
  rcases family_descends (prefixWord ++ tailWord_74592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74596 : List Nat := [2, 3, 1, 1, 4, 2, 3, 2, 4]
def baseStart_74596 : Nat := 118140960795 + 74596 * 2 ^ 59
def prefixEnd_74596 : Nat := 4983230072969 + 3 ^ 40 * 74596 * 2
def baseEnd_74596 : Nat := 8511911756198972557099

theorem tailTrace_74596 : CollatzResearch.WordTrace tailWord_74596 prefixEnd_74596 8511911756198972557099 := by
  unfold tailWord_74596
  simp only [CollatzResearch.WordTrace]
  refine ⟨1360369818879453413813821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1813826425172604551751761 1360369818879453413813821)
  ·
    refine ⟨510138682079795030180183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1360369818879453413813821 510138682079795030180183)
    ·
      refine ⟨765208023119692545270275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 510138682079795030180183 765208023119692545270275)
      ·
        refine ⟨1147812034679538817905413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 765208023119692545270275 1147812034679538817905413)
        ·
          refine ⟨215214756502413528357265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1147812034679538817905413 215214756502413528357265)
          ·
            refine ⟨161411067376810146267949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 215214756502413528357265 161411067376810146267949)
            ·
              refine ⟨60529150266303804850481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 161411067376810146267949 60529150266303804850481)
              ·
                refine ⟨45396862699727853637861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60529150266303804850481 45396862699727853637861)
                ·
                  refine ⟨8511911756198972557099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 45396862699727853637861 8511911756198972557099)
                  ·
                    rfl

theorem cell22_74596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 3, 2, 4].length) (baseStart_74596 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_74596 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_74596 prefixEnd_74596 := by exact prefixLift 74596
  have htrace : WordTrace (prefixWord ++ tailWord_74596) baseStart_74596 baseEnd_74596 := by
    simpa [prefixWord, tailWord_74596, baseEnd_74596] using wordTrace_append hprefix tailTrace_74596
  have hstable : (prefixWord ++ tailWord_74596).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74596).length < 2 ^ (prefixWord ++ tailWord_74596).sum := by decide
  have hdescent : baseEnd_74596 < baseStart_74596 := by decide
  rcases family_descends (prefixWord ++ tailWord_74596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74635 : List Nat := [1, 1, 1, 1, 4, 2, 2, 1, 9]
def baseStart_74635 : Nat := 118140960795 + 74635 * 2 ^ 59
def prefixEnd_74635 : Nat := 4983230072969 + 3 ^ 40 * 74635 * 2
def baseEnd_74635 : Nat := 8516361921871271982059

theorem tailTrace_74635 : CollatzResearch.WordTrace tailWord_74635 prefixEnd_74635 8516361921871271982059 := by
  unfold tailWord_74635
  simp only [CollatzResearch.WordTrace]
  refine ⟨2722162084617616488297359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1814774723078410992198239 2722162084617616488297359)
  ·
    refine ⟨4083243126926424732446039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2722162084617616488297359 4083243126926424732446039)
    ·
      refine ⟨6124864690389637098669059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4083243126926424732446039 6124864690389637098669059)
      ·
        refine ⟨9187297035584455648003589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6124864690389637098669059 9187297035584455648003589)
        ·
          refine ⟨1722618194172085434000673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9187297035584455648003589 1722618194172085434000673)
          ·
            refine ⟨1291963645629064075500505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1722618194172085434000673 1291963645629064075500505)
            ·
              refine ⟨968972734221798056625379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1291963645629064075500505 968972734221798056625379)
              ·
                refine ⟨1453459101332697084938069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 968972734221798056625379 1453459101332697084938069)
                ·
                  refine ⟨8516361921871271982059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 1453459101332697084938069 8516361921871271982059)
                  ·
                    rfl

theorem cell22_74635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 1, 9].length) (baseStart_74635 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_74635 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_74635 prefixEnd_74635 := by exact prefixLift 74635
  have htrace : WordTrace (prefixWord ++ tailWord_74635) baseStart_74635 baseEnd_74635 := by
    simpa [prefixWord, tailWord_74635, baseEnd_74635] using wordTrace_append hprefix tailTrace_74635
  have hstable : (prefixWord ++ tailWord_74635).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74635).length < 2 ^ (prefixWord ++ tailWord_74635).sum := by decide
  have hdescent : baseEnd_74635 < baseStart_74635 := by decide
  rcases family_descends (prefixWord ++ tailWord_74635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74682 : List Nat := [3, 1, 1, 1, 2, 1, 3, 3, 3, 4]
def baseStart_74682 : Nat := 118140960795 + 74682 * 2 ^ 59
def prefixEnd_74682 : Nat := 4983230072969 + 3 ^ 40 * 74682 * 2
def baseEnd_74682 : Nat := 25565174826121360021033

theorem tailTrace_74682 : CollatzResearch.WordTrace tailWord_74682 prefixEnd_74682 25565174826121360021033 := by
  unfold tailWord_74682
  simp only [CollatzResearch.WordTrace]
  refine ⟨680969078861835878814575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1815917543631562343505533 680969078861835878814575)
  ·
    refine ⟨1021453618292753818221863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 680969078861835878814575 1021453618292753818221863)
    ·
      refine ⟨1532180427439130727332795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1021453618292753818221863 1532180427439130727332795)
      ·
        refine ⟨2298270641158696090999193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1532180427439130727332795 2298270641158696090999193)
        ·
          refine ⟨1723702980869022068249395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2298270641158696090999193 1723702980869022068249395)
          ·
            refine ⟨2585554471303533102374093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1723702980869022068249395 2585554471303533102374093)
            ·
              refine ⟨969582926738824913390285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2585554471303533102374093 969582926738824913390285)
              ·
                refine ⟨363593597527059342521357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 969582926738824913390285 363593597527059342521357)
                ·
                  refine ⟨136347599072647253445509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 363593597527059342521357 136347599072647253445509)
                  ·
                    refine ⟨25565174826121360021033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 136347599072647253445509 25565174826121360021033)
                    ·
                      rfl

theorem cell22_74682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 3, 3, 4].length) (baseStart_74682 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_74682 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_74682 prefixEnd_74682 := by exact prefixLift 74682
  have htrace : WordTrace (prefixWord ++ tailWord_74682) baseStart_74682 baseEnd_74682 := by
    simpa [prefixWord, tailWord_74682, baseEnd_74682] using wordTrace_append hprefix tailTrace_74682
  have hstable : (prefixWord ++ tailWord_74682).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74682).length < 2 ^ (prefixWord ++ tailWord_74682).sum := by decide
  have hdescent : baseEnd_74682 < baseStart_74682 := by decide
  rcases family_descends (prefixWord ++ tailWord_74682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74699 : List Nat := [1, 1, 1, 1, 3, 6, 1, 3, 1, 4]
def baseStart_74699 : Nat := 118140960795 + 74699 * 2 ^ 59
def prefixEnd_74699 : Nat := 4983230072969 + 3 ^ 40 * 74699 * 2
def baseEnd_74699 : Nat := 25570994273538982345981

theorem tailTrace_74699 : CollatzResearch.WordTrace tailWord_74699 prefixEnd_74699 25570994273538982345981 := by
  unfold tailWord_74699
  simp only [CollatzResearch.WordTrace]
  refine ⟨2724496356385755418627151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1816330904257170279084767 2724496356385755418627151)
  ·
    refine ⟨4086744534578633127940727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2724496356385755418627151 4086744534578633127940727)
    ·
      refine ⟨6130116801867949691911091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4086744534578633127940727 6130116801867949691911091)
      ·
        refine ⟨9195175202801924537866637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6130116801867949691911091 9195175202801924537866637)
        ·
          refine ⟨3448190701050721701699989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9195175202801924537866637 3448190701050721701699989)
          ·
            refine ⟨161633939111752579767187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 3448190701050721701699989 161633939111752579767187)
            ·
              refine ⟨242450908667628869650781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 161633939111752579767187 242450908667628869650781)
              ·
                refine ⟨90919090750360826119043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 242450908667628869650781 90919090750360826119043)
                ·
                  refine ⟨136378636125541239178565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 90919090750360826119043 136378636125541239178565)
                  ·
                    refine ⟨25570994273538982345981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 136378636125541239178565 25570994273538982345981)
                    ·
                      rfl

theorem cell22_74699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 1, 3, 1, 4].length) (baseStart_74699 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_74699 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_74699 prefixEnd_74699 := by exact prefixLift 74699
  have htrace : WordTrace (prefixWord ++ tailWord_74699) baseStart_74699 baseEnd_74699 := by
    simpa [prefixWord, tailWord_74699, baseEnd_74699] using wordTrace_append hprefix tailTrace_74699
  have hstable : (prefixWord ++ tailWord_74699).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74699).length < 2 ^ (prefixWord ++ tailWord_74699).sum := by decide
  have hdescent : baseEnd_74699 < baseStart_74699 := by decide
  rcases family_descends (prefixWord ++ tailWord_74699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74714 : List Nat := [3, 1, 1, 2, 4, 2, 2, 1, 6]
def baseStart_74714 : Nat := 118140960795 + 74714 * 2 ^ 59
def prefixEnd_74714 : Nat := 4983230072969 + 3 ^ 40 * 74714 * 2
def baseEnd_74714 : Nat := 8525376360027981073645

theorem tailTrace_74714 : CollatzResearch.WordTrace tailWord_74714 prefixEnd_74714 8525376360027981073645 := by
  unfold tailWord_74714
  simp only [CollatzResearch.WordTrace]
  refine ⟨681260862832853245105799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1816695634220941986948797 681260862832853245105799)
  ·
    refine ⟨1021891294249279867658699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 681260862832853245105799 1021891294249279867658699)
    ·
      refine ⟨1532836941373919801488049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1021891294249279867658699 1532836941373919801488049)
      ·
        refine ⟨1149627706030439851116037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1532836941373919801488049 1149627706030439851116037)
        ·
          refine ⟨215555194880707472084257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1149627706030439851116037 215555194880707472084257)
          ·
            refine ⟨161666396160530604063193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 215555194880707472084257 161666396160530604063193)
            ·
              refine ⟨121249797120397953047395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 161666396160530604063193 121249797120397953047395)
              ·
                refine ⟨181874695680596929571093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 121249797120397953047395 181874695680596929571093)
                ·
                  refine ⟨8525376360027981073645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 181874695680596929571093 8525376360027981073645)
                  ·
                    rfl

theorem cell22_74714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 2, 1, 6].length) (baseStart_74714 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_74714 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_74714 prefixEnd_74714 := by exact prefixLift 74714
  have htrace : WordTrace (prefixWord ++ tailWord_74714) baseStart_74714 baseEnd_74714 := by
    simpa [prefixWord, tailWord_74714, baseEnd_74714] using wordTrace_append hprefix tailTrace_74714
  have hstable : (prefixWord ++ tailWord_74714).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74714).length < 2 ^ (prefixWord ++ tailWord_74714).sum := by decide
  have hdescent : baseEnd_74714 < baseStart_74714 := by decide
  rcases family_descends (prefixWord ++ tailWord_74714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74780 : List Nat := [2, 2, 3, 1, 4, 2, 2, 1, 2, 3]
def baseStart_74780 : Nat := 118140960795 + 74780 * 2 ^ 59
def prefixEnd_74780 : Nat := 4983230072969 + 3 ^ 40 * 74780 * 2
def baseEnd_74780 : Nat := 25598722228881771070733

theorem tailTrace_74780 : CollatzResearch.WordTrace tailWord_74780 prefixEnd_74780 25598722228881771070733 := by
  unfold tailWord_74780
  simp only [CollatzResearch.WordTrace]
  refine ⟨1363725334546153126162897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1818300446061537501550529 1363725334546153126162897)
  ·
    refine ⟨1022794000909614844622173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1363725334546153126162897 1022794000909614844622173)
    ·
      refine ⟨383547750341105566733315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1022794000909614844622173 383547750341105566733315)
      ·
        refine ⟨575321625511658350099973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 383547750341105566733315 575321625511658350099973)
        ·
          refine ⟨107872804783435940643745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 575321625511658350099973 107872804783435940643745)
          ·
            refine ⟨80904603587576955482809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 107872804783435940643745 80904603587576955482809)
            ·
              refine ⟨60678452690682716612107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 80904603587576955482809 60678452690682716612107)
              ·
                refine ⟨91017679036024074918161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60678452690682716612107 91017679036024074918161)
                ·
                  refine ⟨68263259277018056188621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 91017679036024074918161 68263259277018056188621)
                  ·
                    refine ⟨25598722228881771070733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 68263259277018056188621 25598722228881771070733)
                    ·
                      rfl

theorem cell22_74780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 2, 2, 1, 2, 3].length) (baseStart_74780 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_74780 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_74780 prefixEnd_74780 := by exact prefixLift 74780
  have htrace : WordTrace (prefixWord ++ tailWord_74780) baseStart_74780 baseEnd_74780 := by
    simpa [prefixWord, tailWord_74780, baseEnd_74780] using wordTrace_append hprefix tailTrace_74780
  have hstable : (prefixWord ++ tailWord_74780).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74780).length < 2 ^ (prefixWord ++ tailWord_74780).sum := by decide
  have hdescent : baseEnd_74780 < baseStart_74780 := by decide
  rcases family_descends (prefixWord ++ tailWord_74780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74832 : List Nat := [2, 1, 1, 1, 1, 3, 1, 2, 10]
def baseStart_74832 : Nat := 118140960795 + 74832 * 2 ^ 59
def prefixEnd_74832 : Nat := 4983230072969 + 3 ^ 40 * 74832 * 2
def baseEnd_74832 : Nat := 8538840963856989590191

theorem tailTrace_74832 : CollatzResearch.WordTrace tailWord_74832 prefixEnd_74832 8538840963856989590191 := by
  unfold tailWord_74832
  simp only [CollatzResearch.WordTrace]
  refine ⟨1364673632451959566609375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1819564843269279422145833 1364673632451959566609375)
  ·
    refine ⟨2047010448677939349914063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1364673632451959566609375 2047010448677939349914063)
    ·
      refine ⟨3070515673016909024871095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2047010448677939349914063 3070515673016909024871095)
      ·
        refine ⟨4605773509525363537306643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3070515673016909024871095 4605773509525363537306643)
        ·
          refine ⟨6908660264288045305959965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4605773509525363537306643 6908660264288045305959965)
          ·
            refine ⟨2590747599108016989734987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6908660264288045305959965 2590747599108016989734987)
            ·
              refine ⟨3886121398662025484602481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2590747599108016989734987 3886121398662025484602481)
              ·
                refine ⟨2914591048996519113451861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3886121398662025484602481 2914591048996519113451861)
                ·
                  refine ⟨8538840963856989590191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 2914591048996519113451861 8538840963856989590191)
                  ·
                    rfl

theorem cell22_74832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 2, 10].length) (baseStart_74832 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_74832 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_74832 prefixEnd_74832 := by exact prefixLift 74832
  have htrace : WordTrace (prefixWord ++ tailWord_74832) baseStart_74832 baseEnd_74832 := by
    simpa [prefixWord, tailWord_74832, baseEnd_74832] using wordTrace_append hprefix tailTrace_74832
  have hstable : (prefixWord ++ tailWord_74832).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74832).length < 2 ^ (prefixWord ++ tailWord_74832).sum := by decide
  have hdescent : baseEnd_74832 < baseStart_74832 := by decide
  rcases family_descends (prefixWord ++ tailWord_74832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74864 : List Nat := [2, 1, 1, 1, 5, 1, 1, 4, 1, 5]
def baseStart_74864 : Nat := 118140960795 + 74864 * 2 ^ 59
def prefixEnd_74864 : Nat := 4983230072969 + 3 ^ 40 * 74864 * 2
def baseEnd_74864 : Nat := 25627477145533551970475

theorem tailTrace_74864 : CollatzResearch.WordTrace tailWord_74864 prefixEnd_74864 25627477145533551970475 := by
  unfold tailWord_74864
  simp only [CollatzResearch.WordTrace]
  refine ⟨1365257200393994299191823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1820342933858659065589097 1365257200393994299191823)
  ·
    refine ⟨2047885800590991448787735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1365257200393994299191823 2047885800590991448787735)
    ·
      refine ⟨3071828700886487173181603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2047885800590991448787735 3071828700886487173181603)
      ·
        refine ⟨4607743051329730759772405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3071828700886487173181603 4607743051329730759772405)
        ·
          refine ⟨431975911062162258728663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4607743051329730759772405 431975911062162258728663)
          ·
            refine ⟨647963866593243388092995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 431975911062162258728663 647963866593243388092995)
            ·
              refine ⟨971945799889865082139493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 647963866593243388092995 971945799889865082139493)
              ·
                refine ⟨182239837479349702901155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 971945799889865082139493 182239837479349702901155)
                ·
                  refine ⟨273359756219024554351733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 182239837479349702901155 273359756219024554351733)
                  ·
                    refine ⟨25627477145533551970475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 273359756219024554351733 25627477145533551970475)
                    ·
                      rfl

theorem cell22_74864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 4, 1, 5].length) (baseStart_74864 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_74864 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_74864 prefixEnd_74864 := by exact prefixLift 74864
  have htrace : WordTrace (prefixWord ++ tailWord_74864) baseStart_74864 baseEnd_74864 := by
    simpa [prefixWord, tailWord_74864, baseEnd_74864] using wordTrace_append hprefix tailTrace_74864
  have hstable : (prefixWord ++ tailWord_74864).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74864).length < 2 ^ (prefixWord ++ tailWord_74864).sum := by decide
  have hdescent : baseEnd_74864 < baseStart_74864 := by decide
  rcases family_descends (prefixWord ++ tailWord_74864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74898 : List Nat := [3, 2, 3, 1, 1, 4, 1, 1, 1, 5]
def baseStart_74898 : Nat := 118140960795 + 74898 * 2 ^ 59
def prefixEnd_74898 : Nat := 4983230072969 + 3 ^ 40 * 74898 * 2
def baseEnd_74898 : Nat := 25639116040368796620371

theorem tailTrace_74898 : CollatzResearch.WordTrace tailWord_74898 prefixEnd_74898 25639116040368796620371 := by
  unfold tailWord_74898
  simp only [CollatzResearch.WordTrace]
  refine ⟨682938620666203101280337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1821169655109874936747565 682938620666203101280337)
  ·
    refine ⟨512203965499652325960253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 682938620666203101280337 512203965499652325960253)
    ·
      refine ⟨192076487062369622235095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 512203965499652325960253 192076487062369622235095)
      ·
        refine ⟨288114730593554433352643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 192076487062369622235095 288114730593554433352643)
        ·
          refine ⟨432172095890331650028965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 288114730593554433352643 432172095890331650028965)
          ·
            refine ⟨81032267979437184380431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 432172095890331650028965 81032267979437184380431)
            ·
              refine ⟨121548401969155776570647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81032267979437184380431 121548401969155776570647)
              ·
                refine ⟨182322602953733664855971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 121548401969155776570647 182322602953733664855971)
                ·
                  refine ⟨273483904430600497283957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 182322602953733664855971 273483904430600497283957)
                  ·
                    refine ⟨25639116040368796620371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 273483904430600497283957 25639116040368796620371)
                    ·
                      rfl

theorem cell22_74898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 4, 1, 1, 1, 5].length) (baseStart_74898 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_74898 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_74898 prefixEnd_74898 := by exact prefixLift 74898
  have htrace : WordTrace (prefixWord ++ tailWord_74898) baseStart_74898 baseEnd_74898 := by
    simpa [prefixWord, tailWord_74898, baseEnd_74898] using wordTrace_append hprefix tailTrace_74898
  have hstable : (prefixWord ++ tailWord_74898).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74898).length < 2 ^ (prefixWord ++ tailWord_74898).sum := by decide
  have hdescent : baseEnd_74898 < baseStart_74898 := by decide
  rcases family_descends (prefixWord ++ tailWord_74898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74909 : List Nat := [1, 4, 2, 1, 1, 2, 1, 1, 2, 7]
def baseStart_74909 : Nat := 118140960795 + 74909 * 2 ^ 59
def prefixEnd_74909 : Nat := 4983230072969 + 3 ^ 40 * 74909 * 2
def baseEnd_74909 : Nat := 25642881565168434595337

theorem tailTrace_74909 : CollatzResearch.WordTrace tailWord_74909 prefixEnd_74909 25642881565168434595337 := by
  unfold tailWord_74909
  simp only [CollatzResearch.WordTrace]
  refine ⟨2732155685624961283771781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1821437123749974189181187 2732155685624961283771781)
  ·
    refine ⟨512279191054680240707209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2732155685624961283771781 512279191054680240707209)
    ·
      refine ⟨384209393291010180530407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 512279191054680240707209 384209393291010180530407)
      ·
        refine ⟨576314089936515270795611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 384209393291010180530407 576314089936515270795611)
        ·
          refine ⟨864471134904772906193417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 576314089936515270795611 864471134904772906193417)
          ·
            refine ⟨648353351178579679645063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 864471134904772906193417 648353351178579679645063)
            ·
              refine ⟨972530026767869519467595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 648353351178579679645063 972530026767869519467595)
              ·
                refine ⟨1458795040151804279201393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 972530026767869519467595 1458795040151804279201393)
                ·
                  refine ⟨1094096280113853209401045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1458795040151804279201393 1094096280113853209401045)
                  ·
                    refine ⟨25642881565168434595337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1094096280113853209401045 25642881565168434595337)
                    ·
                      rfl

theorem cell22_74909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 1, 2, 7].length) (baseStart_74909 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_74909 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_74909 prefixEnd_74909 := by exact prefixLift 74909
  have htrace : WordTrace (prefixWord ++ tailWord_74909) baseStart_74909 baseEnd_74909 := by
    simpa [prefixWord, tailWord_74909, baseEnd_74909] using wordTrace_append hprefix tailTrace_74909
  have hstable : (prefixWord ++ tailWord_74909).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74909).length < 2 ^ (prefixWord ++ tailWord_74909).sum := by decide
  have hdescent : baseEnd_74909 < baseStart_74909 := by decide
  rcases family_descends (prefixWord ++ tailWord_74909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74911 : List Nat := [1, 1, 2, 6, 2, 1, 1, 8]
def baseStart_74911 : Nat := 118140960795 + 74911 * 2 ^ 59
def prefixEnd_74911 : Nat := 4983230072969 + 3 ^ 40 * 74911 * 2
def baseEnd_74911 : Nat := 2849285134004566227259

theorem tailTrace_74911 : CollatzResearch.WordTrace tailWord_74911 prefixEnd_74911 2849285134004566227259 := by
  unfold tailWord_74911
  simp only [CollatzResearch.WordTrace]
  refine ⟨2732228631617715625344587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1821485754411810416896391 2732228631617715625344587)
  ·
    refine ⟨4098342947426573438016881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2732228631617715625344587 4098342947426573438016881)
    ·
      refine ⟨3073757210569930078512661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4098342947426573438016881 3073757210569930078512661)
      ·
        refine ⟨144082369245465472430281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 3073757210569930078512661 144082369245465472430281)
        ·
          refine ⟨108061776934099104322711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 144082369245465472430281 108061776934099104322711)
          ·
            refine ⟨162092665401148656484067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108061776934099104322711 162092665401148656484067)
            ·
              refine ⟨243138998101722984726101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 162092665401148656484067 243138998101722984726101)
              ·
                refine ⟨2849285134004566227259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 243138998101722984726101 2849285134004566227259)
                ·
                  rfl

theorem cell22_74911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 1, 8].length) (baseStart_74911 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_74911 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_74911 prefixEnd_74911 := by exact prefixLift 74911
  have htrace : WordTrace (prefixWord ++ tailWord_74911) baseStart_74911 baseEnd_74911 := by
    simpa [prefixWord, tailWord_74911, baseEnd_74911] using wordTrace_append hprefix tailTrace_74911
  have hstable : (prefixWord ++ tailWord_74911).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74911).length < 2 ^ (prefixWord ++ tailWord_74911).sum := by decide
  have hdescent : baseEnd_74911 < baseStart_74911 := by decide
  rcases family_descends (prefixWord ++ tailWord_74911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74934 : List Nat := [5, 1, 3, 2, 1, 1, 3, 2, 4]
def baseStart_74934 : Nat := 118140960795 + 74934 * 2 ^ 59
def prefixEnd_74934 : Nat := 4983230072969 + 3 ^ 40 * 74934 * 2
def baseEnd_74934 : Nat := 8550479858692234240087

theorem tailTrace_74934 : CollatzResearch.WordTrace tailWord_74934 prefixEnd_74934 8550479858692234240087 := by
  unfold tailWord_74934
  simp only [CollatzResearch.WordTrace]
  refine ⟨170816719408399409589491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1822045007022927035621237 170816719408399409589491)
  ·
    refine ⟨256225079112599114384237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170816719408399409589491 256225079112599114384237)
    ·
      refine ⟨96084404667224667894089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 256225079112599114384237 96084404667224667894089)
      ·
        refine ⟨72063303500418500920567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96084404667224667894089 72063303500418500920567)
        ·
          refine ⟨108094955250627751380851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72063303500418500920567 108094955250627751380851)
          ·
            refine ⟨162142432875941627071277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108094955250627751380851 162142432875941627071277)
            ·
              refine ⟨60803412328478110151729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 162142432875941627071277 60803412328478110151729)
              ·
                refine ⟨45602559246358582613797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60803412328478110151729 45602559246358582613797)
                ·
                  refine ⟨8550479858692234240087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 45602559246358582613797 8550479858692234240087)
                  ·
                    rfl

theorem cell22_74934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 3, 2, 4].length) (baseStart_74934 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_74934 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_74934 prefixEnd_74934 := by exact prefixLift 74934
  have htrace : WordTrace (prefixWord ++ tailWord_74934) baseStart_74934 baseEnd_74934 := by
    simpa [prefixWord, tailWord_74934, baseEnd_74934] using wordTrace_append hprefix tailTrace_74934
  have hstable : (prefixWord ++ tailWord_74934).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74934).length < 2 ^ (prefixWord ++ tailWord_74934).sum := by decide
  have hdescent : baseEnd_74934 < baseStart_74934 := by decide
  rcases family_descends (prefixWord ++ tailWord_74934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74943 : List Nat := [1, 1, 2, 2, 2, 2, 2, 6, 1, 3]
def baseStart_74943 : Nat := 118140960795 + 74943 * 2 ^ 59
def prefixEnd_74943 : Nat := 4983230072969 + 3 ^ 40 * 74943 * 2
def baseEnd_74943 : Nat := 25654520460003679245233

theorem tailTrace_74943 : CollatzResearch.WordTrace tailWord_74943 prefixEnd_74943 25654520460003679245233 := by
  unfold tailWord_74943
  simp only [CollatzResearch.WordTrace]
  refine ⟨2733395767501785090509483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1822263845001190060339655 2733395767501785090509483)
  ·
    refine ⟨4100093651252677635764225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2733395767501785090509483 4100093651252677635764225)
    ·
      refine ⟨3075070238439508226823169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4100093651252677635764225 3075070238439508226823169)
      ·
        refine ⟨2306302678829631170117377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3075070238439508226823169 2306302678829631170117377)
        ·
          refine ⟨1729727009122223377588033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2306302678829631170117377 1729727009122223377588033)
          ·
            refine ⟨1297295256841667533191025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1729727009122223377588033 1297295256841667533191025)
            ·
              refine ⟨972971442631250649893269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1297295256841667533191025 972971442631250649893269)
              ·
                refine ⟨45608036373339874213747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 972971442631250649893269 45608036373339874213747)
                ·
                  refine ⟨68412054560009811320621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45608036373339874213747 68412054560009811320621)
                  ·
                    refine ⟨25654520460003679245233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 68412054560009811320621 25654520460003679245233)
                    ·
                      rfl

theorem cell22_74943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 6, 1, 3].length) (baseStart_74943 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_74943 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_74943 prefixEnd_74943 := by exact prefixLift 74943
  have htrace : WordTrace (prefixWord ++ tailWord_74943) baseStart_74943 baseEnd_74943 := by
    simpa [prefixWord, tailWord_74943, baseEnd_74943] using wordTrace_append hprefix tailTrace_74943
  have hstable : (prefixWord ++ tailWord_74943).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74943).length < 2 ^ (prefixWord ++ tailWord_74943).sum := by decide
  have hdescent : baseEnd_74943 < baseStart_74943 := by decide
  rcases family_descends (prefixWord ++ tailWord_74943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74994 : List Nat := [3, 2, 1, 3, 3, 2, 2, 2, 1, 3]
def baseStart_74994 : Nat := 118140960795 + 74994 * 2 ^ 59
def prefixEnd_74994 : Nat := 4983230072969 + 3 ^ 40 * 74994 * 2
def baseEnd_74994 : Nat := 25671978802256546220077

theorem tailTrace_74994 : CollatzResearch.WordTrace tailWord_74994 prefixEnd_74994 25671978802256546220077 := by
  unfold tailWord_74994
  simp only [CollatzResearch.WordTrace]
  refine ⟨683813972579255200154009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1823503926878013867077357 683813972579255200154009)
  ·
    refine ⟨512860479434441400115507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 683813972579255200154009 512860479434441400115507)
    ·
      refine ⟨769290719151662100173261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 512860479434441400115507 769290719151662100173261)
      ·
        refine ⟨288484019681873287564973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 769290719151662100173261 288484019681873287564973)
        ·
          refine ⟨108181507380702482836865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 288484019681873287564973 108181507380702482836865)
          ·
            refine ⟨81136130535526862127649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 108181507380702482836865 81136130535526862127649)
            ·
              refine ⟨60852097901645146595737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 81136130535526862127649 60852097901645146595737)
              ·
                refine ⟨45639073426233859946803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60852097901645146595737 45639073426233859946803)
                ·
                  refine ⟨68458610139350789920205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45639073426233859946803 68458610139350789920205)
                  ·
                    refine ⟨25671978802256546220077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 68458610139350789920205 25671978802256546220077)
                    ·
                      rfl

theorem cell22_74994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 2, 2, 2, 1, 3].length) (baseStart_74994 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_74994 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_74994 prefixEnd_74994 := by exact prefixLift 74994
  have htrace : WordTrace (prefixWord ++ tailWord_74994) baseStart_74994 baseEnd_74994 := by
    simpa [prefixWord, tailWord_74994, baseEnd_74994] using wordTrace_append hprefix tailTrace_74994
  have hstable : (prefixWord ++ tailWord_74994).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74994).length < 2 ^ (prefixWord ++ tailWord_74994).sum := by decide
  have hdescent : baseEnd_74994 < baseStart_74994 := by decide
  rcases family_descends (prefixWord ++ tailWord_74994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_75031 : List Nat := [1, 1, 3, 4, 1, 1, 3, 1, 1, 6]
def baseStart_75031 : Nat := 118140960795 + 75031 * 2 ^ 59
def prefixEnd_75031 : Nat := 4983230072969 + 3 ^ 40 * 75031 * 2
def baseEnd_75031 : Nat := 25684644658400783044963

theorem tailTrace_75031 : CollatzResearch.WordTrace tailWord_75031 prefixEnd_75031 25684644658400783044963 := by
  unfold tailWord_75031
  simp only [CollatzResearch.WordTrace]
  refine ⟨2736605391182976119712947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1824403594121984079808631 2736605391182976119712947)
  ·
    refine ⟨4104908086774464179569421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2736605391182976119712947 4104908086774464179569421)
    ·
      refine ⟨1539340532540424067338533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4104908086774464179569421 1539340532540424067338533)
      ·
        refine ⟨288626349851329512625975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1539340532540424067338533 288626349851329512625975)
        ·
          refine ⟨432939524776994268938963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 288626349851329512625975 432939524776994268938963)
          ·
            refine ⟨649409287165491403408445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 432939524776994268938963 649409287165491403408445)
            ·
              refine ⟨243528482687059276278167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 649409287165491403408445 243528482687059276278167)
              ·
                refine ⟨365292724030588914417251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 243528482687059276278167 365292724030588914417251)
                ·
                  refine ⟨547939086045883371625877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 365292724030588914417251 547939086045883371625877)
                  ·
                    refine ⟨25684644658400783044963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 547939086045883371625877 25684644658400783044963)
                    ·
                      rfl

theorem cell22_75031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 3, 1, 1, 6].length) (baseStart_75031 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_75031 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_75031 prefixEnd_75031 := by exact prefixLift 75031
  have htrace : WordTrace (prefixWord ++ tailWord_75031) baseStart_75031 baseEnd_75031 := by
    simpa [prefixWord, tailWord_75031, baseEnd_75031] using wordTrace_append hprefix tailTrace_75031
  have hstable : (prefixWord ++ tailWord_75031).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_75031).length < 2 ^ (prefixWord ++ tailWord_75031).sum := by decide
  have hdescent : baseEnd_75031 < baseStart_75031 := by decide
  rcases family_descends (prefixWord ++ tailWord_75031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_75037 : List Nat := [1, 4, 2, 3, 1, 3, 2, 1, 1, 4]
def baseStart_75037 : Nat := 118140960795 + 75037 * 2 ^ 59
def prefixEnd_75037 : Nat := 4983230072969 + 3 ^ 40 * 75037 * 2
def baseEnd_75037 : Nat := 25686698581018767394945

theorem tailTrace_75037 : CollatzResearch.WordTrace tailWord_75037 prefixEnd_75037 25686698581018767394945 := by
  unfold tailWord_75037
  simp only [CollatzResearch.WordTrace]
  refine ⟨2736824229161239144431365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1824549486107492762954243 2736824229161239144431365)
  ·
    refine ⟨513154542967732339580881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2736824229161239144431365 513154542967732339580881)
    ·
      refine ⟨384865907225799254685661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 513154542967732339580881 384865907225799254685661)
      ·
        refine ⟨144324715209674720507123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 384865907225799254685661 144324715209674720507123)
        ·
          refine ⟨216487072814512080760685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 144324715209674720507123 216487072814512080760685)
          ·
            refine ⟨81182652305442030285257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 216487072814512080760685 81182652305442030285257)
            ·
              refine ⟨60886989229081522713943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 81182652305442030285257 60886989229081522713943)
              ·
                refine ⟨91330483843622284070915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60886989229081522713943 91330483843622284070915)
                ·
                  refine ⟨136995725765433426106373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 91330483843622284070915 136995725765433426106373)
                  ·
                    refine ⟨25686698581018767394945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 136995725765433426106373 25686698581018767394945)
                    ·
                      rfl

theorem cell22_75037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 3, 2, 1, 1, 4].length) (baseStart_75037 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_75037 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_75037 prefixEnd_75037 := by exact prefixLift 75037
  have htrace : WordTrace (prefixWord ++ tailWord_75037) baseStart_75037 baseEnd_75037 := by
    simpa [prefixWord, tailWord_75037, baseEnd_75037] using wordTrace_append hprefix tailTrace_75037
  have hstable : (prefixWord ++ tailWord_75037).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_75037).length < 2 ^ (prefixWord ++ tailWord_75037).sum := by decide
  have hdescent : baseEnd_75037 < baseStart_75037 := by decide
  rcases family_descends (prefixWord ++ tailWord_75037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_75050 : List Nat := [3, 1, 4, 2, 1, 2, 1, 1, 4, 3]
def baseStart_75050 : Nat := 118140960795 + 75050 * 2 ^ 59
def prefixEnd_75050 : Nat := 4983230072969 + 3 ^ 40 * 75050 * 2
def baseEnd_75050 : Nat := 25691148746691066819905

theorem tailTrace_75050 : CollatzResearch.WordTrace tailWord_75050 prefixEnd_75050 25691148746691066819905 := by
  unfold tailWord_75050
  simp only [CollatzResearch.WordTrace]
  refine ⟨684324594528535591163651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1824865585409428243103069 684324594528535591163651)
  ·
    refine ⟨1026486891792803386745477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 684324594528535591163651 1026486891792803386745477)
    ·
      refine ⟨192466292211150635014777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1026486891792803386745477 192466292211150635014777)
      ·
        refine ⟨144349719158362976261083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 192466292211150635014777 144349719158362976261083)
        ·
          refine ⟨216524578737544464391625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 144349719158362976261083 216524578737544464391625)
          ·
            refine ⟨162393434053158348293719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 216524578737544464391625 162393434053158348293719)
            ·
              refine ⟨243590151079737522440579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 162393434053158348293719 243590151079737522440579)
              ·
                refine ⟨365385226619606283660869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 243590151079737522440579 365385226619606283660869)
                ·
                  refine ⟨68509729991176178186413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 365385226619606283660869 68509729991176178186413)
                  ·
                    refine ⟨25691148746691066819905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 68509729991176178186413 25691148746691066819905)
                    ·
                      rfl

theorem cell22_75050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 1, 1, 4, 3].length) (baseStart_75050 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_75050 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_75050 prefixEnd_75050 := by exact prefixLift 75050
  have htrace : WordTrace (prefixWord ++ tailWord_75050) baseStart_75050 baseEnd_75050 := by
    simpa [prefixWord, tailWord_75050, baseEnd_75050] using wordTrace_append hprefix tailTrace_75050
  have hstable : (prefixWord ++ tailWord_75050).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_75050).length < 2 ^ (prefixWord ++ tailWord_75050).sum := by decide
  have hdescent : baseEnd_75050 < baseStart_75050 := by decide
  rcases family_descends (prefixWord ++ tailWord_75050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_75112 : List Nat := [2, 1, 4, 2, 3, 2, 1, 1, 3, 3]
def baseStart_75112 : Nat := 118140960795 + 75112 * 2 ^ 59
def prefixEnd_75112 : Nat := 4983230072969 + 3 ^ 40 * 75112 * 2
def baseEnd_75112 : Nat := 25712372613743571769715

theorem tailTrace_75112 : CollatzResearch.WordTrace tailWord_75112 prefixEnd_75112 25712372613743571769715 := by
  unfold tailWord_75112
  simp only [CollatzResearch.WordTrace]
  refine ⟨1369779851944763476705795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1826373135926351302274393 1369779851944763476705795)
  ·
    refine ⟨2054669777917145215058693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1369779851944763476705795 2054669777917145215058693)
    ·
      refine ⟨385250583359464727823505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2054669777917145215058693 385250583359464727823505)
      ·
        refine ⟨288937937519598545867629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 385250583359464727823505 288937937519598545867629)
        ·
          refine ⟨108351726569849454700361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 288937937519598545867629 108351726569849454700361)
          ·
            refine ⟨81263794927387091025271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 108351726569849454700361 81263794927387091025271)
            ·
              refine ⟨121895692391080636537907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81263794927387091025271 121895692391080636537907)
              ·
                refine ⟨182843538586620954806861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 121895692391080636537907 182843538586620954806861)
                ·
                  refine ⟨68566326969982858052573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 182843538586620954806861 68566326969982858052573)
                  ·
                    refine ⟨25712372613743571769715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 68566326969982858052573 25712372613743571769715)
                    ·
                      rfl

theorem cell22_75112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 2, 1, 1, 3, 3].length) (baseStart_75112 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_75112 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_75112 prefixEnd_75112 := by exact prefixLift 75112
  have htrace : WordTrace (prefixWord ++ tailWord_75112) baseStart_75112 baseEnd_75112 := by
    simpa [prefixWord, tailWord_75112, baseEnd_75112] using wordTrace_append hprefix tailTrace_75112
  have hstable : (prefixWord ++ tailWord_75112).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_75112).length < 2 ^ (prefixWord ++ tailWord_75112).sum := by decide
  have hdescent : baseEnd_75112 < baseStart_75112 := by decide
  rcases family_descends (prefixWord ++ tailWord_75112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_75125 : List Nat := [1, 3, 4, 1, 3, 1, 1, 3, 5]
def baseStart_75125 : Nat := 118140960795 + 75125 * 2 ^ 59
def prefixEnd_75125 : Nat := 4983230072969 + 3 ^ 40 * 75125 * 2
def baseEnd_75125 : Nat := 8572274259805290398225

theorem tailTrace_75125 : CollatzResearch.WordTrace tailWord_75125 prefixEnd_75125 8572274259805290398225 := by
  unfold tailWord_75125
  simp only [CollatzResearch.WordTrace]
  refine ⟨2740033852842430173634829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1826689235228286782423219 2740033852842430173634829)
  ·
    refine ⟨1027512694815911315113061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2740033852842430173634829 1027512694815911315113061)
    ·
      refine ⟨192658630277983371583699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1027512694815911315113061 192658630277983371583699)
      ·
        refine ⟨288987945416975057375549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 192658630277983371583699 288987945416975057375549)
        ·
          refine ⟨108370479531365646515831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 288987945416975057375549 108370479531365646515831)
          ·
            refine ⟨162555719297048469773747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108370479531365646515831 162555719297048469773747)
            ·
              refine ⟨243833578945572704660621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 162555719297048469773747 243833578945572704660621)
              ·
                refine ⟨91437592104589764247733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 243833578945572704660621 91437592104589764247733)
                ·
                  refine ⟨8572274259805290398225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 91437592104589764247733 8572274259805290398225)
                  ·
                    rfl

theorem cell22_75125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 1, 3, 5].length) (baseStart_75125 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_75125 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_75125 prefixEnd_75125 := by exact prefixLift 75125
  have htrace : WordTrace (prefixWord ++ tailWord_75125) baseStart_75125 baseEnd_75125 := by
    simpa [prefixWord, tailWord_75125, baseEnd_75125] using wordTrace_append hprefix tailTrace_75125
  have hstable : (prefixWord ++ tailWord_75125).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_75125).length < 2 ^ (prefixWord ++ tailWord_75125).sum := by decide
  have hdescent : baseEnd_75125 < baseStart_75125 := by decide
  rcases family_descends (prefixWord ++ tailWord_75125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_75136 : List Nat := [2, 1, 1, 2, 1, 2, 1, 6, 6]
def baseStart_75136 : Nat := 118140960795 + 75136 * 2 ^ 59
def prefixEnd_75136 : Nat := 4983230072969 + 3 ^ 40 * 75136 * 2
def baseEnd_75136 : Nat := 8573529434738503056547

theorem tailTrace_75136 : CollatzResearch.WordTrace tailWord_75136 prefixEnd_75136 8573529434738503056547 := by
  unfold tailWord_75136
  simp only [CollatzResearch.WordTrace]
  refine ⟨1370217527901289526142631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1826956703868386034856841 1370217527901289526142631)
  ·
    refine ⟨2055326291851934289213947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1370217527901289526142631 2055326291851934289213947)
    ·
      refine ⟨3082989437777901433820921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2055326291851934289213947 3082989437777901433820921)
      ·
        refine ⟨2312242078333426075365691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3082989437777901433820921 2312242078333426075365691)
        ·
          refine ⟨3468363117500139113048537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2312242078333426075365691 3468363117500139113048537)
          ·
            refine ⟨2601272338125104334786403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3468363117500139113048537 2601272338125104334786403)
            ·
              refine ⟨3901908507187656502179605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2601272338125104334786403 3901908507187656502179605)
              ·
                refine ⟨182901961274421398539669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3901908507187656502179605 182901961274421398539669)
                ·
                  refine ⟨8573529434738503056547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 182901961274421398539669 8573529434738503056547)
                  ·
                    rfl

theorem cell22_75136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 6, 6].length) (baseStart_75136 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_75136 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_75136 prefixEnd_75136 := by exact prefixLift 75136
  have htrace : WordTrace (prefixWord ++ tailWord_75136) baseStart_75136 baseEnd_75136 := by
    simpa [prefixWord, tailWord_75136, baseEnd_75136] using wordTrace_append hprefix tailTrace_75136
  have hstable : (prefixWord ++ tailWord_75136).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_75136).length < 2 ^ (prefixWord ++ tailWord_75136).sum := by decide
  have hdescent : baseEnd_75136 < baseStart_75136 := by decide
  rcases family_descends (prefixWord ++ tailWord_75136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_75185 : List Nat := [1, 2, 2, 4, 1, 1, 1, 5, 2, 3]
def baseStart_75185 : Nat := 118140960795 + 75185 * 2 ^ 59
def prefixEnd_75185 : Nat := 4983230072969 + 3 ^ 40 * 75185 * 2
def baseEnd_75185 : Nat := 25737362005595714694491

theorem tailTrace_75185 : CollatzResearch.WordTrace tailWord_75185 prefixEnd_75185 25737362005595714694491 := by
  unfold tailWord_75185
  simp only [CollatzResearch.WordTrace]
  refine ⟨2742222232625060420819009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1828148155083373613879339 2742222232625060420819009)
  ·
    refine ⟨2056666674468795315614257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2742222232625060420819009 2056666674468795315614257)
    ·
      refine ⟨1542500005851596486710693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2056666674468795315614257 1542500005851596486710693)
      ·
        refine ⟨289218751097174341258255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1542500005851596486710693 289218751097174341258255)
        ·
          refine ⟨433828126645761511887383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 289218751097174341258255 433828126645761511887383)
          ·
            refine ⟨650742189968642267831075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 433828126645761511887383 650742189968642267831075)
            ·
              refine ⟨976113284952963401746613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 650742189968642267831075 976113284952963401746613)
              ·
                refine ⟨91510620464340318913745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 976113284952963401746613 91510620464340318913745)
                ·
                  refine ⟨68632965348255239185309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 91510620464340318913745 68632965348255239185309)
                  ·
                    refine ⟨25737362005595714694491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 68632965348255239185309 25737362005595714694491)
                    ·
                      rfl

theorem cell22_75185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 5, 2, 3].length) (baseStart_75185 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_75185 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_75185 prefixEnd_75185 := by exact prefixLift 75185
  have htrace : WordTrace (prefixWord ++ tailWord_75185) baseStart_75185 baseEnd_75185 := by
    simpa [prefixWord, tailWord_75185, baseEnd_75185] using wordTrace_append hprefix tailTrace_75185
  have hstable : (prefixWord ++ tailWord_75185).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_75185).length < 2 ^ (prefixWord ++ tailWord_75185).sum := by decide
  have hdescent : baseEnd_75185 < baseStart_75185 := by decide
  rcases family_descends (prefixWord ++ tailWord_75185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_75320 : List Nat := [2, 1, 2, 1, 4, 3, 1, 2, 1, 5]
def baseStart_75320 : Nat := 118140960795 + 75320 * 2 ^ 59
def prefixEnd_75320 : Nat := 4983230072969 + 3 ^ 40 * 75320 * 2
def baseEnd_75320 : Nat := 25783575264500362569077

theorem tailTrace_75320 : CollatzResearch.WordTrace tailWord_75320 prefixEnd_75320 25783575264500362569077 := by
  unfold tailWord_75320
  simp only [CollatzResearch.WordTrace]
  refine ⟨1373573043567989238491707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1831430724757318984655609 1373573043567989238491707)
  ·
    refine ⟨2060359565351983857737561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1373573043567989238491707 2060359565351983857737561)
    ·
      refine ⟨1545269674013987893303171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2060359565351983857737561 1545269674013987893303171)
      ·
        refine ⟨2317904511020981839954757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1545269674013987893303171 2317904511020981839954757)
        ·
          refine ⟨434607095816434094991517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2317904511020981839954757 434607095816434094991517)
          ·
            refine ⟨162977660931162785621819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 434607095816434094991517 162977660931162785621819)
            ·
              refine ⟨244466491396744178432729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 162977660931162785621819 244466491396744178432729)
              ·
                refine ⟨183349868547558133824547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 244466491396744178432729 183349868547558133824547)
                ·
                  refine ⟨275024802821337200736821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 183349868547558133824547 275024802821337200736821)
                  ·
                    refine ⟨25783575264500362569077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 275024802821337200736821 25783575264500362569077)
                    ·
                      rfl

theorem cell22_75320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 1, 2, 1, 5].length) (baseStart_75320 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_75320 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_75320 prefixEnd_75320 := by exact prefixLift 75320
  have htrace : WordTrace (prefixWord ++ tailWord_75320) baseStart_75320 baseEnd_75320 := by
    simpa [prefixWord, tailWord_75320, baseEnd_75320] using wordTrace_append hprefix tailTrace_75320
  have hstable : (prefixWord ++ tailWord_75320).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_75320).length < 2 ^ (prefixWord ++ tailWord_75320).sum := by decide
  have hdescent : baseEnd_75320 < baseStart_75320 := by decide
  rcases family_descends (prefixWord ++ tailWord_75320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_75324 : List Nat := [2, 2, 2, 2, 4, 1, 3, 1, 1, 4]
def baseStart_75324 : Nat := 118140960795 + 75324 * 2 ^ 59
def prefixEnd_75324 : Nat := 4983230072969 + 3 ^ 40 * 75324 * 2
def baseEnd_75324 : Nat := 25784944546245685469065

theorem tailTrace_75324 : CollatzResearch.WordTrace tailWord_75324 prefixEnd_75324 25784944546245685469065 := by
  unfold tailWord_75324
  simp only [CollatzResearch.WordTrace]
  refine ⟨1373645989560743580064513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1831527986080991440086017 1373645989560743580064513)
  ·
    refine ⟨1030234492170557685048385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1373645989560743580064513 1030234492170557685048385)
    ·
      refine ⟨772675869127918263786289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1030234492170557685048385 772675869127918263786289)
      ·
        refine ⟨579506901845938697839717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 772675869127918263786289 579506901845938697839717)
        ·
          refine ⟨108657544096113505844947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 579506901845938697839717 108657544096113505844947)
          ·
            refine ⟨162986316144170258767421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108657544096113505844947 162986316144170258767421)
            ·
              refine ⟨61119868554063847037783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 162986316144170258767421 61119868554063847037783)
              ·
                refine ⟨91679802831095770556675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61119868554063847037783 91679802831095770556675)
                ·
                  refine ⟨137519704246643655835013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 91679802831095770556675 137519704246643655835013)
                  ·
                    refine ⟨25784944546245685469065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 137519704246643655835013 25784944546245685469065)
                    ·
                      rfl

theorem cell22_75324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 3, 1, 1, 4].length) (baseStart_75324 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_75324 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_75324 prefixEnd_75324 := by exact prefixLift 75324
  have htrace : WordTrace (prefixWord ++ tailWord_75324) baseStart_75324 baseEnd_75324 := by
    simpa [prefixWord, tailWord_75324, baseEnd_75324] using wordTrace_append hprefix tailTrace_75324
  have hstable : (prefixWord ++ tailWord_75324).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_75324).length < 2 ^ (prefixWord ++ tailWord_75324).sum := by decide
  have hdescent : baseEnd_75324 < baseStart_75324 := by decide
  rcases family_descends (prefixWord ++ tailWord_75324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_75399 : List Nat := [1, 1, 4, 2, 1, 3, 2, 4, 1, 3]
def baseStart_75399 : Nat := 118140960795 + 75399 * 2 ^ 59
def prefixEnd_75399 : Nat := 4983230072969 + 3 ^ 40 * 75399 * 2
def baseEnd_75399 : Nat := 25810618578970489843835

theorem tailTrace_75399 : CollatzResearch.WordTrace tailWord_75399 prefixEnd_75399 25810618578970489843835 := by
  unfold tailWord_75399
  simp only [CollatzResearch.WordTrace]
  refine ⟨2750027453849774969109251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1833351635899849979406167 2750027453849774969109251)
  ·
    refine ⟨4125041180774662453663877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2750027453849774969109251 4125041180774662453663877)
    ·
      refine ⟨773445221395249210061977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4125041180774662453663877 773445221395249210061977)
      ·
        refine ⟨580083916046436907546483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 773445221395249210061977 580083916046436907546483)
        ·
          refine ⟨870125874069655361319725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 580083916046436907546483 870125874069655361319725)
          ·
            refine ⟨326297202776120760494897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 870125874069655361319725 326297202776120760494897)
            ·
              refine ⟨244722902082090570371173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 326297202776120760494897 244722902082090570371173)
              ·
                refine ⟨45885544140391981944595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 244722902082090570371173 45885544140391981944595)
                ·
                  refine ⟨68828316210587972916893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45885544140391981944595 68828316210587972916893)
                  ·
                    refine ⟨25810618578970489843835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 68828316210587972916893 25810618578970489843835)
                    ·
                      rfl

theorem cell22_75399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 2, 4, 1, 3].length) (baseStart_75399 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_75399 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_75399 prefixEnd_75399 := by exact prefixLift 75399
  have htrace : WordTrace (prefixWord ++ tailWord_75399) baseStart_75399 baseEnd_75399 := by
    simpa [prefixWord, tailWord_75399, baseEnd_75399] using wordTrace_append hprefix tailTrace_75399
  have hstable : (prefixWord ++ tailWord_75399).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_75399).length < 2 ^ (prefixWord ++ tailWord_75399).sum := by decide
  have hdescent : baseEnd_75399 < baseStart_75399 := by decide
  rcases family_descends (prefixWord ++ tailWord_75399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_75442 : List Nat := [3, 2, 1, 1, 1, 2, 4, 3, 1, 4]
def baseStart_75442 : Nat := 118140960795 + 75442 * 2 ^ 59
def prefixEnd_75442 : Nat := 4983230072969 + 3 ^ 40 * 75442 * 2
def baseEnd_75442 : Nat := 25825338357732711018703

theorem tailTrace_75442 : CollatzResearch.WordTrace tailWord_75442 prefixEnd_75442 25825338357732711018703 := by
  unfold tailWord_75442
  simp only [CollatzResearch.WordTrace]
  refine ⟨687898948173498328231145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1834397195129328875283053 687898948173498328231145)
  ·
    refine ⟨515924211130123746173359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 687898948173498328231145 515924211130123746173359)
    ·
      refine ⟨773886316695185619260039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 515924211130123746173359 773886316695185619260039)
      ·
        refine ⟨1160829475042778428890059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 773886316695185619260039 1160829475042778428890059)
        ·
          refine ⟨1741244212564167643335089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1160829475042778428890059 1741244212564167643335089)
          ·
            refine ⟨1305933159423125732501317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1741244212564167643335089 1305933159423125732501317)
            ·
              refine ⟨244862467391836074843997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1305933159423125732501317 244862467391836074843997)
              ·
                refine ⟨91823425271938528066499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 244862467391836074843997 91823425271938528066499)
                ·
                  refine ⟨137735137907907792099749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 91823425271938528066499 137735137907907792099749)
                  ·
                    refine ⟨25825338357732711018703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 137735137907907792099749 25825338357732711018703)
                    ·
                      rfl

theorem cell22_75442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 4, 3, 1, 4].length) (baseStart_75442 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_75442 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_75442 prefixEnd_75442 := by exact prefixLift 75442
  have htrace : WordTrace (prefixWord ++ tailWord_75442) baseStart_75442 baseEnd_75442 := by
    simpa [prefixWord, tailWord_75442, baseEnd_75442] using wordTrace_append hprefix tailTrace_75442
  have hstable : (prefixWord ++ tailWord_75442).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_75442).length < 2 ^ (prefixWord ++ tailWord_75442).sum := by decide
  have hdescent : baseEnd_75442 < baseStart_75442 := by decide
  rcases family_descends (prefixWord ++ tailWord_75442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_75476 : List Nat := [2, 4, 1, 3, 1, 3, 1, 2, 1, 4]
def baseStart_75476 : Nat := 118140960795 + 75476 * 2 ^ 59
def prefixEnd_75476 : Nat := 4983230072969 + 3 ^ 40 * 75476 * 2
def baseEnd_75476 : Nat := 25836977252567955668599

theorem tailTrace_75476 : CollatzResearch.WordTrace tailWord_75476 prefixEnd_75476 25836977252567955668599 := by
  unfold tailWord_75476
  simp only [CollatzResearch.WordTrace]
  refine ⟨1376417937285408559831141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1835223916380544746441521 1376417937285408559831141)
  ·
    refine ⟨258078363241014104968339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1376417937285408559831141 258078363241014104968339)
    ·
      refine ⟨387117544861521157452509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 258078363241014104968339 387117544861521157452509)
      ·
        refine ⟨145169079323070434044691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 387117544861521157452509 145169079323070434044691)
        ·
          refine ⟨217753618984605651067037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 145169079323070434044691 217753618984605651067037)
          ·
            refine ⟨81657607119227119150139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 217753618984605651067037 81657607119227119150139)
            ·
              refine ⟨122486410678840678725209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81657607119227119150139 122486410678840678725209)
              ·
                refine ⟨91864808009130509043907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 122486410678840678725209 91864808009130509043907)
                ·
                  refine ⟨137797212013695763565861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 91864808009130509043907 137797212013695763565861)
                  ·
                    refine ⟨25836977252567955668599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 137797212013695763565861 25836977252567955668599)
                    ·
                      rfl

theorem cell22_75476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 3, 1, 2, 1, 4].length) (baseStart_75476 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_75476 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_75476 prefixEnd_75476 := by exact prefixLift 75476
  have htrace : WordTrace (prefixWord ++ tailWord_75476) baseStart_75476 baseEnd_75476 := by
    simpa [prefixWord, tailWord_75476, baseEnd_75476] using wordTrace_append hprefix tailTrace_75476
  have hstable : (prefixWord ++ tailWord_75476).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_75476).length < 2 ^ (prefixWord ++ tailWord_75476).sum := by decide
  have hdescent : baseEnd_75476 < baseStart_75476 := by decide
  rcases family_descends (prefixWord ++ tailWord_75476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_75487 : List Nat := [1, 1, 2, 3, 2, 2, 4, 1, 2, 4]
def baseStart_75487 : Nat := 118140960795 + 75487 * 2 ^ 59
def prefixEnd_75487 : Nat := 4983230072969 + 3 ^ 40 * 75487 * 2
def baseEnd_75487 : Nat := 25840742777367593643565

theorem tailTrace_75487 : CollatzResearch.WordTrace tailWord_75487 prefixEnd_75487 25840742777367593643565 := by
  unfold tailWord_75487
  simp only [CollatzResearch.WordTrace]
  refine ⟨2753237077530965998312715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1835491385020643998875143 2753237077530965998312715)
  ·
    refine ⟨4129855616296448997469073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2753237077530965998312715 4129855616296448997469073)
    ·
      refine ⟨3097391712222336748101805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4129855616296448997469073 3097391712222336748101805)
      ·
        refine ⟨1161521892083376280538177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3097391712222336748101805 1161521892083376280538177)
        ·
          refine ⟨871141419062532210403633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1161521892083376280538177 871141419062532210403633)
          ·
            refine ⟨653356064296899157802725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 871141419062532210403633 653356064296899157802725)
            ·
              refine ⟨122504262055668592088011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 653356064296899157802725 122504262055668592088011)
              ·
                refine ⟨183756393083502888132017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 122504262055668592088011 183756393083502888132017)
                ·
                  refine ⟨137817294812627166099013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 183756393083502888132017 137817294812627166099013)
                  ·
                    refine ⟨25840742777367593643565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 137817294812627166099013 25840742777367593643565)
                    ·
                      rfl

theorem cell22_75487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 4, 1, 2, 4].length) (baseStart_75487 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_75487 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_75487 prefixEnd_75487 := by exact prefixLift 75487
  have htrace : WordTrace (prefixWord ++ tailWord_75487) baseStart_75487 baseEnd_75487 := by
    simpa [prefixWord, tailWord_75487, baseEnd_75487] using wordTrace_append hprefix tailTrace_75487
  have hstable : (prefixWord ++ tailWord_75487).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_75487).length < 2 ^ (prefixWord ++ tailWord_75487).sum := by decide
  have hdescent : baseEnd_75487 < baseStart_75487 := by decide
  rcases family_descends (prefixWord ++ tailWord_75487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_75508 : List Nat := [2, 6, 1, 1, 1, 2, 1, 4, 4]
def baseStart_75508 : Nat := 118140960795 + 75508 * 2 ^ 59
def prefixEnd_75508 : Nat := 4983230072969 + 3 ^ 40 * 75508 * 2
def baseEnd_75508 : Nat := 8615977168843512956167

theorem tailTrace_75508 : CollatzResearch.WordTrace tailWord_75508 prefixEnd_75508 8615977168843512956167 := by
  unfold tailWord_75508
  simp only [CollatzResearch.WordTrace]
  refine ⟨1377001505227443292413589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1836002006969924389884785 1377001505227443292413589)
  ·
    refine ⟨64546945557536404331887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 1377001505227443292413589 64546945557536404331887)
    ·
      refine ⟨96820418336304606497831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64546945557536404331887 96820418336304606497831)
      ·
        refine ⟨145230627504456909746747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96820418336304606497831 145230627504456909746747)
        ·
          refine ⟨217845941256685364620121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 145230627504456909746747 217845941256685364620121)
          ·
            refine ⟨163384455942514023465091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 217845941256685364620121 163384455942514023465091)
            ·
              refine ⟨245076683913771035197637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 163384455942514023465091 245076683913771035197637)
              ·
                refine ⟨45951878233832069099557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 245076683913771035197637 45951878233832069099557)
                ·
                  refine ⟨8615977168843512956167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 45951878233832069099557 8615977168843512956167)
                  ·
                    rfl

theorem cell22_75508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 1, 4, 4].length) (baseStart_75508 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_75508 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_75508 prefixEnd_75508 := by exact prefixLift 75508
  have htrace : WordTrace (prefixWord ++ tailWord_75508) baseStart_75508 baseEnd_75508 := by
    simpa [prefixWord, tailWord_75508, baseEnd_75508] using wordTrace_append hprefix tailTrace_75508
  have hstable : (prefixWord ++ tailWord_75508).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_75508).length < 2 ^ (prefixWord ++ tailWord_75508).sum := by decide
  have hdescent : baseEnd_75508 < baseStart_75508 := by decide
  rcases family_descends (prefixWord ++ tailWord_75508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_75551 : List Nat := [1, 1, 2, 4, 2, 1, 4, 3, 1, 3]
def baseStart_75551 : Nat := 118140960795 + 75551 * 2 ^ 59
def prefixEnd_75551 : Nat := 4983230072969 + 3 ^ 40 * 75551 * 2
def baseEnd_75551 : Nat := 25862651285292760043369

theorem tailTrace_75551 : CollatzResearch.WordTrace tailWord_75551 prefixEnd_75551 25862651285292760043369 := by
  unfold tailWord_75551
  simp only [CollatzResearch.WordTrace]
  refine ⟨2755571349299104928642507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1837047566199403285761671 2755571349299104928642507)
  ·
    refine ⟨4133357023948657392963761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2755571349299104928642507 4133357023948657392963761)
    ·
      refine ⟨3100017767961493044722821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4133357023948657392963761 3100017767961493044722821)
      ·
        refine ⟨581253331492779945885529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3100017767961493044722821 581253331492779945885529)
        ·
          refine ⟨435939998619584959414147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 581253331492779945885529 435939998619584959414147)
          ·
            refine ⟨653909997929377439121221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 435939998619584959414147 653909997929377439121221)
            ·
              refine ⟨122608124611758269835229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 653909997929377439121221 122608124611758269835229)
              ·
                refine ⟨45978046729409351188211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 122608124611758269835229 45978046729409351188211)
                ·
                  refine ⟨68967070094114026782317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45978046729409351188211 68967070094114026782317)
                  ·
                    refine ⟨25862651285292760043369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 68967070094114026782317 25862651285292760043369)
                    ·
                      rfl

theorem cell22_75551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 4, 3, 1, 3].length) (baseStart_75551 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_75551 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_75551 prefixEnd_75551 := by exact prefixLift 75551
  have htrace : WordTrace (prefixWord ++ tailWord_75551) baseStart_75551 baseEnd_75551 := by
    simpa [prefixWord, tailWord_75551, baseEnd_75551] using wordTrace_append hprefix tailTrace_75551
  have hstable : (prefixWord ++ tailWord_75551).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_75551).length < 2 ^ (prefixWord ++ tailWord_75551).sum := by decide
  have hdescent : baseEnd_75551 < baseStart_75551 := by decide
  rcases family_descends (prefixWord ++ tailWord_75551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_75564 : List Nat := [2, 2, 1, 1, 1, 7, 1, 2, 5]
def baseStart_75564 : Nat := 118140960795 + 75564 * 2 ^ 59
def prefixEnd_75564 : Nat := 4983230072969 + 3 ^ 40 * 75564 * 2
def baseEnd_75564 : Nat := 8622367150321686489443

theorem tailTrace_75564 : CollatzResearch.WordTrace tailWord_75564 prefixEnd_75564 8622367150321686489443 := by
  unfold tailWord_75564
  simp only [CollatzResearch.WordTrace]
  refine ⟨1378022749126004074432873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1837363665501338765910497 1378022749126004074432873)
  ·
    refine ⟨1033517061844503055824655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1378022749126004074432873 1033517061844503055824655)
    ·
      refine ⟨1550275592766754583736983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1033517061844503055824655 1550275592766754583736983)
      ·
        refine ⟨2325413389150131875605475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1550275592766754583736983 2325413389150131875605475)
        ·
          refine ⟨3488120083725197813408213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2325413389150131875605475 3488120083725197813408213)
          ·
            refine ⟨81752814462309323751755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 3488120083725197813408213 81752814462309323751755)
            ·
              refine ⟨122629221693463985627633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81752814462309323751755 122629221693463985627633)
              ·
                refine ⟨91971916270097989220725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 122629221693463985627633 91971916270097989220725)
                ·
                  refine ⟨8622367150321686489443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 91971916270097989220725 8622367150321686489443)
                  ·
                    rfl

theorem cell22_75564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 5].length) (baseStart_75564 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_75564 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_75564 prefixEnd_75564 := by exact prefixLift 75564
  have htrace : WordTrace (prefixWord ++ tailWord_75564) baseStart_75564 baseEnd_75564 := by
    simpa [prefixWord, tailWord_75564, baseEnd_75564] using wordTrace_append hprefix tailTrace_75564
  have hstable : (prefixWord ++ tailWord_75564).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_75564).length < 2 ^ (prefixWord ++ tailWord_75564).sum := by decide
  have hdescent : baseEnd_75564 < baseStart_75564 := by decide
  rcases family_descends (prefixWord ++ tailWord_75564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_75581 : List Nat := [1, 4, 1, 4, 1, 2, 3, 1, 5]
def baseStart_75581 : Nat := 118140960795 + 75581 * 2 ^ 59
def prefixEnd_75581 : Nat := 4983230072969 + 3 ^ 40 * 75581 * 2
def baseEnd_75581 : Nat := 8624306966127560597759

theorem tailTrace_75581 : CollatzResearch.WordTrace tailWord_75581 prefixEnd_75581 8624306966127560597759 := by
  unfold tailWord_75581
  simp only [CollatzResearch.WordTrace]
  refine ⟨2756665539190420052234597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1837777026126946701489731 2756665539190420052234597)
  ·
    refine ⟨516874788598203759793987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2756665539190420052234597 516874788598203759793987)
    ·
      refine ⟨775312182897305639690981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 516874788598203759793987 775312182897305639690981)
      ·
        refine ⟨145371034293244807442059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 775312182897305639690981 145371034293244807442059)
        ·
          refine ⟨218056551439867211163089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 145371034293244807442059 218056551439867211163089)
          ·
            refine ⟨163542413579900408372317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 218056551439867211163089 163542413579900408372317)
            ·
              refine ⟨61328405092462653139619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 163542413579900408372317 61328405092462653139619)
              ·
                refine ⟨91992607638693979709429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61328405092462653139619 91992607638693979709429)
                ·
                  refine ⟨8624306966127560597759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 91992607638693979709429 8624306966127560597759)
                  ·
                    rfl

theorem cell22_75581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 3, 1, 5].length) (baseStart_75581 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_75581 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_75581 prefixEnd_75581 := by exact prefixLift 75581
  have htrace : WordTrace (prefixWord ++ tailWord_75581) baseStart_75581 baseEnd_75581 := by
    simpa [prefixWord, tailWord_75581, baseEnd_75581] using wordTrace_append hprefix tailTrace_75581
  have hstable : (prefixWord ++ tailWord_75581).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_75581).length < 2 ^ (prefixWord ++ tailWord_75581).sum := by decide
  have hdescent : baseEnd_75581 < baseStart_75581 := by decide
  rcases family_descends (prefixWord ++ tailWord_75581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_75592 : List Nat := [2, 1, 3, 1, 1, 4, 2, 2, 6]
def baseStart_75592 : Nat := 118140960795 + 75592 * 2 ^ 59
def prefixEnd_75592 : Nat := 4983230072969 + 3 ^ 40 * 75592 * 2
def baseEnd_75592 : Nat := 8625562141060773256081

theorem tailTrace_75592 : CollatzResearch.WordTrace tailWord_75592 prefixEnd_75592 8625562141060773256081 := by
  unfold tailWord_75592
  simp only [CollatzResearch.WordTrace]
  refine ⟨1378533371075284465442515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1838044494767045953923353 1378533371075284465442515)
  ·
    refine ⟨2067800056612926698163773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1378533371075284465442515 2067800056612926698163773)
    ·
      refine ⟨775425021229847511811415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2067800056612926698163773 775425021229847511811415)
      ·
        refine ⟨1163137531844771267717123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 775425021229847511811415 1163137531844771267717123)
        ·
          refine ⟨1744706297767156901575685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1163137531844771267717123 1744706297767156901575685)
          ·
            refine ⟨327132430831341919045441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1744706297767156901575685 327132430831341919045441)
            ·
              refine ⟨245349323123506439284081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 327132430831341919045441 245349323123506439284081)
              ·
                refine ⟨184011992342629829463061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 245349323123506439284081 184011992342629829463061)
                ·
                  refine ⟨8625562141060773256081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 184011992342629829463061 8625562141060773256081)
                  ·
                    rfl

theorem cell22_75592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 2, 2, 6].length) (baseStart_75592 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_75592 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_75592 prefixEnd_75592 := by exact prefixLift 75592
  have htrace : WordTrace (prefixWord ++ tailWord_75592) baseStart_75592 baseEnd_75592 := by
    simpa [prefixWord, tailWord_75592, baseEnd_75592] using wordTrace_append hprefix tailTrace_75592
  have hstable : (prefixWord ++ tailWord_75592).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_75592).length < 2 ^ (prefixWord ++ tailWord_75592).sum := by decide
  have hdescent : baseEnd_75592 < baseStart_75592 := by decide
  rcases family_descends (prefixWord ++ tailWord_75592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_75594 : List Nat := [3, 1, 2, 1, 1, 1, 6, 2, 1, 4]
def baseStart_75594 : Nat := 118140960795 + 75594 * 2 ^ 59
def prefixEnd_75594 : Nat := 4983230072969 + 3 ^ 40 * 75594 * 2
def baseEnd_75594 : Nat := 25877371064054981218237

theorem tailTrace_75594 : CollatzResearch.WordTrace tailWord_75594 prefixEnd_75594 25877371064054981218237 := by
  unfold tailWord_75594
  simp only [CollatzResearch.WordTrace]
  refine ⟨689284922035830818114459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1838093125428882181638557 689284922035830818114459)
  ·
    refine ⟨1033927383053746227171689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 689284922035830818114459 1033927383053746227171689)
    ·
      refine ⟨775445537290309670378767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1033927383053746227171689 775445537290309670378767)
      ·
        refine ⟨1163168305935464505568151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 775445537290309670378767 1163168305935464505568151)
        ·
          refine ⟨1744752458903196758352227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1163168305935464505568151 1744752458903196758352227)
          ·
            refine ⟨2617128688354795137528341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1744752458903196758352227 2617128688354795137528341)
            ·
              refine ⟨122677907266631022071641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 2617128688354795137528341 122677907266631022071641)
              ·
                refine ⟨92008430449973266553731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 122677907266631022071641 92008430449973266553731)
                ·
                  refine ⟨138012645674959899830597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 92008430449973266553731 138012645674959899830597)
                  ·
                    refine ⟨25877371064054981218237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 138012645674959899830597 25877371064054981218237)
                    ·
                      rfl

theorem cell22_75594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 6, 2, 1, 4].length) (baseStart_75594 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_75594 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_75594 prefixEnd_75594 := by exact prefixLift 75594
  have htrace : WordTrace (prefixWord ++ tailWord_75594) baseStart_75594 baseEnd_75594 := by
    simpa [prefixWord, tailWord_75594, baseEnd_75594] using wordTrace_append hprefix tailTrace_75594
  have hstable : (prefixWord ++ tailWord_75594).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_75594).length < 2 ^ (prefixWord ++ tailWord_75594).sum := by decide
  have hdescent : baseEnd_75594 < baseStart_75594 := by decide
  rcases family_descends (prefixWord ++ tailWord_75594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_75624 : List Nat := [2, 1, 4, 2, 1, 1, 1, 3, 4, 3]
def baseStart_75624 : Nat := 118140960795 + 75624 * 2 ^ 59
def prefixEnd_75624 : Nat := 4983230072969 + 3 ^ 40 * 75624 * 2
def baseEnd_75624 : Nat := 25887640677144902968145

theorem tailTrace_75624 : CollatzResearch.WordTrace tailWord_75624 prefixEnd_75624 25887640677144902968145 := by
  unfold tailWord_75624
  simp only [CollatzResearch.WordTrace]
  refine ⟨1379116939017319198024963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1838822585356425597366617 1379116939017319198024963)
  ·
    refine ⟨2068675408525978797037445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1379116939017319198024963 2068675408525978797037445)
    ·
      refine ⟨387876639098621024444521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2068675408525978797037445 387876639098621024444521)
      ·
        refine ⟨290907479323965768333391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 387876639098621024444521 290907479323965768333391)
        ·
          refine ⟨436361218985948652500087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 290907479323965768333391 436361218985948652500087)
          ·
            refine ⟨654541828478922978750131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 436361218985948652500087 654541828478922978750131)
            ·
              refine ⟨981812742718384468125197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 654541828478922978750131 981812742718384468125197)
              ·
                refine ⟨368179778519394175546949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 981812742718384468125197 368179778519394175546949)
                ·
                  refine ⟨69033708472386407915053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 368179778519394175546949 69033708472386407915053)
                  ·
                    refine ⟨25887640677144902968145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 69033708472386407915053 25887640677144902968145)
                    ·
                      rfl

theorem cell22_75624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 3, 4, 3].length) (baseStart_75624 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_75624 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_75624 prefixEnd_75624 := by exact prefixLift 75624
  have htrace : WordTrace (prefixWord ++ tailWord_75624) baseStart_75624 baseEnd_75624 := by
    simpa [prefixWord, tailWord_75624, baseEnd_75624] using wordTrace_append hprefix tailTrace_75624
  have hstable : (prefixWord ++ tailWord_75624).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_75624).length < 2 ^ (prefixWord ++ tailWord_75624).sum := by decide
  have hdescent : baseEnd_75624 < baseStart_75624 := by decide
  rcases family_descends (prefixWord ++ tailWord_75624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_75652 : List Nat := [2, 3, 2, 1, 1, 1, 2, 1, 2, 7]
def baseStart_75652 : Nat := 118140960795 + 75652 * 2 ^ 59
def prefixEnd_75652 : Nat := 4983230072969 + 3 ^ 40 * 75652 * 2
def baseEnd_75652 : Nat := 25897225649362163268059

theorem tailTrace_75652 : CollatzResearch.WordTrace tailWord_75652 prefixEnd_75652 25897225649362163268059 := by
  unfold tailWord_75652
  simp only [CollatzResearch.WordTrace]
  refine ⟨1379627560966599589034605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1839503414622132785379473 1379627560966599589034605)
  ·
    refine ⟨517360335362474845887977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1379627560966599589034605 517360335362474845887977)
    ·
      refine ⟨388020251521856134415983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 517360335362474845887977 388020251521856134415983)
      ·
        refine ⟨582030377282784201623975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 388020251521856134415983 582030377282784201623975)
        ·
          refine ⟨873045565924176302435963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 582030377282784201623975 873045565924176302435963)
          ·
            refine ⟨1309568348886264453653945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 873045565924176302435963 1309568348886264453653945)
            ·
              refine ⟨982176261664698340240459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1309568348886264453653945 982176261664698340240459)
              ·
                refine ⟨1473264392497047510360689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 982176261664698340240459 1473264392497047510360689)
                ·
                  refine ⟨1104948294372785632770517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1473264392497047510360689 1104948294372785632770517)
                  ·
                    refine ⟨25897225649362163268059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1104948294372785632770517 25897225649362163268059)
                    ·
                      rfl

theorem cell22_75652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 1, 2, 7].length) (baseStart_75652 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_75652 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_75652 prefixEnd_75652 := by exact prefixLift 75652
  have htrace : WordTrace (prefixWord ++ tailWord_75652) baseStart_75652 baseEnd_75652 := by
    simpa [prefixWord, tailWord_75652, baseEnd_75652] using wordTrace_append hprefix tailTrace_75652
  have hstable : (prefixWord ++ tailWord_75652).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_75652).length < 2 ^ (prefixWord ++ tailWord_75652).sum := by decide
  have hdescent : baseEnd_75652 < baseStart_75652 := by decide
  rcases family_descends (prefixWord ++ tailWord_75652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_75656 : List Nat := [2, 1, 3, 3, 3, 1, 2, 1, 2, 4]
def baseStart_75656 : Nat := 118140960795 + 75656 * 2 ^ 59
def prefixEnd_75656 : Nat := 4983230072969 + 3 ^ 40 * 75656 * 2
def baseEnd_75656 : Nat := 25898594931107486168047

theorem tailTrace_75656 : CollatzResearch.WordTrace tailWord_75656 prefixEnd_75656 25898594931107486168047 := by
  unfold tailWord_75656
  simp only [CollatzResearch.WordTrace]
  refine ⟨1379700506959353930607411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1839600675945805240809881 1379700506959353930607411)
  ·
    refine ⟨2069550760439030895911117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1379700506959353930607411 2069550760439030895911117)
    ·
      refine ⟨776081535164636585966669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2069550760439030895911117 776081535164636585966669)
      ·
        refine ⟨291030575686738719737501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 776081535164636585966669 291030575686738719737501)
        ·
          refine ⟨109136465882527019901563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 291030575686738719737501 109136465882527019901563)
          ·
            refine ⟨163704698823790529852345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109136465882527019901563 163704698823790529852345)
            ·
              refine ⟨122778524117842897389259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 163704698823790529852345 122778524117842897389259)
              ·
                refine ⟨184167786176764346083889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 122778524117842897389259 184167786176764346083889)
                ·
                  refine ⟨138125839632573259562917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 184167786176764346083889 138125839632573259562917)
                  ·
                    refine ⟨25898594931107486168047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 138125839632573259562917 25898594931107486168047)
                    ·
                      rfl

theorem cell22_75656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 2, 1, 2, 4].length) (baseStart_75656 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_75656 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_75656 prefixEnd_75656 := by exact prefixLift 75656
  have htrace : WordTrace (prefixWord ++ tailWord_75656) baseStart_75656 baseEnd_75656 := by
    simpa [prefixWord, tailWord_75656, baseEnd_75656] using wordTrace_append hprefix tailTrace_75656
  have hstable : (prefixWord ++ tailWord_75656).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_75656).length < 2 ^ (prefixWord ++ tailWord_75656).sum := by decide
  have hdescent : baseEnd_75656 < baseStart_75656 := by decide
  rcases family_descends (prefixWord ++ tailWord_75656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_75688 : List Nat := [2, 1, 6, 2, 1, 2, 1, 7]
def baseStart_75688 : Nat := 118140960795 + 75688 * 2 ^ 59
def prefixEnd_75688 : Nat := 4983230072969 + 3 ^ 40 * 75688 * 2
def baseEnd_75688 : Nat := 2878838798341118818661

theorem tailTrace_75688 : CollatzResearch.WordTrace tailWord_75688 prefixEnd_75688 2878838798341118818661 := by
  unfold tailWord_75688
  simp only [CollatzResearch.WordTrace]
  refine ⟨1380284074901388663189859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1840378766535184884253145 1380284074901388663189859)
  ·
    refine ⟨2070426112352082994784789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1380284074901388663189859 2070426112352082994784789)
    ·
      refine ⟨97051224016503890380537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 2070426112352082994784789 97051224016503890380537)
      ·
        refine ⟨72788418012377917785403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97051224016503890380537 72788418012377917785403)
        ·
          refine ⟨109182627018566876678105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72788418012377917785403 109182627018566876678105)
          ·
            refine ⟨81886970263925157508579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 109182627018566876678105 81886970263925157508579)
            ·
              refine ⟨122830455395887736262869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81886970263925157508579 122830455395887736262869)
              ·
                refine ⟨2878838798341118818661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 122830455395887736262869 2878838798341118818661)
                ·
                  rfl

theorem cell22_75688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 2, 1, 7].length) (baseStart_75688 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_75688 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_75688 prefixEnd_75688 := by exact prefixLift 75688
  have htrace : WordTrace (prefixWord ++ tailWord_75688) baseStart_75688 baseEnd_75688 := by
    simpa [prefixWord, tailWord_75688, baseEnd_75688] using wordTrace_append hprefix tailTrace_75688
  have hstable : (prefixWord ++ tailWord_75688).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_75688).length < 2 ^ (prefixWord ++ tailWord_75688).sum := by decide
  have hdescent : baseEnd_75688 < baseStart_75688 := by decide
  rcases family_descends (prefixWord ++ tailWord_75688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_75727 : List Nat := [1, 1, 2, 1, 1, 5, 1, 2, 8]
def baseStart_75727 : Nat := 118140960795 + 75727 * 2 ^ 59
def prefixEnd_75727 : Nat := 4983230072969 + 3 ^ 40 * 75727 * 2
def baseEnd_75727 : Nat := 8640966560695655880943

theorem tailTrace_75727 : CollatzResearch.WordTrace tailWord_75727 prefixEnd_75727 8640966560695655880943 := by
  unfold tailWord_75727
  simp only [CollatzResearch.WordTrace]
  refine ⟨2761990596661486987049435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1841327064440991324699623 2761990596661486987049435)
  ·
    refine ⟨4142985894992230480574153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2761990596661486987049435 4142985894992230480574153)
    ·
      refine ⟨3107239421244172860430615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4142985894992230480574153 3107239421244172860430615)
      ·
        refine ⟨4660859131866259290645923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3107239421244172860430615 4660859131866259290645923)
        ·
          refine ⟨6991288697799388935968885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4660859131866259290645923 6991288697799388935968885)
          ·
            refine ⟨655433315418692712747083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6991288697799388935968885 655433315418692712747083)
            ·
              refine ⟨983149973128039069120625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 655433315418692712747083 983149973128039069120625)
              ·
                refine ⟨737362479846029301840469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 983149973128039069120625 737362479846029301840469)
                ·
                  refine ⟨8640966560695655880943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 737362479846029301840469 8640966560695655880943)
                  ·
                    rfl

theorem cell22_75727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 2, 8].length) (baseStart_75727 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_75727 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_75727 prefixEnd_75727 := by exact prefixLift 75727
  have htrace : WordTrace (prefixWord ++ tailWord_75727) baseStart_75727 baseEnd_75727 := by
    simpa [prefixWord, tailWord_75727, baseEnd_75727] using wordTrace_append hprefix tailTrace_75727
  have hstable : (prefixWord ++ tailWord_75727).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_75727).length < 2 ^ (prefixWord ++ tailWord_75727).sum := by decide
  have hdescent : baseEnd_75727 < baseStart_75727 := by decide
  rcases family_descends (prefixWord ++ tailWord_75727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_75849 : List Nat := [1, 2, 1, 1, 2, 2, 4, 2, 2, 5]
def baseStart_75849 : Nat := 118140960795 + 75849 * 2 ^ 59
def prefixEnd_75849 : Nat := 4983230072969 + 3 ^ 40 * 75849 * 2
def baseEnd_75849 : Nat := 25964662775319316092455

theorem tailTrace_75849 : CollatzResearch.WordTrace tailWord_75849 prefixEnd_75849 25964662775319316092455 := by
  unfold tailWord_75849
  simp only [CollatzResearch.WordTrace]
  refine ⟨2766440302219501822990601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1844293534813001215327067 2766440302219501822990601)
  ·
    refine ⟨2074830226664626367242951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2766440302219501822990601 2074830226664626367242951)
    ·
      refine ⟨3112245339996939550864427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2074830226664626367242951 3112245339996939550864427)
      ·
        refine ⟨4668368009995409326296641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3112245339996939550864427 4668368009995409326296641)
        ·
          refine ⟨3501276007496556994722481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4668368009995409326296641 3501276007496556994722481)
          ·
            refine ⟨2625957005622417746041861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3501276007496556994722481 2625957005622417746041861)
            ·
              refine ⟨492366938554203327382849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2625957005622417746041861 492366938554203327382849)
              ·
                refine ⟨369275203915652495537137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 492366938554203327382849 369275203915652495537137)
                ·
                  refine ⟨276956402936739371652853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 369275203915652495537137 276956402936739371652853)
                  ·
                    refine ⟨25964662775319316092455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 276956402936739371652853 25964662775319316092455)
                    ·
                      rfl

theorem cell22_75849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 2, 2, 5].length) (baseStart_75849 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_75849 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_75849 prefixEnd_75849 := by exact prefixLift 75849
  have htrace : WordTrace (prefixWord ++ tailWord_75849) baseStart_75849 baseEnd_75849 := by
    simpa [prefixWord, tailWord_75849, baseEnd_75849] using wordTrace_append hprefix tailTrace_75849
  have hstable : (prefixWord ++ tailWord_75849).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_75849).length < 2 ^ (prefixWord ++ tailWord_75849).sum := by decide
  have hdescent : baseEnd_75849 < baseStart_75849 := by decide
  rcases family_descends (prefixWord ++ tailWord_75849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_75881 : List Nat := [1, 2, 1, 1, 1, 5, 2, 4, 1, 4]
def baseStart_75881 : Nat := 118140960795 + 75881 * 2 ^ 59
def prefixEnd_75881 : Nat := 4983230072969 + 3 ^ 40 * 75881 * 2
def baseEnd_75881 : Nat := 25975617029281899292357

theorem tailTrace_75881 : CollatzResearch.WordTrace tailWord_75881 prefixEnd_75881 25975617029281899292357 := by
  unfold tailWord_75881
  simp only [CollatzResearch.WordTrace]
  refine ⟨2767607438103571288155497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1845071625402380858770331 2767607438103571288155497)
  ·
    refine ⟨2075705578577678466116623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2767607438103571288155497 2075705578577678466116623)
    ·
      refine ⟨3113558367866517699174935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2075705578577678466116623 3113558367866517699174935)
      ·
        refine ⟨4670337551799776548762403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3113558367866517699174935 4670337551799776548762403)
        ·
          refine ⟨7005506327699664823143605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4670337551799776548762403 7005506327699664823143605)
          ·
            refine ⟨656766218221843577169713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7005506327699664823143605 656766218221843577169713)
            ·
              refine ⟨492574663666382682877285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 656766218221843577169713 492574663666382682877285)
              ·
                refine ⟨92357749437446753039491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 492574663666382682877285 92357749437446753039491)
                ·
                  refine ⟨138536624156170129559237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 92357749437446753039491 138536624156170129559237)
                  ·
                    refine ⟨25975617029281899292357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 138536624156170129559237 25975617029281899292357)
                    ·
                      rfl

theorem cell22_75881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 4, 1, 4].length) (baseStart_75881 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_75881 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_75881 prefixEnd_75881 := by exact prefixLift 75881
  have htrace : WordTrace (prefixWord ++ tailWord_75881) baseStart_75881 baseEnd_75881 := by
    simpa [prefixWord, tailWord_75881, baseEnd_75881] using wordTrace_append hprefix tailTrace_75881
  have hstable : (prefixWord ++ tailWord_75881).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_75881).length < 2 ^ (prefixWord ++ tailWord_75881).sum := by decide
  have hdescent : baseEnd_75881 < baseStart_75881 := by decide
  rcases family_descends (prefixWord ++ tailWord_75881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_75973 : List Nat := [1, 3, 1, 1, 1, 1, 7, 1, 3, 3]
def baseStart_75973 : Nat := 118140960795 + 75973 * 2 ^ 59
def prefixEnd_75973 : Nat := 4983230072969 + 3 ^ 40 * 75973 * 2
def baseEnd_75973 : Nat := 26007110509424325992075

theorem tailTrace_75973 : CollatzResearch.WordTrace tailWord_75973 prefixEnd_75973 26007110509424325992075 := by
  unfold tailWord_75973
  simp only [CollatzResearch.WordTrace]
  refine ⟨2770962953770271000504573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1847308635846847333669715 2770962953770271000504573)
  ·
    refine ⟨1039111107663851625189215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2770962953770271000504573 1039111107663851625189215)
    ·
      refine ⟨1558666661495777437783823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1039111107663851625189215 1558666661495777437783823)
      ·
        refine ⟨2337999992243666156675735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1558666661495777437783823 2337999992243666156675735)
        ·
          refine ⟨3506999988365499235013603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2337999992243666156675735 3506999988365499235013603)
          ·
            refine ⟨5260499982548248852520405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3506999988365499235013603 5260499982548248852520405)
            ·
              refine ⟨123292968340974582480947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 5260499982548248852520405 123292968340974582480947)
              ·
                refine ⟨184939452511461873721421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 123292968340974582480947 184939452511461873721421)
                ·
                  refine ⟨69352294691798202645533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 184939452511461873721421 69352294691798202645533)
                  ·
                    refine ⟨26007110509424325992075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 69352294691798202645533 26007110509424325992075)
                    ·
                      rfl

theorem cell22_75973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 7, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 7, 1, 3, 3].length) (baseStart_75973 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_75973 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_75973 prefixEnd_75973 := by exact prefixLift 75973
  have htrace : WordTrace (prefixWord ++ tailWord_75973) baseStart_75973 baseEnd_75973 := by
    simpa [prefixWord, tailWord_75973, baseEnd_75973] using wordTrace_append hprefix tailTrace_75973
  have hstable : (prefixWord ++ tailWord_75973).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_75973).length < 2 ^ (prefixWord ++ tailWord_75973).sum := by decide
  have hdescent : baseEnd_75973 < baseStart_75973 := by decide
  rcases family_descends (prefixWord ++ tailWord_75973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76031 : List Nat := [1, 1, 2, 2, 1, 4, 2, 3, 6]
def baseStart_76031 : Nat := 118140960795 + 76031 * 2 ^ 59
def prefixEnd_76031 : Nat := 4983230072969 + 3 ^ 40 * 76031 * 2
def baseEnd_76031 : Nat := 8675655031577169347299

theorem tailTrace_76031 : CollatzResearch.WordTrace tailWord_76031 prefixEnd_76031 8675655031577169347299 := by
  unfold tailWord_76031
  simp only [CollatzResearch.WordTrace]
  refine ⟨2773078387560146906115947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1848718925040097937410631 2773078387560146906115947)
  ·
    refine ⟨4159617581340220359173921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2773078387560146906115947 4159617581340220359173921)
    ·
      refine ⟨3119713186005165269380441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4159617581340220359173921 3119713186005165269380441)
      ·
        refine ⟨2339784889503873952035331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3119713186005165269380441 2339784889503873952035331)
        ·
          refine ⟨3509677334255810928052997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2339784889503873952035331 3509677334255810928052997)
          ·
            refine ⟨658064500172964549009937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3509677334255810928052997 658064500172964549009937)
            ·
              refine ⟨493548375129723411757453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 658064500172964549009937 493548375129723411757453)
              ·
                refine ⟨185080640673646279409045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 493548375129723411757453 185080640673646279409045)
                ·
                  refine ⟨8675655031577169347299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 185080640673646279409045 8675655031577169347299)
                  ·
                    rfl

theorem cell22_76031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 3, 6].length) (baseStart_76031 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_76031 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_76031 prefixEnd_76031 := by exact prefixLift 76031
  have htrace : WordTrace (prefixWord ++ tailWord_76031) baseStart_76031 baseEnd_76031 := by
    simpa [prefixWord, tailWord_76031, baseEnd_76031] using wordTrace_append hprefix tailTrace_76031
  have hstable : (prefixWord ++ tailWord_76031).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76031).length < 2 ^ (prefixWord ++ tailWord_76031).sum := by decide
  have hdescent : baseEnd_76031 < baseStart_76031 := by decide
  rcases family_descends (prefixWord ++ tailWord_76031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76063 : List Nat := [1, 1, 2, 4, 3, 1, 2, 2, 1, 5]
def baseStart_76063 : Nat := 118140960795 + 76063 * 2 ^ 59
def prefixEnd_76063 : Nat := 4983230072969 + 3 ^ 40 * 76063 * 2
def baseEnd_76063 : Nat := 26037919348694091241799

theorem tailTrace_76063 : CollatzResearch.WordTrace tailWord_76063 prefixEnd_76063 26037919348694091241799 := by
  unfold tailWord_76063
  simp only [CollatzResearch.WordTrace]
  refine ⟨2774245523444216371280843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1849497015629477580853895 2774245523444216371280843)
  ·
    refine ⟨4161368285166324556921265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2774245523444216371280843 4161368285166324556921265)
    ·
      refine ⟨3121026213874743417690949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4161368285166324556921265 3121026213874743417690949)
      ·
        refine ⟨585192415101514390817053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3121026213874743417690949 585192415101514390817053)
        ·
          refine ⟨219447155663067896556395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 585192415101514390817053 219447155663067896556395)
          ·
            refine ⟨329170733494601844834593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 219447155663067896556395 329170733494601844834593)
            ·
              refine ⟨246878050120951383625945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 329170733494601844834593 246878050120951383625945)
              ·
                refine ⟨185158537590713537719459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 246878050120951383625945 185158537590713537719459)
                ·
                  refine ⟨277737806386070306579189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 185158537590713537719459 277737806386070306579189)
                  ·
                    refine ⟨26037919348694091241799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 277737806386070306579189 26037919348694091241799)
                    ·
                      rfl

theorem cell22_76063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 2, 2, 1, 5].length) (baseStart_76063 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_76063 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_76063 prefixEnd_76063 := by exact prefixLift 76063
  have htrace : WordTrace (prefixWord ++ tailWord_76063) baseStart_76063 baseEnd_76063 := by
    simpa [prefixWord, tailWord_76063, baseEnd_76063] using wordTrace_append hprefix tailTrace_76063
  have hstable : (prefixWord ++ tailWord_76063).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76063).length < 2 ^ (prefixWord ++ tailWord_76063).sum := by decide
  have hdescent : baseEnd_76063 < baseStart_76063 := by decide
  rcases family_descends (prefixWord ++ tailWord_76063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76071 : List Nat := [1, 1, 8, 1, 2, 1, 1, 2, 5]
def baseStart_76071 : Nat := 118140960795 + 76071 * 2 ^ 59
def prefixEnd_76071 : Nat := 4983230072969 + 3 ^ 40 * 76071 * 2
def baseEnd_76071 : Nat := 8680219304061579013925

theorem tailTrace_76071 : CollatzResearch.WordTrace tailWord_76071 prefixEnd_76071 8680219304061579013925 := by
  unfold tailWord_76071
  simp only [CollatzResearch.WordTrace]
  refine ⟨2774537307415233737572067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1849691538276822491714711 2774537307415233737572067)
  ·
    refine ⟨4161805961122850606358101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2774537307415233737572067 4161805961122850606358101)
    ·
      refine ⟨48771163606908405543259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 4161805961122850606358101 48771163606908405543259)
      ·
        refine ⟨73156745410362608314889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48771163606908405543259 73156745410362608314889)
        ·
          refine ⟨54867559057771956236167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73156745410362608314889 54867559057771956236167)
          ·
            refine ⟨82301338586657934354251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54867559057771956236167 82301338586657934354251)
            ·
              refine ⟨123452007879986901531377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82301338586657934354251 123452007879986901531377)
              ·
                refine ⟨92589005909990176148533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 123452007879986901531377 92589005909990176148533)
                ·
                  refine ⟨8680219304061579013925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 92589005909990176148533 8680219304061579013925)
                  ·
                    rfl

theorem cell22_76071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 1, 1, 2, 5].length) (baseStart_76071 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_76071 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_76071 prefixEnd_76071 := by exact prefixLift 76071
  have htrace : WordTrace (prefixWord ++ tailWord_76071) baseStart_76071 baseEnd_76071 := by
    simpa [prefixWord, tailWord_76071, baseEnd_76071] using wordTrace_append hprefix tailTrace_76071
  have hstable : (prefixWord ++ tailWord_76071).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76071).length < 2 ^ (prefixWord ++ tailWord_76071).sum := by decide
  have hdescent : baseEnd_76071 < baseStart_76071 := by decide
  rcases family_descends (prefixWord ++ tailWord_76071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76097 : List Nat := [1, 2, 5, 2, 2, 2, 1, 1, 1, 5]
def baseStart_76097 : Nat := 118140960795 + 76097 * 2 ^ 59
def prefixEnd_76097 : Nat := 4983230072969 + 3 ^ 40 * 76097 * 2
def baseEnd_76097 : Nat := 26049558243529335891695

theorem tailTrace_76097 : CollatzResearch.WordTrace tailWord_76097 prefixEnd_76097 26049558243529335891695 := by
  unfold tailWord_76097
  simp only [CollatzResearch.WordTrace]
  refine ⟨2775485605321040178018545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1850323736880693452012363 2775485605321040178018545)
  ·
    refine ⟨2081614203990780133513909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2775485605321040178018545 2081614203990780133513909)
    ·
      refine ⟨195151331624135637516929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2081614203990780133513909 195151331624135637516929)
      ·
        refine ⟨146363498718101728137697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 195151331624135637516929 146363498718101728137697)
        ·
          refine ⟨109772624038576296103273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 146363498718101728137697 109772624038576296103273)
          ·
            refine ⟨82329468028932222077455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 109772624038576296103273 82329468028932222077455)
            ·
              refine ⟨123494202043398333116183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82329468028932222077455 123494202043398333116183)
              ·
                refine ⟨185241303065097499674275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 123494202043398333116183 185241303065097499674275)
                ·
                  refine ⟨277861954597646249511413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 185241303065097499674275 277861954597646249511413)
                  ·
                    refine ⟨26049558243529335891695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 277861954597646249511413 26049558243529335891695)
                    ·
                      rfl

theorem cell22_76097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 2, 1, 1, 1, 5].length) (baseStart_76097 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_76097 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_76097 prefixEnd_76097 := by exact prefixLift 76097
  have htrace : WordTrace (prefixWord ++ tailWord_76097) baseStart_76097 baseEnd_76097 := by
    simpa [prefixWord, tailWord_76097, baseEnd_76097] using wordTrace_append hprefix tailTrace_76097
  have hstable : (prefixWord ++ tailWord_76097).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76097).length < 2 ^ (prefixWord ++ tailWord_76097).sum := by decide
  have hdescent : baseEnd_76097 < baseStart_76097 := by decide
  rcases family_descends (prefixWord ++ tailWord_76097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76155 : List Nat := [1, 1, 1, 1, 1, 7, 4, 1, 5]
def baseStart_76155 : Nat := 118140960795 + 76155 * 2 ^ 59
def prefixEnd_76155 : Nat := 4983230072969 + 3 ^ 40 * 76155 * 2
def baseEnd_76155 : Nat := 8689804276278839313839

theorem tailTrace_76155 : CollatzResearch.WordTrace tailWord_76155 prefixEnd_76155 8689804276278839313839 := by
  unfold tailWord_76155
  simp only [CollatzResearch.WordTrace]
  refine ⟨2777601039110916083629919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1851734026073944055753279 2777601039110916083629919)
  ·
    refine ⟨4166401558666374125444879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2777601039110916083629919 4166401558666374125444879)
    ·
      refine ⟨6249602337999561188167319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4166401558666374125444879 6249602337999561188167319)
      ·
        refine ⟨9374403506999341782250979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6249602337999561188167319 9374403506999341782250979)
        ·
          refine ⟨14061605260499012673376469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9374403506999341782250979 14061605260499012673376469)
          ·
            refine ⟨329568873292945609532261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 14061605260499012673376469 329568873292945609532261)
            ·
              refine ⟨61794163742427301787299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 329568873292945609532261 61794163742427301787299)
              ·
                refine ⟨92691245613640952680949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61794163742427301787299 92691245613640952680949)
                ·
                  refine ⟨8689804276278839313839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 92691245613640952680949 8689804276278839313839)
                  ·
                    rfl

theorem cell22_76155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 4, 1, 5].length) (baseStart_76155 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_76155 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_76155 prefixEnd_76155 := by exact prefixLift 76155
  have htrace : WordTrace (prefixWord ++ tailWord_76155) baseStart_76155 baseEnd_76155 := by
    simpa [prefixWord, tailWord_76155, baseEnd_76155] using wordTrace_append hprefix tailTrace_76155
  have hstable : (prefixWord ++ tailWord_76155).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76155).length < 2 ^ (prefixWord ++ tailWord_76155).sum := by decide
  have hdescent : baseEnd_76155 < baseStart_76155 := by decide
  rcases family_descends (prefixWord ++ tailWord_76155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76193 : List Nat := [1, 2, 3, 5, 1, 2, 2, 2, 1, 3]
def baseStart_76193 : Nat := 118140960795 + 76193 * 2 ^ 59
def prefixEnd_76193 : Nat := 4983230072969 + 3 ^ 40 * 76193 * 2
def baseEnd_76193 : Nat := 26082421005417085491401

theorem tailTrace_76193 : CollatzResearch.WordTrace tailWord_76193 prefixEnd_76193 26082421005417085491401 := by
  unfold tailWord_76193
  simp only [CollatzResearch.WordTrace]
  refine ⟨2778987012973248573513233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1852658008648832382342155 2778987012973248573513233)
  ·
    refine ⟨2084240259729936430134925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2778987012973248573513233 2084240259729936430134925)
    ·
      refine ⟨781590097398726161300597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2084240259729936430134925 781590097398726161300597)
      ·
        refine ⟨73274071631130577621931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 781590097398726161300597 73274071631130577621931)
        ·
          refine ⟨109911107446695866432897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73274071631130577621931 109911107446695866432897)
          ·
            refine ⟨82433330585021899824673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 109911107446695866432897 82433330585021899824673)
            ·
              refine ⟨61824997938766424868505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82433330585021899824673 61824997938766424868505)
              ·
                refine ⟨46368748454074818651379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61824997938766424868505 46368748454074818651379)
                ·
                  refine ⟨69553122681112227977069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46368748454074818651379 69553122681112227977069)
                  ·
                    refine ⟨26082421005417085491401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 69553122681112227977069 26082421005417085491401)
                    ·
                      rfl

theorem cell22_76193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 2, 2, 2, 1, 3].length) (baseStart_76193 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_76193 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_76193 prefixEnd_76193 := by exact prefixLift 76193
  have htrace : WordTrace (prefixWord ++ tailWord_76193) baseStart_76193 baseEnd_76193 := by
    simpa [prefixWord, tailWord_76193, baseEnd_76193] using wordTrace_append hprefix tailTrace_76193
  have hstable : (prefixWord ++ tailWord_76193).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76193).length < 2 ^ (prefixWord ++ tailWord_76193).sum := by decide
  have hdescent : baseEnd_76193 < baseStart_76193 := by decide
  rcases family_descends (prefixWord ++ tailWord_76193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76215 : List Nat := [1, 1, 3, 1, 3, 4, 2, 1, 1, 5]
def baseStart_76215 : Nat := 118140960795 + 76215 * 2 ^ 59
def prefixEnd_76215 : Nat := 4983230072969 + 3 ^ 40 * 76215 * 2
def baseEnd_76215 : Nat := 26089952055016361441333

theorem tailTrace_76215 : CollatzResearch.WordTrace tailWord_76215 prefixEnd_76215 26089952055016361441333 := by
  unfold tailWord_76215
  simp only [CollatzResearch.WordTrace]
  refine ⟨2779789418893546330814099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1853192945929030887209399 2779789418893546330814099)
  ·
    refine ⟨4169684128340319496221149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2779789418893546330814099 4169684128340319496221149)
    ·
      refine ⟨1563631548127619811082931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4169684128340319496221149 1563631548127619811082931)
      ·
        refine ⟨2345447322191429716624397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1563631548127619811082931 2345447322191429716624397)
        ·
          refine ⟨879542745821786143734149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2345447322191429716624397 879542745821786143734149)
          ·
            refine ⟨164914264841584901950153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 879542745821786143734149 164914264841584901950153)
            ·
              refine ⟨123685698631188676462615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 164914264841584901950153 123685698631188676462615)
              ·
                refine ⟨185528547946783014693923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 123685698631188676462615 185528547946783014693923)
                ·
                  refine ⟨278292821920174522040885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 185528547946783014693923 278292821920174522040885)
                  ·
                    refine ⟨26089952055016361441333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 278292821920174522040885 26089952055016361441333)
                    ·
                      rfl

theorem cell22_76215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 2, 1, 1, 5].length) (baseStart_76215 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_76215 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_76215 prefixEnd_76215 := by exact prefixLift 76215
  have htrace : WordTrace (prefixWord ++ tailWord_76215) baseStart_76215 baseEnd_76215 := by
    simpa [prefixWord, tailWord_76215, baseEnd_76215] using wordTrace_append hprefix tailTrace_76215
  have hstable : (prefixWord ++ tailWord_76215).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76215).length < 2 ^ (prefixWord ++ tailWord_76215).sum := by decide
  have hdescent : baseEnd_76215 < baseStart_76215 := by decide
  rcases family_descends (prefixWord ++ tailWord_76215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76236 : List Nat := [2, 2, 1, 4, 4, 1, 2, 1, 1, 4]
def baseStart_76236 : Nat := 118140960795 + 76236 * 2 ^ 59
def prefixEnd_76236 : Nat := 4983230072969 + 3 ^ 40 * 76236 * 2
def baseEnd_76236 : Nat := 26097140784179306666269

theorem tailTrace_76236 : CollatzResearch.WordTrace tailWord_76236 prefixEnd_76236 26097140784179306666269 := by
  unfold tailWord_76236
  simp only [CollatzResearch.WordTrace]
  refine ⟨1390277675908733458664281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1853703567878311278219041 1390277675908733458664281)
  ·
    refine ⟨1042708256931550093998211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1390277675908733458664281 1042708256931550093998211)
    ·
      refine ⟨1564062385397325140997317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1042708256931550093998211 1564062385397325140997317)
      ·
        refine ⟨293261697261998463936997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1564062385397325140997317 293261697261998463936997)
        ·
          refine ⟨54986568236624711988187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 293261697261998463936997 54986568236624711988187)
          ·
            refine ⟨82479852354937067982281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54986568236624711988187 82479852354937067982281)
            ·
              refine ⟨61859889266202800986711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82479852354937067982281 61859889266202800986711)
              ·
                refine ⟨92789833899304201480067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61859889266202800986711 92789833899304201480067)
                ·
                  refine ⟨139184750848956302220101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 92789833899304201480067 139184750848956302220101)
                  ·
                    refine ⟨26097140784179306666269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 139184750848956302220101 26097140784179306666269)
                    ·
                      rfl

theorem cell22_76236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 1, 2, 1, 1, 4].length) (baseStart_76236 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_76236 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_76236 prefixEnd_76236 := by exact prefixLift 76236
  have htrace : WordTrace (prefixWord ++ tailWord_76236) baseStart_76236 baseEnd_76236 := by
    simpa [prefixWord, tailWord_76236, baseEnd_76236] using wordTrace_append hprefix tailTrace_76236
  have hstable : (prefixWord ++ tailWord_76236).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76236).length < 2 ^ (prefixWord ++ tailWord_76236).sum := by decide
  have hdescent : baseEnd_76236 < baseStart_76236 := by decide
  rcases family_descends (prefixWord ++ tailWord_76236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76311 : List Nat := [1, 1, 3, 6, 1, 2, 1, 1, 3, 3]
def baseStart_76311 : Nat := 118140960795 + 76311 * 2 ^ 59
def prefixEnd_76311 : Nat := 4983230072969 + 3 ^ 40 * 76311 * 2
def baseEnd_76311 : Nat := 26122814816904111041039

theorem tailTrace_76311 : CollatzResearch.WordTrace tailWord_76311 prefixEnd_76311 26122814816904111041039 := by
  unfold tailWord_76311
  simp only [CollatzResearch.WordTrace]
  refine ⟨2783290826545754726308787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1855527217697169817539191 2783290826545754726308787)
  ·
    refine ⟨4174936239818632089463181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2783290826545754726308787 4174936239818632089463181)
    ·
      refine ⟨1565601089931987033548693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4174936239818632089463181 1565601089931987033548693)
      ·
        refine ⟨73387551090561892197595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 1565601089931987033548693 73387551090561892197595)
        ·
          refine ⟨110081326635842838296393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73387551090561892197595 110081326635842838296393)
          ·
            refine ⟨82560994976882128722295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 110081326635842838296393 82560994976882128722295)
            ·
              refine ⟨123841492465323193083443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82560994976882128722295 123841492465323193083443)
              ·
                refine ⟨185762238697984789625165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 123841492465323193083443 185762238697984789625165)
                ·
                  refine ⟨69660839511744296109437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 185762238697984789625165 69660839511744296109437)
                  ·
                    refine ⟨26122814816904111041039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 69660839511744296109437 26122814816904111041039)
                    ·
                      rfl

theorem cell22_76311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 2, 1, 1, 3, 3].length) (baseStart_76311 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_76311 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_76311 prefixEnd_76311 := by exact prefixLift 76311
  have htrace : WordTrace (prefixWord ++ tailWord_76311) baseStart_76311 baseEnd_76311 := by
    simpa [prefixWord, tailWord_76311, baseEnd_76311] using wordTrace_append hprefix tailTrace_76311
  have hstable : (prefixWord ++ tailWord_76311).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76311).length < 2 ^ (prefixWord ++ tailWord_76311).sum := by decide
  have hdescent : baseEnd_76311 < baseStart_76311 := by decide
  rcases family_descends (prefixWord ++ tailWord_76311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76324 : List Nat := [2, 3, 1, 5, 1, 1, 1, 3, 5]
def baseStart_76324 : Nat := 118140960795 + 76324 * 2 ^ 59
def prefixEnd_76324 : Nat := 4983230072969 + 3 ^ 40 * 76324 * 2
def baseEnd_76324 : Nat := 8709088327525470155333

theorem tailTrace_76324 : CollatzResearch.WordTrace tailWord_76324 prefixEnd_76324 8709088327525470155333 := by
  unfold tailWord_76324
  simp only [CollatzResearch.WordTrace]
  refine ⟨1391882487749328973266013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1855843316999105297688017 1391882487749328973266013)
  ·
    refine ⟨521955932905998364974755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1391882487749328973266013 521955932905998364974755)
    ·
      refine ⟨782933899358997547462133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 521955932905998364974755 782933899358997547462133)
      ·
        refine ⟨73400053064906020074575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 782933899358997547462133 73400053064906020074575)
        ·
          refine ⟨110100079597359030111863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73400053064906020074575 110100079597359030111863)
          ·
            refine ⟨165150119396038545167795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110100079597359030111863 165150119396038545167795)
            ·
              refine ⟨247725179094057817751693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 165150119396038545167795 247725179094057817751693)
              ·
                refine ⟨92896942160271681656885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 247725179094057817751693 92896942160271681656885)
                ·
                  refine ⟨8709088327525470155333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 92896942160271681656885 8709088327525470155333)
                  ·
                    rfl

theorem cell22_76324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 1, 3, 5].length) (baseStart_76324 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_76324 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_76324 prefixEnd_76324 := by exact prefixLift 76324
  have htrace : WordTrace (prefixWord ++ tailWord_76324) baseStart_76324 baseEnd_76324 := by
    simpa [prefixWord, tailWord_76324, baseEnd_76324] using wordTrace_append hprefix tailTrace_76324
  have hstable : (prefixWord ++ tailWord_76324).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76324).length < 2 ^ (prefixWord ++ tailWord_76324).sum := by decide
  have hdescent : baseEnd_76324 < baseStart_76324 := by decide
  rcases family_descends (prefixWord ++ tailWord_76324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76337 : List Nat := [1, 2, 2, 3, 1, 1, 5, 2, 1, 4]
def baseStart_76337 : Nat := 118140960795 + 76337 * 2 ^ 59
def prefixEnd_76337 : Nat := 4983230072969 + 3 ^ 40 * 76337 * 2
def baseEnd_76337 : Nat := 26131715148248709890959

theorem tailTrace_76337 : CollatzResearch.WordTrace tailWord_76337 prefixEnd_76337 26131715148248709890959 := by
  unfold tailWord_76337
  simp only [CollatzResearch.WordTrace]
  refine ⟨2784239124451561166755265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1856159416301040777836843 2784239124451561166755265)
  ·
    refine ⟨2088179343338670875066449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2784239124451561166755265 2088179343338670875066449)
    ·
      refine ⟨1566134507504003156299837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2088179343338670875066449 1566134507504003156299837)
      ·
        refine ⟨587300440314001183612439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1566134507504003156299837 587300440314001183612439)
        ·
          refine ⟨880950660471001775418659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 587300440314001183612439 880950660471001775418659)
          ·
            refine ⟨1321425990706502663127989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 880950660471001775418659 1321425990706502663127989)
            ·
              refine ⟨123883686628734624668249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1321425990706502663127989 123883686628734624668249)
              ·
                refine ⟨92912764971550968501187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 123883686628734624668249 92912764971550968501187)
                ·
                  refine ⟨139369147457326452751781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 92912764971550968501187 139369147457326452751781)
                  ·
                    refine ⟨26131715148248709890959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 139369147457326452751781 26131715148248709890959)
                    ·
                      rfl

theorem cell22_76337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 5, 2, 1, 4].length) (baseStart_76337 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_76337 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_76337 prefixEnd_76337 := by exact prefixLift 76337
  have htrace : WordTrace (prefixWord ++ tailWord_76337) baseStart_76337 baseEnd_76337 := by
    simpa [prefixWord, tailWord_76337, baseEnd_76337] using wordTrace_append hprefix tailTrace_76337
  have hstable : (prefixWord ++ tailWord_76337).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76337).length < 2 ^ (prefixWord ++ tailWord_76337).sum := by decide
  have hdescent : baseEnd_76337 < baseStart_76337 := by decide
  rcases family_descends (prefixWord ++ tailWord_76337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76367 : List Nat := [1, 1, 2, 1, 1, 2, 5, 4, 2, 3]
def baseStart_76367 : Nat := 118140960795 + 76367 * 2 ^ 59
def prefixEnd_76367 : Nat := 4983230072969 + 3 ^ 40 * 76367 * 2
def baseEnd_76367 : Nat := 26141984761338631640867

theorem tailTrace_76367 : CollatzResearch.WordTrace tailWord_76367 prefixEnd_76367 26141984761338631640867 := by
  unfold tailWord_76367
  simp only [CollatzResearch.WordTrace]
  refine ⟨2785333314342876290347355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1856888876228584193564903 2785333314342876290347355)
  ·
    refine ⟨4177999971514314435521033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2785333314342876290347355 4177999971514314435521033)
    ·
      refine ⟨3133499978635735826640775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4177999971514314435521033 3133499978635735826640775)
      ·
        refine ⟨4700249967953603739961163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3133499978635735826640775 4700249967953603739961163)
        ·
          refine ⟨7050374951930405609941745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4700249967953603739961163 7050374951930405609941745)
          ·
            refine ⟨5287781213947804207456309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7050374951930405609941745 5287781213947804207456309)
            ·
              refine ⟨495729488807606644449029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5287781213947804207456309 495729488807606644449029)
              ·
                refine ⟨92949279151426245834193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 495729488807606644449029 92949279151426245834193)
                ·
                  refine ⟨69711959363569684375645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 92949279151426245834193 69711959363569684375645)
                  ·
                    refine ⟨26141984761338631640867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 69711959363569684375645 26141984761338631640867)
                    ·
                      rfl

theorem cell22_76367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 4, 2, 3].length) (baseStart_76367 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_76367 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_76367 prefixEnd_76367 := by exact prefixLift 76367
  have htrace : WordTrace (prefixWord ++ tailWord_76367) baseStart_76367 baseEnd_76367 := by
    simpa [prefixWord, tailWord_76367, baseEnd_76367] using wordTrace_append hprefix tailTrace_76367
  have hstable : (prefixWord ++ tailWord_76367).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76367).length < 2 ^ (prefixWord ++ tailWord_76367).sum := by decide
  have hdescent : baseEnd_76367 < baseStart_76367 := by decide
  rcases family_descends (prefixWord ++ tailWord_76367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76369 : List Nat := [1, 2, 2, 1, 3, 3, 4, 2, 4]
def baseStart_76369 : Nat := 118140960795 + 76369 * 2 ^ 59
def prefixEnd_76369 : Nat := 4983230072969 + 3 ^ 40 * 76369 * 2
def baseEnd_76369 : Nat := 8714223134070431030287

theorem tailTrace_76369 : CollatzResearch.WordTrace tailWord_76369 prefixEnd_76369 8714223134070431030287 := by
  unfold tailWord_76369
  simp only [CollatzResearch.WordTrace]
  refine ⟨2785406260335630631920161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1856937506890420421280107 2785406260335630631920161)
  ·
    refine ⟨2089054695251722973940121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2785406260335630631920161 2089054695251722973940121)
    ·
      refine ⟨1566791021438792230455091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2089054695251722973940121 1566791021438792230455091)
      ·
        refine ⟨2350186532158188345682637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1566791021438792230455091 2350186532158188345682637)
        ·
          refine ⟨881319949559320629630989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2350186532158188345682637 881319949559320629630989)
          ·
            refine ⟨330494981084745236111621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 881319949559320629630989 330494981084745236111621)
            ·
              refine ⟨61967808953389731770929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 330494981084745236111621 61967808953389731770929)
              ·
                refine ⟨46475856715042298828197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61967808953389731770929 46475856715042298828197)
                ·
                  refine ⟨8714223134070431030287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 46475856715042298828197 8714223134070431030287)
                  ·
                    rfl

theorem cell22_76369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 4, 2, 4].length) (baseStart_76369 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_76369 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_76369 prefixEnd_76369 := by exact prefixLift 76369
  have htrace : WordTrace (prefixWord ++ tailWord_76369) baseStart_76369 baseEnd_76369 := by
    simpa [prefixWord, tailWord_76369, baseEnd_76369] using wordTrace_append hprefix tailTrace_76369
  have hstable : (prefixWord ++ tailWord_76369).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76369).length < 2 ^ (prefixWord ++ tailWord_76369).sum := by decide
  have hdescent : baseEnd_76369 < baseStart_76369 := by decide
  rcases family_descends (prefixWord ++ tailWord_76369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76485 : List Nat := [1, 3, 1, 1, 1, 1, 2, 1, 2, 9]
def baseStart_76485 : Nat := 118140960795 + 76485 * 2 ^ 59
def prefixEnd_76485 : Nat := 4983230072969 + 3 ^ 40 * 76485 * 2
def baseEnd_76485 : Nat := 26182378572825657190505

theorem tailTrace_76485 : CollatzResearch.WordTrace tailWord_76485 prefixEnd_76485 26182378572825657190505 := by
  unfold tailWord_76485
  simp only [CollatzResearch.WordTrace]
  refine ⟨2789637127915382443142909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1859758085276921628761939 2789637127915382443142909)
  ·
    refine ⟨1046113922968268416178591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2789637127915382443142909 1046113922968268416178591)
    ·
      refine ⟨1569170884452402624267887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1046113922968268416178591 1569170884452402624267887)
      ·
        refine ⟨2353756326678603936401831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1569170884452402624267887 2353756326678603936401831)
        ·
          refine ⟨3530634490017905904602747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2353756326678603936401831 3530634490017905904602747)
          ·
            refine ⟨5295951735026858856904121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3530634490017905904602747 5295951735026858856904121)
            ·
              refine ⟨3971963801270144142678091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5295951735026858856904121 3971963801270144142678091)
              ·
                refine ⟨5957945701905216214017137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3971963801270144142678091 5957945701905216214017137)
                ·
                  refine ⟨4468459276428912160512853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5957945701905216214017137 4468459276428912160512853)
                  ·
                    refine ⟨26182378572825657190505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 4468459276428912160512853 26182378572825657190505)
                    ·
                      rfl

theorem cell22_76485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 1, 2, 9].length) (baseStart_76485 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_76485 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_76485 prefixEnd_76485 := by exact prefixLift 76485
  have htrace : WordTrace (prefixWord ++ tailWord_76485) baseStart_76485 baseEnd_76485 := by
    simpa [prefixWord, tailWord_76485, baseEnd_76485] using wordTrace_append hprefix tailTrace_76485
  have hstable : (prefixWord ++ tailWord_76485).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76485).length < 2 ^ (prefixWord ++ tailWord_76485).sum := by decide
  have hdescent : baseEnd_76485 < baseStart_76485 := by decide
  rcases family_descends (prefixWord ++ tailWord_76485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76534 : List Nat := [5, 1, 1, 1, 1, 2, 1, 4, 2, 4]
def baseStart_76534 : Nat := 118140960795 + 76534 * 2 ^ 59
def prefixEnd_76534 : Nat := 4983230072969 + 3 ^ 40 * 76534 * 2
def baseEnd_76534 : Nat := 26199152274205862715355

theorem tailTrace_76534 : CollatzResearch.WordTrace tailWord_76534 prefixEnd_76534 26199152274205862715355 := by
  unfold tailWord_76534
  simp only [CollatzResearch.WordTrace]
  refine ⟨174464019046116488229791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1860949536491909207784437 174464019046116488229791)
  ·
    refine ⟨261696028569174732344687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174464019046116488229791 261696028569174732344687)
    ·
      refine ⟨392544042853762098517031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 261696028569174732344687 392544042853762098517031)
      ·
        refine ⟨588816064280643147775547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 392544042853762098517031 588816064280643147775547)
        ·
          refine ⟨883224096420964721663321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 588816064280643147775547 883224096420964721663321)
          ·
            refine ⟨662418072315723541247491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 883224096420964721663321 662418072315723541247491)
            ·
              refine ⟨993627108473585311871237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 662418072315723541247491 993627108473585311871237)
              ·
                refine ⟨186305082838797245975857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 993627108473585311871237 186305082838797245975857)
                ·
                  refine ⟨139728812129097934481893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 186305082838797245975857 139728812129097934481893)
                  ·
                    refine ⟨26199152274205862715355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 139728812129097934481893 26199152274205862715355)
                    ·
                      rfl

theorem cell22_76534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 4, 2, 4].length) (baseStart_76534 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_76534 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_76534 prefixEnd_76534 := by exact prefixLift 76534
  have htrace : WordTrace (prefixWord ++ tailWord_76534) baseStart_76534 baseEnd_76534 := by
    simpa [prefixWord, tailWord_76534, baseEnd_76534] using wordTrace_append hprefix tailTrace_76534
  have hstable : (prefixWord ++ tailWord_76534).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76534).length < 2 ^ (prefixWord ++ tailWord_76534).sum := by decide
  have hdescent : baseEnd_76534 < baseStart_76534 := by decide
  rcases family_descends (prefixWord ++ tailWord_76534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76577 : List Nat := [1, 2, 3, 2, 1, 2, 2, 2, 7]
def baseStart_76577 : Nat := 118140960795 + 76577 * 2 ^ 59
def prefixEnd_76577 : Nat := 4983230072969 + 3 ^ 40 * 76577 * 2
def baseEnd_76577 : Nat := 8737957350989361296741

theorem tailTrace_76577 : CollatzResearch.WordTrace tailWord_76577 prefixEnd_76577 8737957350989361296741 := by
  unfold tailWord_76577
  simp only [CollatzResearch.WordTrace]
  refine ⟨2792992643582082155491985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1861995095721388103661323 2792992643582082155491985)
  ·
    refine ⟨2094744482686561616618989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2792992643582082155491985 2094744482686561616618989)
    ·
      refine ⟨785529181007460606232121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2094744482686561616618989 785529181007460606232121)
      ·
        refine ⟨589146885755595454674091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 785529181007460606232121 589146885755595454674091)
        ·
          refine ⟨883720328633393182011137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 589146885755595454674091 883720328633393182011137)
          ·
            refine ⟨662790246475044886508353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 883720328633393182011137 662790246475044886508353)
            ·
              refine ⟨497092684856283664881265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 662790246475044886508353 497092684856283664881265)
              ·
                refine ⟨372819513642212748660949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 497092684856283664881265 372819513642212748660949)
                ·
                  refine ⟨8737957350989361296741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 372819513642212748660949 8737957350989361296741)
                  ·
                    rfl

theorem cell22_76577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 2, 7].length) (baseStart_76577 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_76577 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_76577 prefixEnd_76577 := by exact prefixLift 76577
  have htrace : WordTrace (prefixWord ++ tailWord_76577) baseStart_76577 baseEnd_76577 := by
    simpa [prefixWord, tailWord_76577, baseEnd_76577] using wordTrace_append hprefix tailTrace_76577
  have hstable : (prefixWord ++ tailWord_76577).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76577).length < 2 ^ (prefixWord ++ tailWord_76577).sum := by decide
  have hdescent : baseEnd_76577 < baseStart_76577 := by decide
  rcases family_descends (prefixWord ++ tailWord_76577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76624 : List Nat := [2, 1, 1, 1, 1, 4, 3, 4, 1, 4]
def baseStart_76624 : Nat := 118140960795 + 76624 * 2 ^ 59
def prefixEnd_76624 : Nat := 4983230072969 + 3 ^ 40 * 76624 * 2
def baseEnd_76624 : Nat := 26229961113475627965079

theorem tailTrace_76624 : CollatzResearch.WordTrace tailWord_76624 prefixEnd_76624 26229961113475627965079 := by
  unfold tailWord_76624
  simp only [CollatzResearch.WordTrace]
  refine ⟨1397353437205904591226463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1863137916274539454968617 1397353437205904591226463)
  ·
    refine ⟨2096030155808856886839695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1397353437205904591226463 2096030155808856886839695)
    ·
      refine ⟨3144045233713285330259543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2096030155808856886839695 3144045233713285330259543)
      ·
        refine ⟨4716067850569927995389315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3144045233713285330259543 4716067850569927995389315)
        ·
          refine ⟨7074101775854891993083973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4716067850569927995389315 7074101775854891993083973)
          ·
            refine ⟨1326394082972792248703245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7074101775854891993083973 1326394082972792248703245)
            ·
              refine ⟨497397781114797093263717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1326394082972792248703245 497397781114797093263717)
              ·
                refine ⟨93262083959024454986947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 497397781114797093263717 93262083959024454986947)
                ·
                  refine ⟨139893125938536682480421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 93262083959024454986947 139893125938536682480421)
                  ·
                    refine ⟨26229961113475627965079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 139893125938536682480421 26229961113475627965079)
                    ·
                      rfl

theorem cell22_76624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 4, 1, 4].length) (baseStart_76624 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_76624 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_76624 prefixEnd_76624 := by exact prefixLift 76624
  have htrace : WordTrace (prefixWord ++ tailWord_76624) baseStart_76624 baseEnd_76624 := by
    simpa [prefixWord, tailWord_76624, baseEnd_76624] using wordTrace_append hprefix tailTrace_76624
  have hstable : (prefixWord ++ tailWord_76624).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76624).length < 2 ^ (prefixWord ++ tailWord_76624).sum := by decide
  have hdescent : baseEnd_76624 < baseStart_76624 := by decide
  rcases family_descends (prefixWord ++ tailWord_76624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76667 : List Nat := [1, 1, 1, 1, 1, 5, 3, 9]
def baseStart_76667 : Nat := 118140960795 + 76667 * 2 ^ 59
def prefixEnd_76667 : Nat := 4983230072969 + 3 ^ 40 * 76667 * 2
def baseEnd_76667 : Nat := 2916075654693094348883

theorem tailTrace_76667 : CollatzResearch.WordTrace tailWord_76667 prefixEnd_76667 2916075654693094348883 := by
  unfold tailWord_76667
  simp only [CollatzResearch.WordTrace]
  refine ⟨2796275213256027526268255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1864183475504018350845503 2796275213256027526268255)
  ·
    refine ⟨4194412819884041289402383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2796275213256027526268255 4194412819884041289402383)
    ·
      refine ⟨6291619229826061934103575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4194412819884041289402383 6291619229826061934103575)
      ·
        refine ⟨9437428844739092901155363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6291619229826061934103575 9437428844739092901155363)
        ·
          refine ⟨14156143267108639351733045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9437428844739092901155363 14156143267108639351733045)
          ·
            refine ⟨1327138431291434939224973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 14156143267108639351733045 1327138431291434939224973)
            ·
              refine ⟨497676911734288102209365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1327138431291434939224973 497676911734288102209365)
              ·
                refine ⟨2916075654693094348883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 497676911734288102209365 2916075654693094348883)
                ·
                  rfl

theorem cell22_76667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 9].length) (baseStart_76667 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_76667 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_76667 prefixEnd_76667 := by exact prefixLift 76667
  have htrace : WordTrace (prefixWord ++ tailWord_76667) baseStart_76667 baseEnd_76667 := by
    simpa [prefixWord, tailWord_76667, baseEnd_76667] using wordTrace_append hprefix tailTrace_76667
  have hstable : (prefixWord ++ tailWord_76667).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76667).length < 2 ^ (prefixWord ++ tailWord_76667).sum := by decide
  have hdescent : baseEnd_76667 < baseStart_76667 := by decide
  rcases family_descends (prefixWord ++ tailWord_76667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76733 : List Nat := [1, 4, 1, 2, 4, 1, 1, 2, 3, 3]
def baseStart_76733 : Nat := 118140960795 + 76733 * 2 ^ 59
def prefixEnd_76733 : Nat := 4983230072969 + 3 ^ 40 * 76733 * 2
def baseEnd_76733 : Nat := 26267274041035676989745

theorem tailTrace_76733 : CollatzResearch.WordTrace tailWord_76733 prefixEnd_76733 26267274041035676989745 := by
  unfold tailWord_76733
  simp only [CollatzResearch.WordTrace]
  refine ⟨2798682431016920798170853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1865788287344613865447235 2798682431016920798170853)
  ·
    refine ⟨524752955815672649657035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2798682431016920798170853 524752955815672649657035)
    ·
      refine ⟨787129433723508974485553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 524752955815672649657035 787129433723508974485553)
      ·
        refine ⟨590347075292631730864165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 787129433723508974485553 590347075292631730864165)
        ·
          refine ⟨110690076617368449537031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 590347075292631730864165 110690076617368449537031)
          ·
            refine ⟨166035114926052674305547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110690076617368449537031 166035114926052674305547)
            ·
              refine ⟨249052672389079011458321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 166035114926052674305547 249052672389079011458321)
              ·
                refine ⟨186789504291809258593741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 249052672389079011458321 186789504291809258593741)
                ·
                  refine ⟨70046064109428471972653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 186789504291809258593741 70046064109428471972653)
                  ·
                    refine ⟨26267274041035676989745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 70046064109428471972653 26267274041035676989745)
                    ·
                      rfl

theorem cell22_76733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 1, 2, 3, 3].length) (baseStart_76733 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_76733 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_76733 prefixEnd_76733 := by exact prefixLift 76733
  have htrace : WordTrace (prefixWord ++ tailWord_76733) baseStart_76733 baseEnd_76733 := by
    simpa [prefixWord, tailWord_76733, baseEnd_76733] using wordTrace_append hprefix tailTrace_76733
  have hstable : (prefixWord ++ tailWord_76733).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76733).length < 2 ^ (prefixWord ++ tailWord_76733).sum := by decide
  have hdescent : baseEnd_76733 < baseStart_76733 := by decide
  rcases family_descends (prefixWord ++ tailWord_76733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76750 : List Nat := [4, 1, 1, 1, 2, 4, 2, 3, 1, 3]
def baseStart_76750 : Nat := 118140960795 + 76750 * 2 ^ 59
def prefixEnd_76750 : Nat := 4983230072969 + 3 ^ 40 * 76750 * 2
def baseEnd_76750 : Nat := 26273093488453299314693

theorem tailTrace_76750 : CollatzResearch.WordTrace tailWord_76750 prefixEnd_76750 26273093488453299314693 := by
  unfold tailWord_76750
  simp only [CollatzResearch.WordTrace]
  refine ⟨349912808994416587692463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1866201647970221801026469 349912808994416587692463)
  ·
    refine ⟨524869213491624881538695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 349912808994416587692463 524869213491624881538695)
    ·
      refine ⟨787303820237437322308043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 524869213491624881538695 787303820237437322308043)
      ·
        refine ⟨1180955730356155983462065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 787303820237437322308043 1180955730356155983462065)
        ·
          refine ⟨885716797767116987596549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1180955730356155983462065 885716797767116987596549)
          ·
            refine ⟨166071899581334435174353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 885716797767116987596549 166071899581334435174353)
            ·
              refine ⟨124553924686000826380765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 166071899581334435174353 124553924686000826380765)
              ·
                refine ⟨46707721757250309892787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 124553924686000826380765 46707721757250309892787)
                ·
                  refine ⟨70061582635875464839181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46707721757250309892787 70061582635875464839181)
                  ·
                    refine ⟨26273093488453299314693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 70061582635875464839181 26273093488453299314693)
                    ·
                      rfl

theorem cell22_76750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 2, 3, 1, 3].length) (baseStart_76750 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_76750 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_76750 prefixEnd_76750 := by exact prefixLift 76750
  have htrace : WordTrace (prefixWord ++ tailWord_76750) baseStart_76750 baseEnd_76750 := by
    simpa [prefixWord, tailWord_76750, baseEnd_76750] using wordTrace_append hprefix tailTrace_76750
  have hstable : (prefixWord ++ tailWord_76750).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76750).length < 2 ^ (prefixWord ++ tailWord_76750).sum := by decide
  have hdescent : baseEnd_76750 < baseStart_76750 := by decide
  rcases family_descends (prefixWord ++ tailWord_76750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76759 : List Nat := [1, 1, 3, 2, 1, 1, 2, 2, 5, 4]
def baseStart_76759 : Nat := 118140960795 + 76759 * 2 ^ 59
def prefixEnd_76759 : Nat := 4983230072969 + 3 ^ 40 * 76759 * 2
def baseEnd_76759 : Nat := 26276174372380275839665

theorem tailTrace_76759 : CollatzResearch.WordTrace tailWord_76759 prefixEnd_76759 26276174372380275839665 := by
  unfold tailWord_76759
  simp only [CollatzResearch.WordTrace]
  refine ⟨2799630728922727238617331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1866420485948484825744887 2799630728922727238617331)
  ·
    refine ⟨4199446093384090857925997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2799630728922727238617331 4199446093384090857925997)
    ·
      refine ⟨1574792285019034071722249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4199446093384090857925997 1574792285019034071722249)
      ·
        refine ⟨1181094213764275553791687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1574792285019034071722249 1181094213764275553791687)
        ·
          refine ⟨1771641320646413330687531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1181094213764275553791687 1771641320646413330687531)
          ·
            refine ⟨2657461980969619996031297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1771641320646413330687531 2657461980969619996031297)
            ·
              refine ⟨1993096485727214997023473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2657461980969619996031297 1993096485727214997023473)
              ·
                refine ⟨1494822364295411247767605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1993096485727214997023473 1494822364295411247767605)
                ·
                  refine ⟨140139596652694804478213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1494822364295411247767605 140139596652694804478213)
                  ·
                    refine ⟨26276174372380275839665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 140139596652694804478213 26276174372380275839665)
                    ·
                      rfl

theorem cell22_76759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 2, 5, 4].length) (baseStart_76759 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_76759 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_76759 prefixEnd_76759 := by exact prefixLift 76759
  have htrace : WordTrace (prefixWord ++ tailWord_76759) baseStart_76759 baseEnd_76759 := by
    simpa [prefixWord, tailWord_76759, baseEnd_76759] using wordTrace_append hprefix tailTrace_76759
  have hstable : (prefixWord ++ tailWord_76759).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76759).length < 2 ^ (prefixWord ++ tailWord_76759).sum := by decide
  have hdescent : baseEnd_76759 < baseStart_76759 := by decide
  rcases family_descends (prefixWord ++ tailWord_76759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76808 : List Nat := [2, 1, 3, 2, 1, 3, 3, 3, 4]
def baseStart_76808 : Nat := 118140960795 + 76808 * 2 ^ 59
def prefixEnd_76808 : Nat := 4983230072969 + 3 ^ 40 * 76808 * 2
def baseEnd_76808 : Nat := 8764316024586827121505

theorem tailTrace_76808 : CollatzResearch.WordTrace tailWord_76808 prefixEnd_76808 8764316024586827121505 := by
  unfold tailWord_76808
  simp only [CollatzResearch.WordTrace]
  refine ⟨1400708952872604303575539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1867611937163472404767385 1400708952872604303575539)
  ·
    refine ⟨2101063429308906455363309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1400708952872604303575539 2101063429308906455363309)
    ·
      refine ⟨787898785990839920761241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2101063429308906455363309 787898785990839920761241)
      ·
        refine ⟨590924089493129940570931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 787898785990839920761241 590924089493129940570931)
        ·
          refine ⟨886386134239694910856397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 590924089493129940570931 886386134239694910856397)
          ·
            refine ⟨332394800339885591571149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 886386134239694910856397 332394800339885591571149)
            ·
              refine ⟨124648050127457096839181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 332394800339885591571149 124648050127457096839181)
              ·
                refine ⟨46743018797796411314693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 124648050127457096839181 46743018797796411314693)
                ·
                  refine ⟨8764316024586827121505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 46743018797796411314693 8764316024586827121505)
                  ·
                    rfl

theorem cell22_76808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 3, 3, 4].length) (baseStart_76808 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_76808 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_76808 prefixEnd_76808 := by exact prefixLift 76808
  have htrace : WordTrace (prefixWord ++ tailWord_76808) baseStart_76808 baseEnd_76808 := by
    simpa [prefixWord, tailWord_76808, baseEnd_76808] using wordTrace_append hprefix tailTrace_76808
  have hstable : (prefixWord ++ tailWord_76808).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76808).length < 2 ^ (prefixWord ++ tailWord_76808).sum := by decide
  have hdescent : baseEnd_76808 < baseStart_76808 := by decide
  rcases family_descends (prefixWord ++ tailWord_76808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76821 : List Nat := [1, 3, 2, 1, 4, 1, 1, 1, 4, 4]
def baseStart_76821 : Nat := 118140960795 + 76821 * 2 ^ 59
def prefixEnd_76821 : Nat := 4983230072969 + 3 ^ 40 * 76821 * 2
def baseEnd_76821 : Nat := 26297398239432780789475

theorem tailTrace_76821 : CollatzResearch.WordTrace tailWord_76821 prefixEnd_76821 26297398239432780789475 := by
  unfold tailWord_76821
  simp only [CollatzResearch.WordTrace]
  refine ⟨2801892054698111827374317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1867928036465407884916211 2801892054698111827374317)
  ·
    refine ⟨1050709520511791935265369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2801892054698111827374317 1050709520511791935265369)
    ·
      refine ⟨788032140383843951449027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1050709520511791935265369 788032140383843951449027)
      ·
        refine ⟨1182048210575765927173541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 788032140383843951449027 1182048210575765927173541)
        ·
          refine ⟨221634039482956111345039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1182048210575765927173541 221634039482956111345039)
          ·
            refine ⟨332451059224434167017559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 221634039482956111345039 332451059224434167017559)
            ·
              refine ⟨498676588836651250526339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 332451059224434167017559 498676588836651250526339)
              ·
                refine ⟨748014883254976875789509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 498676588836651250526339 748014883254976875789509)
                ·
                  refine ⟨140252790610308164210533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 748014883254976875789509 140252790610308164210533)
                  ·
                    refine ⟨26297398239432780789475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 140252790610308164210533 26297398239432780789475)
                    ·
                      rfl

theorem cell22_76821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 1, 4, 4].length) (baseStart_76821 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_76821 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_76821 prefixEnd_76821 := by exact prefixLift 76821
  have htrace : WordTrace (prefixWord ++ tailWord_76821) baseStart_76821 baseEnd_76821 := by
    simpa [prefixWord, tailWord_76821, baseEnd_76821] using wordTrace_append hprefix tailTrace_76821
  have hstable : (prefixWord ++ tailWord_76821).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76821).length < 2 ^ (prefixWord ++ tailWord_76821).sum := by decide
  have hdescent : baseEnd_76821 < baseStart_76821 := by decide
  rcases family_descends (prefixWord ++ tailWord_76821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76823 : List Nat := [1, 1, 3, 5, 1, 1, 2, 1, 4, 3]
def baseStart_76823 : Nat := 118140960795 + 76823 * 2 ^ 59
def prefixEnd_76823 : Nat := 4983230072969 + 3 ^ 40 * 76823 * 2
def baseEnd_76823 : Nat := 26298082880305442239469

theorem tailTrace_76823 : CollatzResearch.WordTrace tailWord_76823 prefixEnd_76823 26298082880305442239469 := by
  unfold tailWord_76823
  simp only [CollatzResearch.WordTrace]
  refine ⟨2801965000690866168947123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1867976667127244112631415 2801965000690866168947123)
  ·
    refine ⟨4202947501036299253420685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2801965000690866168947123 4202947501036299253420685)
    ·
      refine ⟨1576105312888612220032757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4202947501036299253420685 1576105312888612220032757)
      ·
        refine ⟨147759873083307395628071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1576105312888612220032757 147759873083307395628071)
        ·
          refine ⟨221639809624961093442107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147759873083307395628071 221639809624961093442107)
          ·
            refine ⟨332459714437441640163161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 221639809624961093442107 332459714437441640163161)
            ·
              refine ⟨249344785828081230122371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 332459714437441640163161 249344785828081230122371)
              ·
                refine ⟨374017178742121845183557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 249344785828081230122371 374017178742121845183557)
                ·
                  refine ⟨70128221014147845971917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 374017178742121845183557 70128221014147845971917)
                  ·
                    refine ⟨26298082880305442239469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 70128221014147845971917 26298082880305442239469)
                    ·
                      rfl

theorem cell22_76823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 2, 1, 4, 3].length) (baseStart_76823 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_76823 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_76823 prefixEnd_76823 := by exact prefixLift 76823
  have htrace : WordTrace (prefixWord ++ tailWord_76823) baseStart_76823 baseEnd_76823 := by
    simpa [prefixWord, tailWord_76823, baseEnd_76823] using wordTrace_append hprefix tailTrace_76823
  have hstable : (prefixWord ++ tailWord_76823).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76823).length < 2 ^ (prefixWord ++ tailWord_76823).sum := by decide
  have hdescent : baseEnd_76823 < baseStart_76823 := by decide
  rcases family_descends (prefixWord ++ tailWord_76823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76836 : List Nat := [2, 3, 1, 4, 1, 1, 1, 9]
def baseStart_76836 : Nat := 118140960795 + 76836 * 2 ^ 59
def prefixEnd_76836 : Nat := 4983230072969 + 3 ^ 40 * 76836 * 2
def baseEnd_76836 : Nat := 2922503671775304629381

theorem tailTrace_76836 : CollatzResearch.WordTrace tailWord_76836 prefixEnd_76836 2922503671775304629381 := by
  unfold tailWord_76836
  simp only [CollatzResearch.WordTrace]
  refine ⟨1401219574821884694585181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1868292766429179592780241 1401219574821884694585181)
  ·
    refine ⟨525457340558206760469443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1401219574821884694585181 525457340558206760469443)
    ·
      refine ⟨788186010837310140704165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 525457340558206760469443 788186010837310140704165)
      ·
        refine ⟨147784877031995651382031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 788186010837310140704165 147784877031995651382031)
        ·
          refine ⟨221677315547993477073047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147784877031995651382031 221677315547993477073047)
          ·
            refine ⟨332515973321990215609571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 221677315547993477073047 332515973321990215609571)
            ·
              refine ⟨498773959982985323414357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 332515973321990215609571 498773959982985323414357)
              ·
                refine ⟨2922503671775304629381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 498773959982985323414357 2922503671775304629381)
                ·
                  rfl

theorem cell22_76836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 9].length) (baseStart_76836 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_76836 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_76836 prefixEnd_76836 := by exact prefixLift 76836
  have htrace : WordTrace (prefixWord ++ tailWord_76836) baseStart_76836 baseEnd_76836 := by
    simpa [prefixWord, tailWord_76836, baseEnd_76836] using wordTrace_append hprefix tailTrace_76836
  have hstable : (prefixWord ++ tailWord_76836).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76836).length < 2 ^ (prefixWord ++ tailWord_76836).sum := by decide
  have hdescent : baseEnd_76836 < baseStart_76836 := by decide
  rcases family_descends (prefixWord ++ tailWord_76836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76851 : List Nat := [1, 1, 1, 2, 4, 1, 1, 3, 5, 3]
def baseStart_76851 : Nat := 118140960795 + 76851 * 2 ^ 59
def prefixEnd_76851 : Nat := 4983230072969 + 3 ^ 40 * 76851 * 2
def baseEnd_76851 : Nat := 26307667852522702539383

theorem tailTrace_76851 : CollatzResearch.WordTrace tailWord_76851 prefixEnd_76851 26307667852522702539383 := by
  unfold tailWord_76851
  simp only [CollatzResearch.WordTrace]
  refine ⟨2802986244589426950966407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1868657496392951300644271 2802986244589426950966407)
  ·
    refine ⟨4204479366884140426449611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2802986244589426950966407 4204479366884140426449611)
    ·
      refine ⟨6306719050326210639674417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4204479366884140426449611 6306719050326210639674417)
      ·
        refine ⟨4730039287744657979755813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6306719050326210639674417 4730039287744657979755813)
        ·
          refine ⟨886882366452123371204215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4730039287744657979755813 886882366452123371204215)
          ·
            refine ⟨1330323549678185056806323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 886882366452123371204215 1330323549678185056806323)
            ·
              refine ⟨1995485324517277585209485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1330323549678185056806323 1995485324517277585209485)
              ·
                refine ⟨748306996693979094453557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1995485324517277585209485 748306996693979094453557)
                ·
                  refine ⟨70153780940060540105021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 748306996693979094453557 70153780940060540105021)
                  ·
                    refine ⟨26307667852522702539383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 70153780940060540105021 26307667852522702539383)
                    ·
                      rfl

theorem cell22_76851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 3, 5, 3].length) (baseStart_76851 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_76851 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_76851 prefixEnd_76851 := by exact prefixLift 76851
  have htrace : WordTrace (prefixWord ++ tailWord_76851) baseStart_76851 baseEnd_76851 := by
    simpa [prefixWord, tailWord_76851, baseEnd_76851] using wordTrace_append hprefix tailTrace_76851
  have hstable : (prefixWord ++ tailWord_76851).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76851).length < 2 ^ (prefixWord ++ tailWord_76851).sum := by decide
  have hdescent : baseEnd_76851 < baseStart_76851 := by decide
  rcases family_descends (prefixWord ++ tailWord_76851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76881 : List Nat := [1, 2, 2, 1, 3, 1, 3, 4, 5]
def baseStart_76881 : Nat := 118140960795 + 76881 * 2 ^ 59
def prefixEnd_76881 : Nat := 4983230072969 + 3 ^ 40 * 76881 * 2
def baseEnd_76881 : Nat := 8772645821870874763097

theorem tailTrace_76881 : CollatzResearch.WordTrace tailWord_76881 prefixEnd_76881 8772645821870874763097 := by
  unfold tailWord_76881
  simp only [CollatzResearch.WordTrace]
  refine ⟨2804080434480742074558497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1869386956320494716372331 2804080434480742074558497)
  ·
    refine ⟨2103060325860556555918873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2804080434480742074558497 2103060325860556555918873)
    ·
      refine ⟨1577295244395417416939155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2103060325860556555918873 1577295244395417416939155)
      ·
        refine ⟨2365942866593126125408733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1577295244395417416939155 2365942866593126125408733)
        ·
          refine ⟨887228574972422297028275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2365942866593126125408733 887228574972422297028275)
          ·
            refine ⟨1330842862458633445542413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 887228574972422297028275 1330842862458633445542413)
            ·
              refine ⟨499066073421987542078405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1330842862458633445542413 499066073421987542078405)
              ·
                refine ⟨93574888766622664139701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 499066073421987542078405 93574888766622664139701)
                ·
                  refine ⟨8772645821870874763097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 93574888766622664139701 8772645821870874763097)
                  ·
                    rfl

theorem cell22_76881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 4, 5].length) (baseStart_76881 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_76881 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_76881 prefixEnd_76881 := by exact prefixLift 76881
  have htrace : WordTrace (prefixWord ++ tailWord_76881) baseStart_76881 baseEnd_76881 := by
    simpa [prefixWord, tailWord_76881, baseEnd_76881] using wordTrace_append hprefix tailTrace_76881
  have hstable : (prefixWord ++ tailWord_76881).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76881).length < 2 ^ (prefixWord ++ tailWord_76881).sum := by decide
  have hdescent : baseEnd_76881 < baseStart_76881 := by decide
  rcases family_descends (prefixWord ++ tailWord_76881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76885 : List Nat := [1, 3, 2, 2, 1, 2, 3, 4, 1, 3]
def baseStart_76885 : Nat := 118140960795 + 76885 * 2 ^ 59
def prefixEnd_76885 : Nat := 4983230072969 + 3 ^ 40 * 76885 * 2
def baseEnd_76885 : Nat := 26319306747357947189279

theorem tailTrace_76885 : CollatzResearch.WordTrace tailWord_76885 prefixEnd_76885 26319306747357947189279 := by
  unfold tailWord_76885
  simp only [CollatzResearch.WordTrace]
  refine ⟨2804226326466250757704109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1869484217644167171802739 2804226326466250757704109)
  ·
    refine ⟨1051584872424844034139041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2804226326466250757704109 1051584872424844034139041)
    ·
      refine ⟨788688654318633025604281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1051584872424844034139041 788688654318633025604281)
      ·
        refine ⟨591516490738974769203211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 788688654318633025604281 591516490738974769203211)
        ·
          refine ⟨887274736108462153804817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 591516490738974769203211 887274736108462153804817)
          ·
            refine ⟨665456052081346615353613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 887274736108462153804817 665456052081346615353613)
            ·
              refine ⟨249546019530504980757605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 665456052081346615353613 249546019530504980757605)
              ·
                refine ⟨46789878661969683892051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 249546019530504980757605 46789878661969683892051)
                ·
                  refine ⟨70184817992954525838077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46789878661969683892051 70184817992954525838077)
                  ·
                    refine ⟨26319306747357947189279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 70184817992954525838077 26319306747357947189279)
                    ·
                      rfl

theorem cell22_76885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 3, 4, 1, 3].length) (baseStart_76885 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_76885 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_76885 prefixEnd_76885 := by exact prefixLift 76885
  have htrace : WordTrace (prefixWord ++ tailWord_76885) baseStart_76885 baseEnd_76885 := by
    simpa [prefixWord, tailWord_76885, baseEnd_76885] using wordTrace_append hprefix tailTrace_76885
  have hstable : (prefixWord ++ tailWord_76885).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76885).length < 2 ^ (prefixWord ++ tailWord_76885).sum := by decide
  have hdescent : baseEnd_76885 < baseStart_76885 := by decide
  rcases family_descends (prefixWord ++ tailWord_76885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76896 : List Nat := [2, 1, 1, 3, 2, 2, 3, 1, 2, 5]
def baseStart_76896 : Nat := 118140960795 + 76896 * 2 ^ 59
def prefixEnd_76896 : Nat := 4983230072969 + 3 ^ 40 * 76896 * 2
def baseEnd_76896 : Nat := 26323072272157585164245

theorem tailTrace_76896 : CollatzResearch.WordTrace tailWord_76896 prefixEnd_76896 26323072272157585164245 := by
  unfold tailWord_76896
  simp only [CollatzResearch.WordTrace]
  refine ⟨1402313764713199818177271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1869751686284266424236361 1402313764713199818177271)
  ·
    refine ⟨2103470647069799727265907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1402313764713199818177271 2103470647069799727265907)
    ·
      refine ⟨3155205970604699590898861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2103470647069799727265907 3155205970604699590898861)
      ·
        refine ⟨1183202238976762346587073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3155205970604699590898861 1183202238976762346587073)
        ·
          refine ⟨887401679232571759940305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1183202238976762346587073 887401679232571759940305)
          ·
            refine ⟨665551259424428819955229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 887401679232571759940305 665551259424428819955229)
            ·
              refine ⟨249581722284160807483211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 665551259424428819955229 249581722284160807483211)
              ·
                refine ⟨374372583426241211224817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 249581722284160807483211 374372583426241211224817)
                ·
                  refine ⟨280779437569680908418613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 374372583426241211224817 280779437569680908418613)
                  ·
                    refine ⟨26323072272157585164245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 280779437569680908418613 26323072272157585164245)
                    ·
                      rfl

theorem cell22_76896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 3, 1, 2, 5].length) (baseStart_76896 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_76896 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_76896 prefixEnd_76896 := by exact prefixLift 76896
  have htrace : WordTrace (prefixWord ++ tailWord_76896) baseStart_76896 baseEnd_76896 := by
    simpa [prefixWord, tailWord_76896, baseEnd_76896] using wordTrace_append hprefix tailTrace_76896
  have hstable : (prefixWord ++ tailWord_76896).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76896).length < 2 ^ (prefixWord ++ tailWord_76896).sum := by decide
  have hdescent : baseEnd_76896 < baseStart_76896 := by decide
  rcases family_descends (prefixWord ++ tailWord_76896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76911 : List Nat := [1, 1, 2, 1, 3, 3, 1, 3, 3, 4]
def baseStart_76911 : Nat := 118140960795 + 76911 * 2 ^ 59
def prefixEnd_76911 : Nat := 4983230072969 + 3 ^ 40 * 76911 * 2
def baseEnd_76911 : Nat := 26328207078702546039199

theorem tailTrace_76911 : CollatzResearch.WordTrace tailWord_76911 prefixEnd_76911 26328207078702546039199 := by
  unfold tailWord_76911
  simp only [CollatzResearch.WordTrace]
  refine ⟨2805174624372057198150587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1870116416248038132100391 2805174624372057198150587)
  ·
    refine ⟨4207761936558085797225881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2805174624372057198150587 4207761936558085797225881)
    ·
      refine ⟨3155821452418564347919411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4207761936558085797225881 3155821452418564347919411)
      ·
        refine ⟨4733732178627846521879117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3155821452418564347919411 4733732178627846521879117)
        ·
          refine ⟨1775149566985442445704669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4733732178627846521879117 1775149566985442445704669)
          ·
            refine ⟨665681087619540917139251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1775149566985442445704669 665681087619540917139251)
            ·
              refine ⟨998521631429311375708877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 665681087619540917139251 998521631429311375708877)
              ·
                refine ⟨374445611785991765890829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 998521631429311375708877 374445611785991765890829)
                ·
                  refine ⟨140417104419746912209061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 374445611785991765890829 140417104419746912209061)
                  ·
                    refine ⟨26328207078702546039199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 140417104419746912209061 26328207078702546039199)
                    ·
                      rfl

theorem cell22_76911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 3, 3, 4].length) (baseStart_76911 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_76911 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_76911 prefixEnd_76911 := by exact prefixLift 76911
  have htrace : WordTrace (prefixWord ++ tailWord_76911) baseStart_76911 baseEnd_76911 := by
    simpa [prefixWord, tailWord_76911, baseEnd_76911] using wordTrace_append hprefix tailTrace_76911
  have hstable : (prefixWord ++ tailWord_76911).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76911).length < 2 ^ (prefixWord ++ tailWord_76911).sum := by decide
  have hdescent : baseEnd_76911 < baseStart_76911 := by decide
  rcases family_descends (prefixWord ++ tailWord_76911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76962 : List Nat := [3, 3, 1, 3, 2, 1, 2, 2, 1, 4]
def baseStart_76962 : Nat := 118140960795 + 76962 * 2 ^ 59
def prefixEnd_76962 : Nat := 4983230072969 + 3 ^ 40 * 76962 * 2
def baseEnd_76962 : Nat := 26345665420955413014043

theorem tailTrace_76962 : CollatzResearch.WordTrace tailWord_76962 prefixEnd_76962 26345665420955413014043 := by
  unfold tailWord_76962
  simp only [CollatzResearch.WordTrace]
  refine ⟨701758686796823227064285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1871356498124861938838093 701758686796823227064285)
  ·
    refine ⟨263159507548808710149107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 701758686796823227064285 263159507548808710149107)
    ·
      refine ⟨394739261323213065223661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 263159507548808710149107 394739261323213065223661)
      ·
        refine ⟨148027222996204899458873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 394739261323213065223661 148027222996204899458873)
        ·
          refine ⟨111020417247153674594155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 148027222996204899458873 111020417247153674594155)
          ·
            refine ⟨166530625870730511891233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111020417247153674594155 166530625870730511891233)
            ·
              refine ⟨124897969403047883918425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 166530625870730511891233 124897969403047883918425)
              ·
                refine ⟨93673477052285912938819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 124897969403047883918425 93673477052285912938819)
                ·
                  refine ⟨140510215578428869408229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 93673477052285912938819 140510215578428869408229)
                  ·
                    refine ⟨26345665420955413014043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 140510215578428869408229 26345665420955413014043)
                    ·
                      rfl

theorem cell22_76962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 2, 2, 1, 4].length) (baseStart_76962 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_76962 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_76962 prefixEnd_76962 := by exact prefixLift 76962
  have htrace : WordTrace (prefixWord ++ tailWord_76962) baseStart_76962 baseEnd_76962 := by
    simpa [prefixWord, tailWord_76962, baseEnd_76962] using wordTrace_append hprefix tailTrace_76962
  have hstable : (prefixWord ++ tailWord_76962).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76962).length < 2 ^ (prefixWord ++ tailWord_76962).sum := by decide
  have hdescent : baseEnd_76962 < baseStart_76962 := by decide
  rcases family_descends (prefixWord ++ tailWord_76962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76977 : List Nat := [1, 2, 2, 5, 1, 3, 1, 3, 4]
def baseStart_76977 : Nat := 118140960795 + 76977 * 2 ^ 59
def prefixEnd_76977 : Nat := 4983230072969 + 3 ^ 40 * 76977 * 2
def baseEnd_76977 : Nat := 8783600075833457962999

theorem tailTrace_76977 : CollatzResearch.WordTrace tailWord_76977 prefixEnd_76977 8783600075833457962999 := by
  unfold tailWord_76977
  simp only [CollatzResearch.WordTrace]
  refine ⟨2807581842132950470053185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1871721228088633646702123 2807581842132950470053185)
  ·
    refine ⟨2105686381599712852539889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2807581842132950470053185 2105686381599712852539889)
    ·
      refine ⟨1579264786199784639404917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2105686381599712852539889 1579264786199784639404917)
      ·
        refine ⟨148056073706229809944211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1579264786199784639404917 148056073706229809944211)
        ·
          refine ⟨222084110559344714916317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148056073706229809944211 222084110559344714916317)
          ·
            refine ⟨83281541459754268093619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 222084110559344714916317 83281541459754268093619)
            ·
              refine ⟨124922312189631402140429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83281541459754268093619 124922312189631402140429)
              ·
                refine ⟨46845867071111775802661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 124922312189631402140429 46845867071111775802661)
                ·
                  refine ⟨8783600075833457962999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 46845867071111775802661 8783600075833457962999)
                  ·
                    rfl

theorem cell22_76977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 3, 1, 3, 4].length) (baseStart_76977 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_76977 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_76977 prefixEnd_76977 := by exact prefixLift 76977
  have htrace : WordTrace (prefixWord ++ tailWord_76977) baseStart_76977 baseEnd_76977 := by
    simpa [prefixWord, tailWord_76977, baseEnd_76977] using wordTrace_append hprefix tailTrace_76977
  have hstable : (prefixWord ++ tailWord_76977).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76977).length < 2 ^ (prefixWord ++ tailWord_76977).sum := by decide
  have hdescent : baseEnd_76977 < baseStart_76977 := by decide
  rcases family_descends (prefixWord ++ tailWord_76977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76988 : List Nat := [2, 2, 2, 3, 2, 3, 8]
def baseStart_76988 : Nat := 118140960795 + 76988 * 2 ^ 59
def prefixEnd_76988 : Nat := 4983230072969 + 3 ^ 40 * 76988 * 2
def baseEnd_76988 : Nat := 976095027862963402369

theorem tailTrace_76988 : CollatzResearch.WordTrace tailWord_76988 prefixEnd_76988 976095027862963402369 := by
  unfold tailWord_76988
  simp only [CollatzResearch.WordTrace]
  refine ⟨1403991522546549674351809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1871988696728732899135745 1403991522546549674351809)
  ·
    refine ⟨1052993641909912255763857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1403991522546549674351809 1052993641909912255763857)
    ·
      refine ⟨789745231432434191822893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1052993641909912255763857 789745231432434191822893)
      ·
        refine ⟨296154461787162821933585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 789745231432434191822893 296154461787162821933585)
        ·
          refine ⟨222115846340372116450189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 296154461787162821933585 222115846340372116450189)
          ·
            refine ⟨83293442377639543668821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 222115846340372116450189 83293442377639543668821)
            ·
              refine ⟨976095027862963402369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 83293442377639543668821 976095027862963402369)
              ·
                rfl

theorem cell22_76988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 3, 8].length) (baseStart_76988 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_76988 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_76988 prefixEnd_76988 := by exact prefixLift 76988
  have htrace : WordTrace (prefixWord ++ tailWord_76988) baseStart_76988 baseEnd_76988 := by
    simpa [prefixWord, tailWord_76988, baseEnd_76988] using wordTrace_append hprefix tailTrace_76988
  have hstable : (prefixWord ++ tailWord_76988).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76988).length < 2 ^ (prefixWord ++ tailWord_76988).sum := by decide
  have hdescent : baseEnd_76988 < baseStart_76988 := by decide
  rcases family_descends (prefixWord ++ tailWord_76988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76990 : List Nat := [4, 2, 1, 1, 3, 2, 1, 2, 2, 4]
def baseStart_76990 : Nat := 118140960795 + 76990 * 2 ^ 59
def prefixEnd_76990 : Nat := 4983230072969 + 3 ^ 40 * 76990 * 2
def baseEnd_76990 : Nat := 26355250393172673313957

theorem tailTrace_76990 : CollatzResearch.WordTrace tailWord_76990 prefixEnd_76990 26355250393172673313957 := by
  unfold tailWord_76990
  simp only [CollatzResearch.WordTrace]
  refine ⟨351006998885731711284553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1872037327390569126850949 351006998885731711284553)
  ·
    refine ⟨263255249164298783463415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 351006998885731711284553 263255249164298783463415)
    ·
      refine ⟨394882873746448175195123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 263255249164298783463415 394882873746448175195123)
      ·
        refine ⟨592324310619672262792685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 394882873746448175195123 592324310619672262792685)
        ·
          refine ⟨222121616482377098547257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 592324310619672262792685 222121616482377098547257)
          ·
            refine ⟨166591212361782823910443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 222121616482377098547257 166591212361782823910443)
            ·
              refine ⟨249886818542674235865665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 166591212361782823910443 249886818542674235865665)
              ·
                refine ⟨187415113907005676899249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 249886818542674235865665 187415113907005676899249)
                ·
                  refine ⟨140561335430254257674437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 187415113907005676899249 140561335430254257674437)
                  ·
                    refine ⟨26355250393172673313957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 140561335430254257674437 26355250393172673313957)
                    ·
                      rfl

theorem cell22_76990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 1, 2, 2, 4].length) (baseStart_76990 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_76990 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_76990 prefixEnd_76990 := by exact prefixLift 76990
  have htrace : WordTrace (prefixWord ++ tailWord_76990) baseStart_76990 baseEnd_76990 := by
    simpa [prefixWord, tailWord_76990, baseEnd_76990] using wordTrace_append hprefix tailTrace_76990
  have hstable : (prefixWord ++ tailWord_76990).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76990).length < 2 ^ (prefixWord ++ tailWord_76990).sum := by decide
  have hdescent : baseEnd_76990 < baseStart_76990 := by decide
  rcases family_descends (prefixWord ++ tailWord_76990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76994 : List Nat := [3, 5, 1, 1, 2, 2, 1, 1, 6]
def baseStart_76994 : Nat := 118140960795 + 76994 * 2 ^ 59
def prefixEnd_76994 : Nat := 4983230072969 + 3 ^ 40 * 76994 * 2
def baseEnd_76994 : Nat := 8785539891639332071315

theorem tailTrace_76994 : CollatzResearch.WordTrace tailWord_76994 prefixEnd_76994 8785539891639332071315 := by
  unfold tailWord_76994
  simp only [CollatzResearch.WordTrace]
  refine ⟨702050470767840593355509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1872134588714241582281357 702050470767840593355509)
  ·
    refine ⟨65817231634485055627079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 702050470767840593355509 65817231634485055627079)
    ·
      refine ⟨98725847451727583440619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65817231634485055627079 98725847451727583440619)
      ·
        refine ⟨148088771177591375160929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98725847451727583440619 148088771177591375160929)
        ·
          refine ⟨111066578383193531370697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 148088771177591375160929 111066578383193531370697)
          ·
            refine ⟨83299933787395148528023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 111066578383193531370697 83299933787395148528023)
            ·
              refine ⟨124949900681092722792035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83299933787395148528023 124949900681092722792035)
              ·
                refine ⟨187424851021639084188053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 124949900681092722792035 187424851021639084188053)
                ·
                  refine ⟨8785539891639332071315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 187424851021639084188053 8785539891639332071315)
                  ·
                    rfl

theorem cell22_76994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 2, 1, 1, 6].length) (baseStart_76994 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_76994 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_76994 prefixEnd_76994 := by exact prefixLift 76994
  have htrace : WordTrace (prefixWord ++ tailWord_76994) baseStart_76994 baseEnd_76994 := by
    simpa [prefixWord, tailWord_76994, baseEnd_76994] using wordTrace_append hprefix tailTrace_76994
  have hstable : (prefixWord ++ tailWord_76994).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76994).length < 2 ^ (prefixWord ++ tailWord_76994).sum := by decide
  have hdescent : baseEnd_76994 < baseStart_76994 := by decide
  rcases family_descends (prefixWord ++ tailWord_76994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_77003 : List Nat := [1, 1, 1, 1, 3, 2, 2, 5, 3, 3]
def baseStart_77003 : Nat := 118140960795 + 77003 * 2 ^ 59
def prefixEnd_77003 : Nat := 4983230072969 + 3 ^ 40 * 77003 * 2
def baseEnd_77003 : Nat := 26359700558844972738917

theorem tailTrace_77003 : CollatzResearch.WordTrace tailWord_77003 prefixEnd_77003 26359700558844972738917 := by
  unfold tailWord_77003
  simp only [CollatzResearch.WordTrace]
  refine ⟨2808530140038756910499663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1872353426692504606999775 2808530140038756910499663)
  ·
    refine ⟨4212795210058135365749495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2808530140038756910499663 4212795210058135365749495)
    ·
      refine ⟨6319192815087203048624243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4212795210058135365749495 6319192815087203048624243)
      ·
        refine ⟨9478789222630804572936365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6319192815087203048624243 9478789222630804572936365)
        ·
          refine ⟨3554545958486551714851137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9478789222630804572936365 3554545958486551714851137)
          ·
            refine ⟨2665909468864913786138353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3554545958486551714851137 2665909468864913786138353)
            ·
              refine ⟨1999432101648685339603765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2665909468864913786138353 1999432101648685339603765)
              ·
                refine ⟨187446759529564250587853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1999432101648685339603765 187446759529564250587853)
                ·
                  refine ⟨70292534823586593970445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 187446759529564250587853 70292534823586593970445)
                  ·
                    refine ⟨26359700558844972738917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 70292534823586593970445 26359700558844972738917)
                    ·
                      rfl

theorem cell22_77003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 5, 3, 3].length) (baseStart_77003 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_77003 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_77003 prefixEnd_77003 := by exact prefixLift 77003
  have htrace : WordTrace (prefixWord ++ tailWord_77003) baseStart_77003 baseEnd_77003 := by
    simpa [prefixWord, tailWord_77003, baseEnd_77003] using wordTrace_append hprefix tailTrace_77003
  have hstable : (prefixWord ++ tailWord_77003).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_77003).length < 2 ^ (prefixWord ++ tailWord_77003).sum := by decide
  have hdescent : baseEnd_77003 < baseStart_77003 := by decide
  rcases family_descends (prefixWord ++ tailWord_77003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_77054 : List Nat := [4, 2, 2, 1, 1, 3, 1, 4, 1, 3]
def baseStart_77054 : Nat := 118140960795 + 77054 * 2 ^ 59
def prefixEnd_77054 : Nat := 4983230072969 + 3 ^ 40 * 77054 * 2
def baseEnd_77054 : Nat := 26377158901097839713761

theorem tailTrace_77054 : CollatzResearch.WordTrace tailWord_77054 prefixEnd_77054 26377158901097839713761 := by
  unfold tailWord_77054
  simp only [CollatzResearch.WordTrace]
  refine ⟨351298782856749077575777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1873593508569328413737477 351298782856749077575777)
  ·
    refine ⟨263474087142561808181833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 351298782856749077575777 263474087142561808181833)
    ·
      refine ⟨197605565356921356136375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 263474087142561808181833 197605565356921356136375)
      ·
        refine ⟨296408348035382034204563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 197605565356921356136375 296408348035382034204563)
        ·
          refine ⟨444612522053073051306845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 296408348035382034204563 444612522053073051306845)
          ·
            refine ⟨166729695769902394240067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 444612522053073051306845 166729695769902394240067)
            ·
              refine ⟨250094543654853591360101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 166729695769902394240067 250094543654853591360101)
              ·
                refine ⟨46892726935285048380019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 250094543654853591360101 46892726935285048380019)
                ·
                  refine ⟨70339090402927572570029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46892726935285048380019 70339090402927572570029)
                  ·
                    refine ⟨26377158901097839713761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 70339090402927572570029 26377158901097839713761)
                    ·
                      rfl

theorem cell22_77054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 1, 4, 1, 3].length) (baseStart_77054 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_77054 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_77054 prefixEnd_77054 := by exact prefixLift 77054
  have htrace : WordTrace (prefixWord ++ tailWord_77054) baseStart_77054 baseEnd_77054 := by
    simpa [prefixWord, tailWord_77054, baseEnd_77054] using wordTrace_append hprefix tailTrace_77054
  have hstable : (prefixWord ++ tailWord_77054).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_77054).length < 2 ^ (prefixWord ++ tailWord_77054).sum := by decide
  have hdescent : baseEnd_77054 < baseStart_77054 := by decide
  rcases family_descends (prefixWord ++ tailWord_77054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_77138 : List Nat := [3, 2, 2, 1, 1, 1, 1, 1, 1, 9]
def baseStart_77138 : Nat := 118140960795 + 77138 * 2 ^ 59
def prefixEnd_77138 : Nat := 4983230072969 + 3 ^ 40 * 77138 * 2
def baseEnd_77138 : Nat := 26405913817749620613503

theorem tailTrace_77138 : CollatzResearch.WordTrace tailWord_77138 prefixEnd_77138 26405913817749620613503 := by
  unfold tailWord_77138
  simp only [CollatzResearch.WordTrace]
  refine ⟨703363498637418741666017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1875635996366449977776045 703363498637418741666017)
  ·
    refine ⟨527522623978064056249513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 703363498637418741666017 527522623978064056249513)
    ·
      refine ⟨395641967983548042187135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 527522623978064056249513 395641967983548042187135)
      ·
        refine ⟨593462951975322063280703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 395641967983548042187135 593462951975322063280703)
        ·
          refine ⟨890194427962983094921055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 593462951975322063280703 890194427962983094921055)
          ·
            refine ⟨1335291641944474642381583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 890194427962983094921055 1335291641944474642381583)
            ·
              refine ⟨2002937462916711963572375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1335291641944474642381583 2002937462916711963572375)
              ·
                refine ⟨3004406194375067945358563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2002937462916711963572375 3004406194375067945358563)
                ·
                  refine ⟨4506609291562601918037845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3004406194375067945358563 4506609291562601918037845)
                  ·
                    refine ⟨26405913817749620613503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 4506609291562601918037845 26405913817749620613503)
                    ·
                      rfl

theorem cell22_77138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 1, 1, 9].length) (baseStart_77138 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_77138 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_77138 prefixEnd_77138 := by exact prefixLift 77138
  have htrace : WordTrace (prefixWord ++ tailWord_77138) baseStart_77138 baseEnd_77138 := by
    simpa [prefixWord, tailWord_77138, baseEnd_77138] using wordTrace_append hprefix tailTrace_77138
  have hstable : (prefixWord ++ tailWord_77138).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_77138).length < 2 ^ (prefixWord ++ tailWord_77138).sum := by decide
  have hdescent : baseEnd_77138 < baseStart_77138 := by decide
  rcases family_descends (prefixWord ++ tailWord_77138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_77168 : List Nat := [2, 1, 1, 1, 4, 2, 1, 3, 7]
def baseStart_77168 : Nat := 118140960795 + 77168 * 2 ^ 59
def prefixEnd_77168 : Nat := 4983230072969 + 3 ^ 40 * 77168 * 2
def baseEnd_77168 : Nat := 8805394476946514121137

theorem tailTrace_77168 : CollatzResearch.WordTrace tailWord_77168 prefixEnd_77168 8805394476946514121137 := by
  unfold tailWord_77168
  simp only [CollatzResearch.WordTrace]
  refine ⟨1407274092220495045128079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1876365456293993393504105 1407274092220495045128079)
  ·
    refine ⟨2110911138330742567692119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1407274092220495045128079 2110911138330742567692119)
    ·
      refine ⟨3166366707496113851538179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2110911138330742567692119 3166366707496113851538179)
      ·
        refine ⟨4749550061244170777307269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3166366707496113851538179 4749550061244170777307269)
        ·
          refine ⟨890540636483282020745113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4749550061244170777307269 890540636483282020745113)
          ·
            refine ⟨667905477362461515558835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 890540636483282020745113 667905477362461515558835)
            ·
              refine ⟨1001858216043692273338253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 667905477362461515558835 1001858216043692273338253)
              ·
                refine ⟨375696831016384602501845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1001858216043692273338253 375696831016384602501845)
                ·
                  refine ⟨8805394476946514121137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 375696831016384602501845 8805394476946514121137)
                  ·
                    rfl

theorem cell22_77168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 3, 7].length) (baseStart_77168 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_77168 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_77168 prefixEnd_77168 := by exact prefixLift 77168
  have htrace : WordTrace (prefixWord ++ tailWord_77168) baseStart_77168 baseEnd_77168 := by
    simpa [prefixWord, tailWord_77168, baseEnd_77168] using wordTrace_append hprefix tailTrace_77168
  have hstable : (prefixWord ++ tailWord_77168).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_77168).length < 2 ^ (prefixWord ++ tailWord_77168).sum := by decide
  have hdescent : baseEnd_77168 < baseStart_77168 := by decide
  rcases family_descends (prefixWord ++ tailWord_77168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_77320 : List Nat := [2, 1, 3, 2, 1, 1, 3, 2, 7]
def baseStart_77320 : Nat := 118140960795 + 77320 * 2 ^ 59
def prefixEnd_77320 : Nat := 4983230072969 + 3 ^ 40 * 77320 * 2
def baseEnd_77320 : Nat := 8822738712387270854315

theorem tailTrace_77320 : CollatzResearch.WordTrace tailWord_77320 prefixEnd_77320 8822738712387270854315 := by
  unfold tailWord_77320
  simp only [CollatzResearch.WordTrace]
  refine ⟨1410046039945160024894707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1880061386593546699859609 1410046039945160024894707)
  ·
    refine ⟨2115069059917740037342061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1410046039945160024894707 2115069059917740037342061)
    ·
      refine ⟨793150897469152514003273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2115069059917740037342061 793150897469152514003273)
      ·
        refine ⟨594863173101864385502455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 793150897469152514003273 594863173101864385502455)
        ·
          refine ⟨892294759652796578253683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 594863173101864385502455 892294759652796578253683)
          ·
            refine ⟨1338442139479194867380525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 892294759652796578253683 1338442139479194867380525)
            ·
              refine ⟨501915802304698075267697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1338442139479194867380525 501915802304698075267697)
              ·
                refine ⟨376436851728523556450773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 501915802304698075267697 376436851728523556450773)
                ·
                  refine ⟨8822738712387270854315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 376436851728523556450773 8822738712387270854315)
                  ·
                    rfl

theorem cell22_77320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 2, 7].length) (baseStart_77320 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_77320 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_77320 prefixEnd_77320 := by exact prefixLift 77320
  have htrace : WordTrace (prefixWord ++ tailWord_77320) baseStart_77320 baseEnd_77320 := by
    simpa [prefixWord, tailWord_77320, baseEnd_77320] using wordTrace_append hprefix tailTrace_77320
  have hstable : (prefixWord ++ tailWord_77320).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_77320).length < 2 ^ (prefixWord ++ tailWord_77320).sum := by decide
  have hdescent : baseEnd_77320 < baseStart_77320 := by decide
  rcases family_descends (prefixWord ++ tailWord_77320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_77367 : List Nat := [1, 1, 3, 1, 2, 5, 1, 1, 3, 4]
def baseStart_77367 : Nat := 118140960795 + 77367 * 2 ^ 59
def prefixEnd_77367 : Nat := 4983230072969 + 3 ^ 40 * 77367 * 2
def baseEnd_77367 : Nat := 26484305197669356637801

theorem tailTrace_77367 : CollatzResearch.WordTrace tailWord_77367 prefixEnd_77367 26484305197669356637801 := by
  unfold tailWord_77367
  simp only [CollatzResearch.WordTrace]
  refine ⟨2821806310720047076750355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1881204207146698051166903 2821806310720047076750355)
  ·
    refine ⟨4232709466080070615125533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2821806310720047076750355 4232709466080070615125533)
    ·
      refine ⟨1587266049780026480672075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4232709466080070615125533 1587266049780026480672075)
      ·
        refine ⟨2380899074670039721008113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1587266049780026480672075 2380899074670039721008113)
        ·
          refine ⟨1785674306002529790756085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2380899074670039721008113 1785674306002529790756085)
          ·
            refine ⟨167406966187737167883383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1785674306002529790756085 167406966187737167883383)
            ·
              refine ⟨251110449281605751825075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 167406966187737167883383 251110449281605751825075)
              ·
                refine ⟨376665673922408627737613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 251110449281605751825075 376665673922408627737613)
                ·
                  refine ⟨141249627720903235401605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 376665673922408627737613 141249627720903235401605)
                  ·
                    refine ⟨26484305197669356637801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 141249627720903235401605 26484305197669356637801)
                    ·
                      rfl

theorem cell22_77367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 1, 1, 3, 4].length) (baseStart_77367 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_77367 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_77367 prefixEnd_77367 := by exact prefixLift 77367
  have htrace : WordTrace (prefixWord ++ tailWord_77367) baseStart_77367 baseEnd_77367 := by
    simpa [prefixWord, tailWord_77367, baseEnd_77367] using wordTrace_append hprefix tailTrace_77367
  have hstable : (prefixWord ++ tailWord_77367).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_77367).length < 2 ^ (prefixWord ++ tailWord_77367).sum := by decide
  have hdescent : baseEnd_77367 < baseStart_77367 := by decide
  rcases family_descends (prefixWord ++ tailWord_77367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_77399 : List Nat := [1, 1, 3, 2, 2, 4, 1, 4, 4]
def baseStart_77399 : Nat := 118140960795 + 77399 * 2 ^ 59
def prefixEnd_77399 : Nat := 4983230072969 + 3 ^ 40 * 77399 * 2
def baseEnd_77399 : Nat := 8831753150543979945901

theorem tailTrace_77399 : CollatzResearch.WordTrace tailWord_77399 prefixEnd_77399 8831753150543979945901 := by
  unfold tailWord_77399
  simp only [CollatzResearch.WordTrace]
  refine ⟨2822973446604116541915251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1881982297736077694610167 2822973446604116541915251)
  ·
    refine ⟨4234460169906174812872877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2822973446604116541915251 4234460169906174812872877)
    ·
      refine ⟨1587922563714815554827329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4234460169906174812872877 1587922563714815554827329)
      ·
        refine ⟨1190941922786111666120497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1587922563714815554827329 1190941922786111666120497)
        ·
          refine ⟨893206442089583749590373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1190941922786111666120497 893206442089583749590373)
          ·
            refine ⟨167476207891796953048195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 893206442089583749590373 167476207891796953048195)
            ·
              refine ⟨251214311837695429572293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 167476207891796953048195 251214311837695429572293)
              ·
                refine ⟨47102683469567893044805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 251214311837695429572293 47102683469567893044805)
                ·
                  refine ⟨8831753150543979945901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 47102683469567893044805 8831753150543979945901)
                  ·
                    rfl

theorem cell22_77399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 1, 4, 4].length) (baseStart_77399 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_77399 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_77399 prefixEnd_77399 := by exact prefixLift 77399
  have htrace : WordTrace (prefixWord ++ tailWord_77399) baseStart_77399 baseEnd_77399 := by
    simpa [prefixWord, tailWord_77399, baseEnd_77399] using wordTrace_append hprefix tailTrace_77399
  have hstable : (prefixWord ++ tailWord_77399).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_77399).length < 2 ^ (prefixWord ++ tailWord_77399).sum := by decide
  have hdescent : baseEnd_77399 < baseStart_77399 := by decide
  rcases family_descends (prefixWord ++ tailWord_77399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_77429 : List Nat := [1, 3, 4, 2, 1, 2, 1, 1, 1, 6]
def baseStart_77429 : Nat := 118140960795 + 77429 * 2 ^ 59
def prefixEnd_77429 : Nat := 4983230072969 + 3 ^ 40 * 77429 * 2
def baseEnd_77429 : Nat := 26505529064721861587611

theorem tailTrace_77429 : CollatzResearch.WordTrace tailWord_77429 prefixEnd_77429 26505529064721861587611 := by
  unfold tailWord_77429
  simp only [CollatzResearch.WordTrace]
  refine ⟨2824067636495431665507341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1882711757663621110338227 2824067636495431665507341)
  ·
    refine ⟨1059025363685786874565253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2824067636495431665507341 1059025363685786874565253)
    ·
      refine ⟨198567255691085038980985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1059025363685786874565253 198567255691085038980985)
      ·
        refine ⟨148925441768313779235739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 198567255691085038980985 148925441768313779235739)
        ·
          refine ⟨223388162652470668853609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148925441768313779235739 223388162652470668853609)
          ·
            refine ⟨167541121989353001640207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 223388162652470668853609 167541121989353001640207)
            ·
              refine ⟨251311682984029502460311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 167541121989353001640207 251311682984029502460311)
              ·
                refine ⟨376967524476044253690467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 251311682984029502460311 376967524476044253690467)
                ·
                  refine ⟨565451286714066380535701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 376967524476044253690467 565451286714066380535701)
                  ·
                    refine ⟨26505529064721861587611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 565451286714066380535701 26505529064721861587611)
                    ·
                      rfl

theorem cell22_77429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 1, 1, 1, 6].length) (baseStart_77429 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_77429 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_77429 prefixEnd_77429 := by exact prefixLift 77429
  have htrace : WordTrace (prefixWord ++ tailWord_77429) baseStart_77429 baseEnd_77429 := by
    simpa [prefixWord, tailWord_77429, baseEnd_77429] using wordTrace_append hprefix tailTrace_77429
  have hstable : (prefixWord ++ tailWord_77429).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_77429).length < 2 ^ (prefixWord ++ tailWord_77429).sum := by decide
  have hdescent : baseEnd_77429 < baseStart_77429 := by decide
  rcases family_descends (prefixWord ++ tailWord_77429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_77510 : List Nat := [6, 1, 2, 1, 1, 1, 3, 1, 3, 3]
def baseStart_77510 : Nat := 118140960795 + 77510 * 2 ^ 59
def prefixEnd_77510 : Nat := 4983230072969 + 3 ^ 40 * 77510 * 2
def baseEnd_77510 : Nat := 26533257020064650312363

theorem tailTrace_77510 : CollatzResearch.WordTrace tailWord_77510 prefixEnd_77510 26533257020064650312363 := by
  unfold tailWord_77510
  simp only [CollatzResearch.WordTrace]
  refine ⟨88344435912561953100187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 1884681299467988332803989 88344435912561953100187)
  ·
    refine ⟨132516653868842929650281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88344435912561953100187 132516653868842929650281)
    ·
      refine ⟨99387490401632197237711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132516653868842929650281 99387490401632197237711)
      ·
        refine ⟨149081235602448295856567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99387490401632197237711 149081235602448295856567)
        ·
          refine ⟨223621853403672443784851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149081235602448295856567 223621853403672443784851)
          ·
            refine ⟨335432780105508665677277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 223621853403672443784851 335432780105508665677277)
            ·
              refine ⟨125787292539565749628979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 335432780105508665677277 125787292539565749628979)
              ·
                refine ⟨188680938809348624443469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 125787292539565749628979 188680938809348624443469)
                ·
                  refine ⟨70755352053505734166301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 188680938809348624443469 70755352053505734166301)
                  ·
                    refine ⟨26533257020064650312363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 70755352053505734166301 26533257020064650312363)
                    ·
                      rfl

theorem cell22_77510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 3, 1, 3, 3].length) (baseStart_77510 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_77510 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_77510 prefixEnd_77510 := by exact prefixLift 77510
  have htrace : WordTrace (prefixWord ++ tailWord_77510) baseStart_77510 baseEnd_77510 := by
    simpa [prefixWord, tailWord_77510, baseEnd_77510] using wordTrace_append hprefix tailTrace_77510
  have hstable : (prefixWord ++ tailWord_77510).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_77510).length < 2 ^ (prefixWord ++ tailWord_77510).sum := by decide
  have hdescent : baseEnd_77510 < baseStart_77510 := by decide
  rcases family_descends (prefixWord ++ tailWord_77510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_77547 : List Nat := [1, 1, 1, 1, 2, 4, 2, 3, 1, 6]
def baseStart_77547 : Nat := 118140960795 + 77547 * 2 ^ 59
def prefixEnd_77547 : Nat := 4983230072969 + 3 ^ 40 * 77547 * 2
def baseEnd_77547 : Nat := 26545922876208887137249

theorem tailTrace_77547 : CollatzResearch.WordTrace tailWord_77547 prefixEnd_77547 26545922876208887137249 := by
  unfold tailWord_77547
  simp only [CollatzResearch.WordTrace]
  refine ⟨2828371450067937818302895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1885580966711958545535263 2828371450067937818302895)
  ·
    refine ⟨4242557175101906727454343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2828371450067937818302895 4242557175101906727454343)
    ·
      refine ⟨6363835762652860091181515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4242557175101906727454343 6363835762652860091181515)
      ·
        refine ⟨9545753643979290136772273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6363835762652860091181515 9545753643979290136772273)
        ·
          refine ⟨7159315232984467602579205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9545753643979290136772273 7159315232984467602579205)
          ·
            refine ⟨1342371606184587675483601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7159315232984467602579205 1342371606184587675483601)
            ·
              refine ⟨1006778704638440756612701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1342371606184587675483601 1006778704638440756612701)
              ·
                refine ⟨377542014239415283729763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1006778704638440756612701 377542014239415283729763)
                ·
                  refine ⟨566313021359122925594645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 377542014239415283729763 566313021359122925594645)
                  ·
                    refine ⟨26545922876208887137249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 566313021359122925594645 26545922876208887137249)
                    ·
                      rfl

theorem cell22_77547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 3, 1, 6].length) (baseStart_77547 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_77547 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_77547 prefixEnd_77547 := by exact prefixLift 77547
  have htrace : WordTrace (prefixWord ++ tailWord_77547) baseStart_77547 baseEnd_77547 := by
    simpa [prefixWord, tailWord_77547, baseEnd_77547] using wordTrace_append hprefix tailTrace_77547
  have hstable : (prefixWord ++ tailWord_77547).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_77547).length < 2 ^ (prefixWord ++ tailWord_77547).sum := by decide
  have hdescent : baseEnd_77547 < baseStart_77547 := by decide
  rcases family_descends (prefixWord ++ tailWord_77547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_77549 : List Nat := [1, 5, 1, 2, 1, 2, 1, 1, 3, 5]
def baseStart_77549 : Nat := 118140960795 + 77549 * 2 ^ 59
def prefixEnd_77549 : Nat := 4983230072969 + 3 ^ 40 * 77549 * 2
def baseEnd_77549 : Nat := 26546607517081548587243

theorem tailTrace_77549 : CollatzResearch.WordTrace tailWord_77549 prefixEnd_77549 26546607517081548587243 := by
  unfold tailWord_77549
  simp only [CollatzResearch.WordTrace]
  refine ⟨2828444396060692159875701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1885629597373794773250467 2828444396060692159875701)
  ·
    refine ⟨265166662130689889988347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2828444396060692159875701 265166662130689889988347)
    ·
      refine ⟨397749993196034834982521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 265166662130689889988347 397749993196034834982521)
      ·
        refine ⟨298312494897026126236891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 397749993196034834982521 298312494897026126236891)
        ·
          refine ⟨447468742345539189355337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 298312494897026126236891 447468742345539189355337)
          ·
            refine ⟨335601556759154392016503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 447468742345539189355337 335601556759154392016503)
            ·
              refine ⟨503402335138731588024755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 335601556759154392016503 503402335138731588024755)
              ·
                refine ⟨755103502708097382037133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 503402335138731588024755 755103502708097382037133)
                ·
                  refine ⟨283163813515536518263925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 755103502708097382037133 283163813515536518263925)
                  ·
                    refine ⟨26546607517081548587243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 283163813515536518263925 26546607517081548587243)
                    ·
                      rfl

theorem cell22_77549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 1, 3, 5].length) (baseStart_77549 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_77549 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_77549 prefixEnd_77549 := by exact prefixLift 77549
  have htrace : WordTrace (prefixWord ++ tailWord_77549) baseStart_77549 baseEnd_77549 := by
    simpa [prefixWord, tailWord_77549, baseEnd_77549] using wordTrace_append hprefix tailTrace_77549
  have hstable : (prefixWord ++ tailWord_77549).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_77549).length < 2 ^ (prefixWord ++ tailWord_77549).sum := by decide
  have hdescent : baseEnd_77549 < baseStart_77549 := by decide
  rcases family_descends (prefixWord ++ tailWord_77549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_77564 : List Nat := [2, 2, 2, 1, 3, 1, 1, 4, 2, 4]
def baseStart_77564 : Nat := 118140960795 + 77564 * 2 ^ 59
def prefixEnd_77564 : Nat := 4983230072969 + 3 ^ 40 * 77564 * 2
def baseEnd_77564 : Nat := 26551742323626509462197

theorem tailTrace_77564 : CollatzResearch.WordTrace tailWord_77564 prefixEnd_77564 26551742323626509462197 := by
  unfold tailWord_77564
  simp only [CollatzResearch.WordTrace]
  refine ⟨1414495745503174860835873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1885994327337566481114497 1414495745503174860835873)
  ·
    refine ⟨1060871809127381145626905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1414495745503174860835873 1060871809127381145626905)
    ·
      refine ⟨795653856845535859220179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1060871809127381145626905 795653856845535859220179)
      ·
        refine ⟨1193480785268303788830269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 795653856845535859220179 1193480785268303788830269)
        ·
          refine ⟨447555294475613920811351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1193480785268303788830269 447555294475613920811351)
          ·
            refine ⟨671332941713420881217027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 447555294475613920811351 671332941713420881217027)
            ·
              refine ⟨1006999412570131321825541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 671332941713420881217027 1006999412570131321825541)
              ·
                refine ⟨188812389856899622842289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1006999412570131321825541 188812389856899622842289)
                ·
                  refine ⟨141609292392674717131717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 188812389856899622842289 141609292392674717131717)
                  ·
                    refine ⟨26551742323626509462197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 141609292392674717131717 26551742323626509462197)
                    ·
                      rfl

theorem cell22_77564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 4, 2, 4].length) (baseStart_77564 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_77564 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_77564 prefixEnd_77564 := by exact prefixLift 77564
  have htrace : WordTrace (prefixWord ++ tailWord_77564) baseStart_77564 baseEnd_77564 := by
    simpa [prefixWord, tailWord_77564, baseEnd_77564] using wordTrace_append hprefix tailTrace_77564
  have hstable : (prefixWord ++ tailWord_77564).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_77564).length < 2 ^ (prefixWord ++ tailWord_77564).sum := by decide
  have hdescent : baseEnd_77564 < baseStart_77564 := by decide
  rcases family_descends (prefixWord ++ tailWord_77564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_77577 : List Nat := [1, 2, 1, 1, 3, 2, 1, 2, 2, 7]
def baseStart_77577 : Nat := 118140960795 + 77577 * 2 ^ 59
def prefixEnd_77577 : Nat := 4983230072969 + 3 ^ 40 * 77577 * 2
def baseEnd_77577 : Nat := 26556192489298808887157

theorem tailTrace_77577 : CollatzResearch.WordTrace tailWord_77577 prefixEnd_77577 26556192489298808887157 := by
  unfold tailWord_77577
  simp only [CollatzResearch.WordTrace]
  refine ⟨2829465639959252941894985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1886310426639501961263323 2829465639959252941894985)
  ·
    refine ⟨2122099229969439706421239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2829465639959252941894985 2122099229969439706421239)
    ·
      refine ⟨3183148844954159559631859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2122099229969439706421239 3183148844954159559631859)
      ·
        refine ⟨4774723267431239339447789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3183148844954159559631859 4774723267431239339447789)
        ·
          refine ⟨1790521225286714752292921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4774723267431239339447789 1790521225286714752292921)
          ·
            refine ⟨1342890918965036064219691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1790521225286714752292921 1342890918965036064219691)
            ·
              refine ⟨2014336378447554096329537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1342890918965036064219691 2014336378447554096329537)
              ·
                refine ⟨1510752283835665572247153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2014336378447554096329537 1510752283835665572247153)
                ·
                  refine ⟨1133064212876749179185365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1510752283835665572247153 1133064212876749179185365)
                  ·
                    refine ⟨26556192489298808887157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1133064212876749179185365 26556192489298808887157)
                    ·
                      rfl

theorem cell22_77577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 2, 2, 7].length) (baseStart_77577 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_77577 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_77577 prefixEnd_77577 := by exact prefixLift 77577
  have htrace : WordTrace (prefixWord ++ tailWord_77577) baseStart_77577 baseEnd_77577 := by
    simpa [prefixWord, tailWord_77577, baseEnd_77577] using wordTrace_append hprefix tailTrace_77577
  have hstable : (prefixWord ++ tailWord_77577).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_77577).length < 2 ^ (prefixWord ++ tailWord_77577).sum := by decide
  have hdescent : baseEnd_77577 < baseStart_77577 := by decide
  rcases family_descends (prefixWord ++ tailWord_77577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_77624 : List Nat := [2, 1, 2, 1, 3, 4, 1, 1, 7]
def baseStart_77624 : Nat := 118140960795 + 77624 * 2 ^ 59
def prefixEnd_77624 : Nat := 4983230072969 + 3 ^ 40 * 77624 * 2
def baseEnd_77624 : Nat := 8857427183268784320671

theorem tailTrace_77624 : CollatzResearch.WordTrace tailWord_77624 prefixEnd_77624 8857427183268784320671 := by
  unfold tailWord_77624
  simp only [CollatzResearch.WordTrace]
  refine ⟨1415589935394489984427963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1887453247192653312570617 1415589935394489984427963)
  ·
    refine ⟨2123384903091734976641945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1415589935394489984427963 2123384903091734976641945)
    ·
      refine ⟨1592538677318801232481459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2123384903091734976641945 1592538677318801232481459)
      ·
        refine ⟨2388808015978201848722189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1592538677318801232481459 2388808015978201848722189)
        ·
          refine ⟨895803005991825693270821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2388808015978201848722189 895803005991825693270821)
          ·
            refine ⟨167963063623467317488279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 895803005991825693270821 167963063623467317488279)
            ·
              refine ⟨251944595435200976232419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 167963063623467317488279 251944595435200976232419)
              ·
                refine ⟨377916893152801464348629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 251944595435200976232419 377916893152801464348629)
                ·
                  refine ⟨8857427183268784320671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 377916893152801464348629 8857427183268784320671)
                  ·
                    rfl

theorem cell22_77624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 1, 1, 7].length) (baseStart_77624 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_77624 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_77624 prefixEnd_77624 := by exact prefixLift 77624
  have htrace : WordTrace (prefixWord ++ tailWord_77624) baseStart_77624 baseEnd_77624 := by
    simpa [prefixWord, tailWord_77624, baseEnd_77624] using wordTrace_append hprefix tailTrace_77624
  have hstable : (prefixWord ++ tailWord_77624).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_77624).length < 2 ^ (prefixWord ++ tailWord_77624).sum := by decide
  have hdescent : baseEnd_77624 < baseStart_77624 := by decide
  rcases family_descends (prefixWord ++ tailWord_77624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_77628 : List Nat := [2, 2, 2, 2, 1, 1, 4, 4, 1, 3]
def baseStart_77628 : Nat := 118140960795 + 77628 * 2 ^ 59
def prefixEnd_77628 : Nat := 4983230072969 + 3 ^ 40 * 77628 * 2
def baseEnd_77628 : Nat := 26573650831551675862001

theorem tailTrace_77628 : CollatzResearch.WordTrace tailWord_77628 prefixEnd_77628 26573650831551675862001 := by
  unfold tailWord_77628
  simp only [CollatzResearch.WordTrace]
  refine ⟨1415662881387244326000769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1887550508516325768001025 1415662881387244326000769)
  ·
    refine ⟨1061747161040433244500577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1415662881387244326000769 1061747161040433244500577)
    ·
      refine ⟨796310370780324933375433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1061747161040433244500577 796310370780324933375433)
      ·
        refine ⟨597232778085243700031575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 796310370780324933375433 597232778085243700031575)
        ·
          refine ⟨895849167127865550047363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 597232778085243700031575 895849167127865550047363)
          ·
            refine ⟨1343773750691798325071045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 895849167127865550047363 1343773750691798325071045)
            ·
              refine ⟨251957578254712185950821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1343773750691798325071045 251957578254712185950821)
              ·
                refine ⟨47242045922758534865779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 251957578254712185950821 47242045922758534865779)
                ·
                  refine ⟨70863068884137802298669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47242045922758534865779 70863068884137802298669)
                  ·
                    refine ⟨26573650831551675862001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 70863068884137802298669 26573650831551675862001)
                    ·
                      rfl

theorem cell22_77628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 4, 4, 1, 3].length) (baseStart_77628 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_77628 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_77628 prefixEnd_77628 := by exact prefixLift 77628
  have htrace : WordTrace (prefixWord ++ tailWord_77628) baseStart_77628 baseEnd_77628 := by
    simpa [prefixWord, tailWord_77628, baseEnd_77628] using wordTrace_append hprefix tailTrace_77628
  have hstable : (prefixWord ++ tailWord_77628).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_77628).length < 2 ^ (prefixWord ++ tailWord_77628).sum := by decide
  have hdescent : baseEnd_77628 < baseStart_77628 := by decide
  rcases family_descends (prefixWord ++ tailWord_77628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_77639 : List Nat := [1, 1, 4, 1, 2, 1, 4, 1, 2, 5]
def baseStart_77639 : Nat := 118140960795 + 77639 * 2 ^ 59
def prefixEnd_77639 : Nat := 4983230072969 + 3 ^ 40 * 77639 * 2
def baseEnd_77639 : Nat := 26577416356351313836967

theorem tailTrace_77639 : CollatzResearch.WordTrace tailWord_77639 prefixEnd_77639 26577416356351313836967 := by
  unfold tailWord_77639
  simp only [CollatzResearch.WordTrace]
  refine ⟨2831726965734637530651971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1887817977156425020434647 2831726965734637530651971)
  ·
    refine ⟨4247590448601956295977957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2831726965734637530651971 4247590448601956295977957)
    ·
      refine ⟨796423209112866805495867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4247590448601956295977957 796423209112866805495867)
      ·
        refine ⟨1194634813669300208243801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 796423209112866805495867 1194634813669300208243801)
        ·
          refine ⟨895976110251975156182851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1194634813669300208243801 895976110251975156182851)
          ·
            refine ⟨1343964165377962734274277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 895976110251975156182851 1343964165377962734274277)
            ·
              refine ⟨251993281008368012676427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1343964165377962734274277 251993281008368012676427)
              ·
                refine ⟨377989921512552019014641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 251993281008368012676427 377989921512552019014641)
                ·
                  refine ⟨283492441134414014260981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 377989921512552019014641 283492441134414014260981)
                  ·
                    refine ⟨26577416356351313836967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 283492441134414014260981 26577416356351313836967)
                    ·
                      rfl

theorem cell22_77639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 4, 1, 2, 5].length) (baseStart_77639 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_77639 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_77639 prefixEnd_77639 := by exact prefixLift 77639
  have htrace : WordTrace (prefixWord ++ tailWord_77639) baseStart_77639 baseEnd_77639 := by
    simpa [prefixWord, tailWord_77639, baseEnd_77639] using wordTrace_append hprefix tailTrace_77639
  have hstable : (prefixWord ++ tailWord_77639).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_77639).length < 2 ^ (prefixWord ++ tailWord_77639).sum := by decide
  have hdescent : baseEnd_77639 < baseStart_77639 := by decide
  rcases family_descends (prefixWord ++ tailWord_77639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_77641 : List Nat := [1, 2, 1, 1, 2, 4, 5, 1, 5]
def baseStart_77641 : Nat := 118140960795 + 77641 * 2 ^ 59
def prefixEnd_77641 : Nat := 4983230072969 + 3 ^ 40 * 77641 * 2
def baseEnd_77641 : Nat := 8859366999074658428987

theorem tailTrace_77641 : CollatzResearch.WordTrace tailWord_77641 prefixEnd_77641 8859366999074658428987 := by
  unfold tailWord_77641
  simp only [CollatzResearch.WordTrace]
  refine ⟨2831799911727391872224777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1887866607818261248149851 2831799911727391872224777)
  ·
    refine ⟨2123849933795543904168583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2831799911727391872224777 2123849933795543904168583)
    ·
      refine ⟨3185774900693315856252875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2123849933795543904168583 3185774900693315856252875)
      ·
        refine ⟨4778662351039973784379313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3185774900693315856252875 4778662351039973784379313)
        ·
          refine ⟨3583996763279980338284485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4778662351039973784379313 3583996763279980338284485)
          ·
            refine ⟨671999393114996313428341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3583996763279980338284485 671999393114996313428341)
            ·
              refine ⟨62999943104530904383907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 671999393114996313428341 62999943104530904383907)
              ·
                refine ⟨94499914656796356575861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62999943104530904383907 94499914656796356575861)
                ·
                  refine ⟨8859366999074658428987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 94499914656796356575861 8859366999074658428987)
                  ·
                    rfl

theorem cell22_77641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 5, 1, 5].length) (baseStart_77641 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_77641 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_77641 prefixEnd_77641 := by exact prefixLift 77641
  have htrace : WordTrace (prefixWord ++ tailWord_77641) baseStart_77641 baseEnd_77641 := by
    simpa [prefixWord, tailWord_77641, baseEnd_77641] using wordTrace_append hprefix tailTrace_77641
  have hstable : (prefixWord ++ tailWord_77641).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_77641).length < 2 ^ (prefixWord ++ tailWord_77641).sum := by decide
  have hdescent : baseEnd_77641 < baseStart_77641 := by decide
  rcases family_descends (prefixWord ++ tailWord_77641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_77671 : List Nat := [1, 1, 5, 1, 2, 1, 1, 5, 1, 4]
def baseStart_77671 : Nat := 118140960795 + 77671 * 2 ^ 59
def prefixEnd_77671 : Nat := 4983230072969 + 3 ^ 40 * 77671 * 2
def baseEnd_77671 : Nat := 26588370610313897036869

theorem tailTrace_77671 : CollatzResearch.WordTrace tailWord_77671 prefixEnd_77671 26588370610313897036869 := by
  unfold tailWord_77671
  simp only [CollatzResearch.WordTrace]
  refine ⟨2832894101618706995816867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1888596067745804663877911 2832894101618706995816867)
  ·
    refine ⟨4249341152428060493725301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2832894101618706995816867 4249341152428060493725301)
    ·
      refine ⟨398375733040130671286747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4249341152428060493725301 398375733040130671286747)
      ·
        refine ⟨597563599560196006930121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 398375733040130671286747 597563599560196006930121)
        ·
          refine ⟨448172699670147005197591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 597563599560196006930121 448172699670147005197591)
          ·
            refine ⟨672259049505220507796387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 448172699670147005197591 672259049505220507796387)
            ·
              refine ⟨1008388574257830761694581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 672259049505220507796387 1008388574257830761694581)
              ·
                refine ⟨94536428836671633908867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1008388574257830761694581 94536428836671633908867)
                ·
                  refine ⟨141804643255007450863301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 94536428836671633908867 141804643255007450863301)
                  ·
                    refine ⟨26588370610313897036869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 141804643255007450863301 26588370610313897036869)
                    ·
                      rfl

theorem cell22_77671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 5, 1, 4].length) (baseStart_77671 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_77671 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_77671 prefixEnd_77671 := by exact prefixLift 77671
  have htrace : WordTrace (prefixWord ++ tailWord_77671) baseStart_77671 baseEnd_77671 := by
    simpa [prefixWord, tailWord_77671, baseEnd_77671] using wordTrace_append hprefix tailTrace_77671
  have hstable : (prefixWord ++ tailWord_77671).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_77671).length < 2 ^ (prefixWord ++ tailWord_77671).sum := by decide
  have hdescent : baseEnd_77671 < baseStart_77671 := by decide
  rcases family_descends (prefixWord ++ tailWord_77671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_77735 : List Nat := [1, 1, 6, 1, 2, 2, 2, 2, 2, 3]
def baseStart_77735 : Nat := 118140960795 + 77735 * 2 ^ 59
def prefixEnd_77735 : Nat := 4983230072969 + 3 ^ 40 * 77735 * 2
def baseEnd_77735 : Nat := 26610279118239063436673

theorem tailTrace_77735 : CollatzResearch.WordTrace tailWord_77735 prefixEnd_77735 26610279118239063436673 := by
  unfold tailWord_77735
  simp only [CollatzResearch.WordTrace]
  refine ⟨2835228373386845926146659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1890152248924563950764439 2835228373386845926146659)
  ·
    refine ⟨4252842560080268889219989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2835228373386845926146659 4252842560080268889219989)
    ·
      refine ⟨199351995003762604182187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 4252842560080268889219989 199351995003762604182187)
      ·
        refine ⟨299027992505643906273281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 199351995003762604182187 299027992505643906273281)
        ·
          refine ⟨224270994379232929704961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 299027992505643906273281 224270994379232929704961)
          ·
            refine ⟨168203245784424697278721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 224270994379232929704961 168203245784424697278721)
            ·
              refine ⟨126152434338318522959041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 168203245784424697278721 126152434338318522959041)
              ·
                refine ⟨94614325753738892219281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 126152434338318522959041 94614325753738892219281)
                ·
                  refine ⟨70960744315304169164461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 94614325753738892219281 70960744315304169164461)
                  ·
                    refine ⟨26610279118239063436673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 70960744315304169164461 26610279118239063436673)
                    ·
                      rfl

theorem cell22_77735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 2, 2, 2, 3].length) (baseStart_77735 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_77735 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_77735 prefixEnd_77735 := by exact prefixLift 77735
  have htrace : WordTrace (prefixWord ++ tailWord_77735) baseStart_77735 baseEnd_77735 := by
    simpa [prefixWord, tailWord_77735, baseEnd_77735] using wordTrace_append hprefix tailTrace_77735
  have hstable : (prefixWord ++ tailWord_77735).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_77735).length < 2 ^ (prefixWord ++ tailWord_77735).sum := by decide
  have hdescent : baseEnd_77735 < baseStart_77735 := by decide
  rcases family_descends (prefixWord ++ tailWord_77735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_77746 : List Nat := [3, 2, 1, 1, 1, 1, 1, 2, 7, 3]
def baseStart_77746 : Nat := 118140960795 + 77746 * 2 ^ 59
def prefixEnd_77746 : Nat := 4983230072969 + 3 ^ 40 * 77746 * 2
def baseEnd_77746 : Nat := 26614044643038701411639

theorem tailTrace_77746 : CollatzResearch.WordTrace tailWord_77746 prefixEnd_77746 26614044643038701411639 := by
  unfold tailWord_77746
  simp only [CollatzResearch.WordTrace]
  refine ⟨708907394086748701199273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1890419717564663203198061 708907394086748701199273)
  ·
    refine ⟨531680545565061525899455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 708907394086748701199273 531680545565061525899455)
    ·
      refine ⟨797520818347592288849183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 531680545565061525899455 797520818347592288849183)
      ·
        refine ⟨1196281227521388433273775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 797520818347592288849183 1196281227521388433273775)
        ·
          refine ⟨1794421841282082649910663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1196281227521388433273775 1794421841282082649910663)
          ·
            refine ⟨2691632761923123974865995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1794421841282082649910663 2691632761923123974865995)
            ·
              refine ⟨4037449142884685962298993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2691632761923123974865995 4037449142884685962298993)
              ·
                refine ⟨3028086857163514471724245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4037449142884685962298993 3028086857163514471724245)
                ·
                  refine ⟨70970785714769870431037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3028086857163514471724245 70970785714769870431037)
                  ·
                    refine ⟨26614044643038701411639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 70970785714769870431037 26614044643038701411639)
                    ·
                      rfl

theorem cell22_77746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 2, 7, 3].length) (baseStart_77746 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_77746 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_77746 prefixEnd_77746 := by exact prefixLift 77746
  have htrace : WordTrace (prefixWord ++ tailWord_77746) baseStart_77746 baseEnd_77746 := by
    simpa [prefixWord, tailWord_77746, baseEnd_77746] using wordTrace_append hprefix tailTrace_77746
  have hstable : (prefixWord ++ tailWord_77746).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_77746).length < 2 ^ (prefixWord ++ tailWord_77746).sum := by decide
  have hdescent : baseEnd_77746 < baseStart_77746 := by decide
  rcases family_descends (prefixWord ++ tailWord_77746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_77791 : List Nat := [1, 1, 2, 3, 4, 1, 1, 2, 2, 5]
def baseStart_77791 : Nat := 118140960795 + 77791 * 2 ^ 59
def prefixEnd_77791 : Nat := 4983230072969 + 3 ^ 40 * 77791 * 2
def baseEnd_77791 : Nat := 26629449062673584036501

theorem tailTrace_77791 : CollatzResearch.WordTrace tailWord_77791 prefixEnd_77791 26629449062673584036501 := by
  unfold tailWord_77791
  simp only [CollatzResearch.WordTrace]
  refine ⟨2837270861183967490185227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1891513907455978326790151 2837270861183967490185227)
  ·
    refine ⟨4255906291775951235277841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2837270861183967490185227 4255906291775951235277841)
    ·
      refine ⟨3191929718831963426458381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4255906291775951235277841 3191929718831963426458381)
      ·
        refine ⟨1196973644561986284921893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3191929718831963426458381 1196973644561986284921893)
        ·
          refine ⟨224432558355372428422855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1196973644561986284921893 224432558355372428422855)
          ·
            refine ⟨336648837533058642634283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 224432558355372428422855 336648837533058642634283)
            ·
              refine ⟨504973256299587963951425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 336648837533058642634283 504973256299587963951425)
              ·
                refine ⟨378729942224690972963569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 504973256299587963951425 378729942224690972963569)
                ·
                  refine ⟨284047456668518229722677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 378729942224690972963569 284047456668518229722677)
                  ·
                    refine ⟨26629449062673584036501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 284047456668518229722677 26629449062673584036501)
                    ·
                      rfl

theorem cell22_77791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 2, 2, 5].length) (baseStart_77791 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_77791 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_77791 prefixEnd_77791 := by exact prefixLift 77791
  have htrace : WordTrace (prefixWord ++ tailWord_77791) baseStart_77791 baseEnd_77791 := by
    simpa [prefixWord, tailWord_77791, baseEnd_77791] using wordTrace_append hprefix tailTrace_77791
  have hstable : (prefixWord ++ tailWord_77791).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_77791).length < 2 ^ (prefixWord ++ tailWord_77791).sum := by decide
  have hdescent : baseEnd_77791 < baseStart_77791 := by decide
  rcases family_descends (prefixWord ++ tailWord_77791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_77821 : List Nat := [1, 4, 1, 1, 1, 2, 4, 2, 6]
def baseStart_77821 : Nat := 118140960795 + 77821 * 2 ^ 59
def prefixEnd_77821 : Nat := 4983230072969 + 3 ^ 40 * 77821 * 2
def baseEnd_77821 : Nat := 8879906225254501928803

theorem tailTrace_77821 : CollatzResearch.WordTrace tailWord_77821 prefixEnd_77821 8879906225254501928803 := by
  unfold tailWord_77821
  simp only [CollatzResearch.WordTrace]
  refine ⟨2838365051075282613777317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1892243367383521742518211 2838365051075282613777317)
  ·
    refine ⟨532193447076615490083247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2838365051075282613777317 532193447076615490083247)
    ·
      refine ⟨798290170614923235124871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 532193447076615490083247 798290170614923235124871)
      ·
        refine ⟨1197435255922384852687307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 798290170614923235124871 1197435255922384852687307)
        ·
          refine ⟨1796152883883577279030961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1197435255922384852687307 1796152883883577279030961)
          ·
            refine ⟨1347114662912682959273221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1796152883883577279030961 1347114662912682959273221)
            ·
              refine ⟨252583999296128054863729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1347114662912682959273221 252583999296128054863729)
              ·
                refine ⟨189437999472096041147797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 252583999296128054863729 189437999472096041147797)
                ·
                  refine ⟨8879906225254501928803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 189437999472096041147797 8879906225254501928803)
                  ·
                    rfl

theorem cell22_77821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 4, 2, 6].length) (baseStart_77821 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_77821 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_77821 prefixEnd_77821 := by exact prefixLift 77821
  have htrace : WordTrace (prefixWord ++ tailWord_77821) baseStart_77821 baseEnd_77821 := by
    simpa [prefixWord, tailWord_77821, baseEnd_77821] using wordTrace_append hprefix tailTrace_77821
  have hstable : (prefixWord ++ tailWord_77821).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_77821).length < 2 ^ (prefixWord ++ tailWord_77821).sum := by decide
  have hdescent : baseEnd_77821 < baseStart_77821 := by decide
  rcases family_descends (prefixWord ++ tailWord_77821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_77836 : List Nat := [2, 2, 1, 2, 3, 1, 2, 1, 3, 5]
def baseStart_77836 : Nat := 118140960795 + 77836 * 2 ^ 59
def prefixEnd_77836 : Nat := 4983230072969 + 3 ^ 40 * 77836 * 2
def baseEnd_77836 : Nat := 26644853482308466661363

theorem tailTrace_77836 : CollatzResearch.WordTrace tailWord_77836 prefixEnd_77836 26644853482308466661363 := by
  unfold tailWord_77836
  simp only [CollatzResearch.WordTrace]
  refine ⟨1419456073010470087786681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1892608097347293450382241 1419456073010470087786681)
  ·
    refine ⟨1064592054757852565840011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1419456073010470087786681 1064592054757852565840011)
    ·
      refine ⟨1596888082136778848760017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1064592054757852565840011 1596888082136778848760017)
      ·
        refine ⟨1197666061602584136570013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1596888082136778848760017 1197666061602584136570013)
        ·
          refine ⟨449124773100969051213755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1197666061602584136570013 449124773100969051213755)
          ·
            refine ⟨673687159651453576820633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 449124773100969051213755 673687159651453576820633)
            ·
              refine ⟨505265369738590182615475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 673687159651453576820633 505265369738590182615475)
              ·
                refine ⟨757898054607885273923213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 505265369738590182615475 757898054607885273923213)
                ·
                  refine ⟨284211770477956977721205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 757898054607885273923213 284211770477956977721205)
                  ·
                    refine ⟨26644853482308466661363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 284211770477956977721205 26644853482308466661363)
                    ·
                      rfl

theorem cell22_77836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 1, 3, 5].length) (baseStart_77836 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_77836 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_77836 prefixEnd_77836 := by exact prefixLift 77836
  have htrace : WordTrace (prefixWord ++ tailWord_77836) baseStart_77836 baseEnd_77836 := by
    simpa [prefixWord, tailWord_77836, baseEnd_77836] using wordTrace_append hprefix tailTrace_77836
  have hstable : (prefixWord ++ tailWord_77836).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_77836).length < 2 ^ (prefixWord ++ tailWord_77836).sum := by decide
  have hdescent : baseEnd_77836 < baseStart_77836 := by decide
  rcases family_descends (prefixWord ++ tailWord_77836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_77855 : List Nat := [1, 1, 2, 4, 1, 2, 5, 2, 4]
def baseStart_77855 : Nat := 118140960795 + 77855 * 2 ^ 59
def prefixEnd_77855 : Nat := 4983230072969 + 3 ^ 40 * 77855 * 2
def baseEnd_77855 : Nat := 8883785856866250145435

theorem tailTrace_77855 : CollatzResearch.WordTrace tailWord_77855 prefixEnd_77855 8883785856866250145435 := by
  unfold tailWord_77855
  simp only [CollatzResearch.WordTrace]
  refine ⟨2839605132952106420515019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1893070088634737613676679 2839605132952106420515019)
  ·
    refine ⟨4259407699428159630772529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2839605132952106420515019 4259407699428159630772529)
    ·
      refine ⟨3194555774571119723079397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4259407699428159630772529 3194555774571119723079397)
      ·
        refine ⟨598979207732084948077387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3194555774571119723079397 598979207732084948077387)
        ·
          refine ⟨898468811598127422116081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 598979207732084948077387 898468811598127422116081)
          ·
            refine ⟨673851608698595566587061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 898468811598127422116081 673851608698595566587061)
            ·
              refine ⟨63173588315493334367537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 673851608698595566587061 63173588315493334367537)
              ·
                refine ⟨47380191236620000775653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 63173588315493334367537 47380191236620000775653)
                ·
                  refine ⟨8883785856866250145435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 47380191236620000775653 8883785856866250145435)
                  ·
                    rfl

theorem cell22_77855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 5, 2, 4].length) (baseStart_77855 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_77855 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_77855 prefixEnd_77855 := by exact prefixLift 77855
  have htrace : WordTrace (prefixWord ++ tailWord_77855) baseStart_77855 baseEnd_77855 := by
    simpa [prefixWord, tailWord_77855, baseEnd_77855] using wordTrace_append hprefix tailTrace_77855
  have hstable : (prefixWord ++ tailWord_77855).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_77855).length < 2 ^ (prefixWord ++ tailWord_77855).sum := by decide
  have hdescent : baseEnd_77855 < baseStart_77855 := by decide
  rcases family_descends (prefixWord ++ tailWord_77855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_77911 : List Nat := [1, 1, 3, 2, 2, 1, 2, 3, 7]
def baseStart_77911 : Nat := 118140960795 + 77911 * 2 ^ 59
def prefixEnd_77911 : Nat := 4983230072969 + 3 ^ 40 * 77911 * 2
def baseEnd_77911 : Nat := 8890175838344423678711

theorem tailTrace_77911 : CollatzResearch.WordTrace tailWord_77911 prefixEnd_77911 8890175838344423678711 := by
  unfold tailWord_77911
  simp only [CollatzResearch.WordTrace]
  refine ⟨2841647620749227984553587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1894431747166151989702391 2841647620749227984553587)
  ·
    refine ⟨4262471431123841976830381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2841647620749227984553587 4262471431123841976830381)
    ·
      refine ⟨1598426786671440741311393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4262471431123841976830381 1598426786671440741311393)
      ·
        refine ⟨1198820090003580555983545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1598426786671440741311393 1198820090003580555983545)
        ·
          refine ⟨899115067502685416987659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1198820090003580555983545 899115067502685416987659)
          ·
            refine ⟨1348672601254028125481489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 899115067502685416987659 1348672601254028125481489)
            ·
              refine ⟨1011504450940521094111117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1348672601254028125481489 1011504450940521094111117)
              ·
                refine ⟨379314169102695410291669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1011504450940521094111117 379314169102695410291669)
                ·
                  refine ⟨8890175838344423678711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 379314169102695410291669 8890175838344423678711)
                  ·
                    rfl

theorem cell22_77911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 3, 7].length) (baseStart_77911 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_77911 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_77911 prefixEnd_77911 := by exact prefixLift 77911
  have htrace : WordTrace (prefixWord ++ tailWord_77911) baseStart_77911 baseEnd_77911 := by
    simpa [prefixWord, tailWord_77911, baseEnd_77911] using wordTrace_append hprefix tailTrace_77911
  have hstable : (prefixWord ++ tailWord_77911).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_77911).length < 2 ^ (prefixWord ++ tailWord_77911).sum := by decide
  have hdescent : baseEnd_77911 < baseStart_77911 := by decide
  rcases family_descends (prefixWord ++ tailWord_77911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_77973 : List Nat := [1, 3, 2, 1, 1, 1, 6, 1, 6]
def baseStart_77973 : Nat := 118140960795 + 77973 * 2 ^ 59
def prefixEnd_77973 : Nat := 4983230072969 + 3 ^ 40 * 77973 * 2
def baseEnd_77973 : Nat := 8897250460695258661981

theorem tailTrace_77973 : CollatzResearch.WordTrace tailWord_77973 prefixEnd_77973 8897250460695258661981 := by
  unfold tailWord_77973
  simp only [CollatzResearch.WordTrace]
  refine ⟨2843908946524612573310573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1895939297683075048873715 2843908946524612573310573)
  ·
    refine ⟨1066465854946729714991465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2843908946524612573310573 1066465854946729714991465)
    ·
      refine ⟨799849391210047286243599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1066465854946729714991465 799849391210047286243599)
      ·
        refine ⟨1199774086815070929365399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 799849391210047286243599 1199774086815070929365399)
        ·
          refine ⟨1799661130222606394048099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1199774086815070929365399 1799661130222606394048099)
          ·
            refine ⟨2699491695333909591072149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1799661130222606394048099 2699491695333909591072149)
            ·
              refine ⟨126538673218777012081507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 2699491695333909591072149 126538673218777012081507)
              ·
                refine ⟨189808009828165518122261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 126538673218777012081507 189808009828165518122261)
                ·
                  refine ⟨8897250460695258661981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 189808009828165518122261 8897250460695258661981)
                  ·
                    rfl

theorem cell22_77973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 6, 1, 6].length) (baseStart_77973 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_77973 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_77973 prefixEnd_77973 := by exact prefixLift 77973
  have htrace : WordTrace (prefixWord ++ tailWord_77973) baseStart_77973 baseEnd_77973 := by
    simpa [prefixWord, tailWord_77973, baseEnd_77973] using wordTrace_append hprefix tailTrace_77973
  have hstable : (prefixWord ++ tailWord_77973).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_77973).length < 2 ^ (prefixWord ++ tailWord_77973).sum := by decide
  have hdescent : baseEnd_77973 < baseStart_77973 := by decide
  rcases family_descends (prefixWord ++ tailWord_77973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_78003 : List Nat := [1, 1, 1, 2, 3, 2, 1, 5, 2, 4]
def baseStart_78003 : Nat := 118140960795 + 78003 * 2 ^ 59
def prefixEnd_78003 : Nat := 4983230072969 + 3 ^ 40 * 78003 * 2
def baseEnd_78003 : Nat := 26702020995175697735851

theorem tailTrace_78003 : CollatzResearch.WordTrace tailWord_78003 prefixEnd_78003 26702020995175697735851 := by
  unfold tailWord_78003
  simp only [CollatzResearch.WordTrace]
  refine ⟨2845003136415927696902663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1896668757610618464601775 2845003136415927696902663)
  ·
    refine ⟨4267504704623891545353995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2845003136415927696902663 4267504704623891545353995)
    ·
      refine ⟨6401257056935837318030993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4267504704623891545353995 6401257056935837318030993)
      ·
        refine ⟨4800942792701877988523245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6401257056935837318030993 4800942792701877988523245)
        ·
          refine ⟨1800353547263204245696217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4800942792701877988523245 1800353547263204245696217)
          ·
            refine ⟨1350265160447403184272163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1800353547263204245696217 1350265160447403184272163)
            ·
              refine ⟨2025397740671104776408245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1350265160447403184272163 2025397740671104776408245)
              ·
                refine ⟨189881038187916072788273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2025397740671104776408245 189881038187916072788273)
                ·
                  refine ⟨142410778640937054591205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 189881038187916072788273 142410778640937054591205)
                  ·
                    refine ⟨26702020995175697735851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 142410778640937054591205 26702020995175697735851)
                    ·
                      rfl

theorem cell22_78003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 5, 2, 4].length) (baseStart_78003 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_78003 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_78003 prefixEnd_78003 := by exact prefixLift 78003
  have htrace : WordTrace (prefixWord ++ tailWord_78003) baseStart_78003 baseEnd_78003 := by
    simpa [prefixWord, tailWord_78003, baseEnd_78003] using wordTrace_append hprefix tailTrace_78003
  have hstable : (prefixWord ++ tailWord_78003).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_78003).length < 2 ^ (prefixWord ++ tailWord_78003).sum := by decide
  have hdescent : baseEnd_78003 < baseStart_78003 := by decide
  rcases family_descends (prefixWord ++ tailWord_78003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_78007 : List Nat := [1, 1, 3, 1, 4, 4, 1, 3, 4]
def baseStart_78007 : Nat := 118140960795 + 78007 * 2 ^ 59
def prefixEnd_78007 : Nat := 4983230072969 + 3 ^ 40 * 78007 * 2
def baseEnd_78007 : Nat := 8901130092307006878613

theorem tailTrace_78007 : CollatzResearch.WordTrace tailWord_78007 prefixEnd_78007 8901130092307006878613 := by
  unfold tailWord_78007
  simp only [CollatzResearch.WordTrace]
  refine ⟨2845149028401436380048275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1896766018934290920032183 2845149028401436380048275)
  ·
    refine ⟨4267723542602154570072413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2845149028401436380048275 4267723542602154570072413)
    ·
      refine ⟨1600396328475807963777155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4267723542602154570072413 1600396328475807963777155)
      ·
        refine ⟨2400594492713711945665733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1600396328475807963777155 2400594492713711945665733)
        ·
          refine ⟨450111467383820989812325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2400594492713711945665733 450111467383820989812325)
          ·
            refine ⟨84395900134466435589811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 450111467383820989812325 84395900134466435589811)
            ·
              refine ⟨126593850201699653384717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84395900134466435589811 126593850201699653384717)
              ·
                refine ⟨47472693825637370019269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 126593850201699653384717 47472693825637370019269)
                ·
                  refine ⟨8901130092307006878613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 47472693825637370019269 8901130092307006878613)
                  ·
                    rfl

theorem cell22_78007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 4, 1, 3, 4].length) (baseStart_78007 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_78007 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_78007 prefixEnd_78007 := by exact prefixLift 78007
  have htrace : WordTrace (prefixWord ++ tailWord_78007) baseStart_78007 baseEnd_78007 := by
    simpa [prefixWord, tailWord_78007, baseEnd_78007] using wordTrace_append hprefix tailTrace_78007
  have hstable : (prefixWord ++ tailWord_78007).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_78007).length < 2 ^ (prefixWord ++ tailWord_78007).sum := by decide
  have hdescent : baseEnd_78007 < baseStart_78007 := by decide
  rcases family_descends (prefixWord ++ tailWord_78007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_78020 : List Nat := [2, 3, 3, 1, 2, 1, 1, 1, 4, 4]
def baseStart_78020 : Nat := 118140960795 + 78020 * 2 ^ 59
def prefixEnd_78020 : Nat := 4983230072969 + 3 ^ 40 * 78020 * 2
def baseEnd_78020 : Nat := 26707840442593320060799

theorem tailTrace_78020 : CollatzResearch.WordTrace tailWord_78020 prefixEnd_78020 26707840442593320060799 := by
  unfold tailWord_78020
  simp only [CollatzResearch.WordTrace]
  refine ⟨1422811588677169800135757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1897082118236226400181009 1422811588677169800135757)
  ·
    refine ⟨533554345753938675050909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1422811588677169800135757 533554345753938675050909)
    ·
      refine ⟨200082879657727003144091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 533554345753938675050909 200082879657727003144091)
      ·
        refine ⟨300124319486590504716137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 200082879657727003144091 300124319486590504716137)
        ·
          refine ⟨225093239614942878537103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 300124319486590504716137 225093239614942878537103)
          ·
            refine ⟨337639859422414317805655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 225093239614942878537103 337639859422414317805655)
            ·
              refine ⟨506459789133621476708483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 337639859422414317805655 506459789133621476708483)
              ·
                refine ⟨759689683700432215062725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 506459789133621476708483 759689683700432215062725)
                ·
                  refine ⟨142441815693831040324261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 759689683700432215062725 142441815693831040324261)
                  ·
                    refine ⟨26707840442593320060799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 142441815693831040324261 26707840442593320060799)
                    ·
                      rfl

theorem cell22_78020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 1, 4, 4].length) (baseStart_78020 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_78020 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_78020 prefixEnd_78020 := by exact prefixLift 78020
  have htrace : WordTrace (prefixWord ++ tailWord_78020) baseStart_78020 baseEnd_78020 := by
    simpa [prefixWord, tailWord_78020, baseEnd_78020] using wordTrace_append hprefix tailTrace_78020
  have hstable : (prefixWord ++ tailWord_78020).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_78020).length < 2 ^ (prefixWord ++ tailWord_78020).sum := by decide
  have hdescent : baseEnd_78020 < baseStart_78020 := by decide
  rcases family_descends (prefixWord ++ tailWord_78020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_78067 : List Nat := [1, 1, 1, 2, 2, 4, 2, 5, 1, 3]
def baseStart_78067 : Nat := 118140960795 + 78067 * 2 ^ 59
def prefixEnd_78067 : Nat := 4983230072969 + 3 ^ 40 * 78067 * 2
def baseEnd_78067 : Nat := 26723929503100864135655

theorem tailTrace_78067 : CollatzResearch.WordTrace tailWord_78067 prefixEnd_78067 26723929503100864135655 := by
  unfold tailWord_78067
  simp only [CollatzResearch.WordTrace]
  refine ⟨2847337408184066627232455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1898224938789377751488303 2847337408184066627232455)
  ·
    refine ⟨4271006112276099940848683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2847337408184066627232455 4271006112276099940848683)
    ·
      refine ⟨6406509168414149911273025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4271006112276099940848683 6406509168414149911273025)
      ·
        refine ⟨4804881876310612433454769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6406509168414149911273025 4804881876310612433454769)
        ·
          refine ⟨3603661407232959325091077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4804881876310612433454769 3603661407232959325091077)
          ·
            refine ⟨675686513856179873454577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3603661407232959325091077 675686513856179873454577)
            ·
              refine ⟨506764885392134905090933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 675686513856179873454577 506764885392134905090933)
              ·
                refine ⟨47509208005512647352275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 506764885392134905090933 47509208005512647352275)
                ·
                  refine ⟨71263812008268971028413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47509208005512647352275 71263812008268971028413)
                  ·
                    refine ⟨26723929503100864135655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 71263812008268971028413 26723929503100864135655)
                    ·
                      rfl

theorem cell22_78067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 5, 1, 3].length) (baseStart_78067 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_78067 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_78067 prefixEnd_78067 := by exact prefixLift 78067
  have htrace : WordTrace (prefixWord ++ tailWord_78067) baseStart_78067 baseEnd_78067 := by
    simpa [prefixWord, tailWord_78067, baseEnd_78067] using wordTrace_append hprefix tailTrace_78067
  have hstable : (prefixWord ++ tailWord_78067).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_78067).length < 2 ^ (prefixWord ++ tailWord_78067).sum := by decide
  have hdescent : baseEnd_78067 < baseStart_78067 := by decide
  rcases family_descends (prefixWord ++ tailWord_78067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_78127 : List Nat := [1, 1, 2, 1, 2, 1, 8, 1, 1, 4]
def baseStart_78127 : Nat := 118140960795 + 78127 * 2 ^ 59
def prefixEnd_78127 : Nat := 4983230072969 + 3 ^ 40 * 78127 * 2
def baseEnd_78127 : Nat := 26744468729280707635471

theorem tailTrace_78127 : CollatzResearch.WordTrace tailWord_78127 prefixEnd_78127 26744468729280707635471 := by
  unfold tailWord_78127
  simp only [CollatzResearch.WordTrace]
  refine ⟨2849525787966696874416635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1899683858644464582944423 2849525787966696874416635)
  ·
    refine ⟨4274288681950045311624953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2849525787966696874416635 4274288681950045311624953)
    ·
      refine ⟨3205716511462533983718715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4274288681950045311624953 3205716511462533983718715)
      ·
        refine ⟨4808574767193800975578073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3205716511462533983718715 4808574767193800975578073)
        ·
          refine ⟨3606431075395350731683555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4808574767193800975578073 3606431075395350731683555)
          ·
            refine ⟨5409646613093026097525333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3606431075395350731683555 5409646613093026097525333)
            ·
              refine ⟨63394296247183899580375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 5409646613093026097525333 63394296247183899580375)
              ·
                refine ⟨95091444370775849370563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63394296247183899580375 95091444370775849370563)
                ·
                  refine ⟨142637166556163774055845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 95091444370775849370563 142637166556163774055845)
                  ·
                    refine ⟨26744468729280707635471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 142637166556163774055845 26744468729280707635471)
                    ·
                      rfl

theorem cell22_78127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 8, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 8, 1, 1, 4].length) (baseStart_78127 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_78127 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_78127 prefixEnd_78127 := by exact prefixLift 78127
  have htrace : WordTrace (prefixWord ++ tailWord_78127) baseStart_78127 baseEnd_78127 := by
    simpa [prefixWord, tailWord_78127, baseEnd_78127] using wordTrace_append hprefix tailTrace_78127
  have hstable : (prefixWord ++ tailWord_78127).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_78127).length < 2 ^ (prefixWord ++ tailWord_78127).sum := by decide
  have hdescent : baseEnd_78127 < baseStart_78127 := by decide
  rcases family_descends (prefixWord ++ tailWord_78127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_78142 : List Nat := [4, 2, 1, 2, 1, 3, 2, 1, 6]
def baseStart_78142 : Nat := 118140960795 + 78142 * 2 ^ 59
def prefixEnd_78142 : Nat := 4983230072969 + 3 ^ 40 * 78142 * 2
def baseEnd_78142 : Nat := 8916534511941889503475

theorem tailTrace_78142 : CollatzResearch.WordTrace tailWord_78142 prefixEnd_78142 8916534511941889503475 := by
  unfold tailWord_78142
  simp only [CollatzResearch.WordTrace]
  refine ⟨356259110364044304526585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1900048588608236290808453 356259110364044304526585)
  ·
    refine ⟨267194332773033228394939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 356259110364044304526585 267194332773033228394939)
    ·
      refine ⟨400791499159549842592409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 267194332773033228394939 400791499159549842592409)
      ·
        refine ⟨300593624369662381944307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 400791499159549842592409 300593624369662381944307)
        ·
          refine ⟨450890436554493572916461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 300593624369662381944307 450890436554493572916461)
          ·
            refine ⟨169083913707935089843673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 450890436554493572916461 169083913707935089843673)
            ·
              refine ⟨126812935280951317382755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 169083913707935089843673 126812935280951317382755)
              ·
                refine ⟨190219402921426976074133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 126812935280951317382755 190219402921426976074133)
                ·
                  refine ⟨8916534511941889503475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 190219402921426976074133 8916534511941889503475)
                  ·
                    rfl

theorem cell22_78142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 2, 1, 6].length) (baseStart_78142 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_78142 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_78142 prefixEnd_78142 := by exact prefixLift 78142
  have htrace : WordTrace (prefixWord ++ tailWord_78142) baseStart_78142 baseEnd_78142 := by
    simpa [prefixWord, tailWord_78142, baseEnd_78142] using wordTrace_append hprefix tailTrace_78142
  have hstable : (prefixWord ++ tailWord_78142).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_78142).length < 2 ^ (prefixWord ++ tailWord_78142).sum := by decide
  have hdescent : baseEnd_78142 < baseStart_78142 := by decide
  rcases family_descends (prefixWord ++ tailWord_78142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_78153 : List Nat := [1, 2, 1, 1, 2, 3, 1, 11]
def baseStart_78153 : Nat := 118140960795 + 78153 * 2 ^ 59
def prefixEnd_78153 : Nat := 4983230072969 + 3 ^ 40 * 78153 * 2
def baseEnd_78153 : Nat := 2972596562291700720599

theorem tailTrace_78153 : CollatzResearch.WordTrace tailWord_78153 prefixEnd_78153 2972596562291700720599 := by
  unfold tailWord_78153
  simp only [CollatzResearch.WordTrace]
  refine ⟨2850474085872503314863113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1900316057248335543242075 2850474085872503314863113)
  ·
    refine ⟨2137855564404377486147335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2850474085872503314863113 2137855564404377486147335)
    ·
      refine ⟨3206783346606566229221003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2137855564404377486147335 3206783346606566229221003)
      ·
        refine ⟨4810175019909849343831505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3206783346606566229221003 4810175019909849343831505)
        ·
          refine ⟨3607631264932387007873629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4810175019909849343831505 3607631264932387007873629)
          ·
            refine ⟨1352861724349645127952611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3607631264932387007873629 1352861724349645127952611)
            ·
              refine ⟨2029292586524467691928917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1352861724349645127952611 2029292586524467691928917)
              ·
                refine ⟨2972596562291700720599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 2029292586524467691928917 2972596562291700720599)
                ·
                  rfl

theorem cell22_78153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 11].length) (baseStart_78153 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_78153 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_78153 prefixEnd_78153 := by exact prefixLift 78153
  have htrace : WordTrace (prefixWord ++ tailWord_78153) baseStart_78153 baseEnd_78153 := by
    simpa [prefixWord, tailWord_78153, baseEnd_78153] using wordTrace_append hprefix tailTrace_78153
  have hstable : (prefixWord ++ tailWord_78153).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_78153).length < 2 ^ (prefixWord ++ tailWord_78153).sum := by decide
  have hdescent : baseEnd_78153 < baseStart_78153 := by decide
  rcases family_descends (prefixWord ++ tailWord_78153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_78176 : List Nat := [2, 1, 1, 3, 6, 1, 1, 3, 4]
def baseStart_78176 : Nat := 118140960795 + 78176 * 2 ^ 59
def prefixEnd_78176 : Nat := 4983230072969 + 3 ^ 40 * 78176 * 2
def baseEnd_78176 : Nat := 8920414143553637720107

theorem tailTrace_78176 : CollatzResearch.WordTrace tailWord_78176 prefixEnd_78176 8920414143553637720107 := by
  unfold tailWord_78176
  simp only [CollatzResearch.WordTrace]
  refine ⟨1425656482394589121475191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1900875309859452161966921 1425656482394589121475191)
  ·
    refine ⟨2138484723591883682212787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1425656482394589121475191 2138484723591883682212787)
    ·
      refine ⟨3207727085387825523319181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2138484723591883682212787 3207727085387825523319181)
      ·
        refine ⟨1202897657020434571244693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3207727085387825523319181 1202897657020434571244693)
        ·
          refine ⟨56385827672832870527095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 1202897657020434571244693 56385827672832870527095)
          ·
            refine ⟨84578741509249305790643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56385827672832870527095 84578741509249305790643)
            ·
              refine ⟨126868112263873958685965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84578741509249305790643 126868112263873958685965)
              ·
                refine ⟨47575542098952734507237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 126868112263873958685965 47575542098952734507237)
                ·
                  refine ⟨8920414143553637720107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 47575542098952734507237 8920414143553637720107)
                  ·
                    rfl

theorem cell22_78176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 1, 1, 3, 4].length) (baseStart_78176 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_78176 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_78176 prefixEnd_78176 := by exact prefixLift 78176
  have htrace : WordTrace (prefixWord ++ tailWord_78176) baseStart_78176 baseEnd_78176 := by
    simpa [prefixWord, tailWord_78176, baseEnd_78176] using wordTrace_append hprefix tailTrace_78176
  have hstable : (prefixWord ++ tailWord_78176).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_78176).length < 2 ^ (prefixWord ++ tailWord_78176).sum := by decide
  have hdescent : baseEnd_78176 < baseStart_78176 := by decide
  rcases family_descends (prefixWord ++ tailWord_78176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_78253 : List Nat := [1, 5, 2, 2, 2, 1, 1, 4, 1, 3]
def baseStart_78253 : Nat := 118140960795 + 78253 * 2 ^ 59
def prefixEnd_78253 : Nat := 4983230072969 + 3 ^ 40 * 78253 * 2
def baseEnd_78253 : Nat := 26787601104258378985085

theorem tailTrace_78253 : CollatzResearch.WordTrace tailWord_78253 prefixEnd_78253 26787601104258378985085 := by
  unfold tailWord_78253
  simp only [CollatzResearch.WordTrace]
  refine ⟨2854121385510220393503413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1902747590340146929002275 2854121385510220393503413)
  ·
    refine ⟨267573879891583161890945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2854121385510220393503413 267573879891583161890945)
    ·
      refine ⟨200680409918687371418209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 267573879891583161890945 200680409918687371418209)
      ·
        refine ⟨150510307439015528563657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 200680409918687371418209 150510307439015528563657)
        ·
          refine ⟨112882730579261646422743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 150510307439015528563657 112882730579261646422743)
          ·
            refine ⟨169324095868892469634115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112882730579261646422743 169324095868892469634115)
            ·
              refine ⟨253986143803338704451173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 169324095868892469634115 253986143803338704451173)
              ·
                refine ⟨47622401963126007084595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 253986143803338704451173 47622401963126007084595)
                ·
                  refine ⟨71433602944689010626893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47622401963126007084595 71433602944689010626893)
                  ·
                    refine ⟨26787601104258378985085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 71433602944689010626893 26787601104258378985085)
                    ·
                      rfl

theorem cell22_78253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 1, 4, 1, 3].length) (baseStart_78253 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_78253 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_78253 prefixEnd_78253 := by exact prefixLift 78253
  have htrace : WordTrace (prefixWord ++ tailWord_78253) baseStart_78253 baseEnd_78253 := by
    simpa [prefixWord, tailWord_78253, baseEnd_78253] using wordTrace_append hprefix tailTrace_78253
  have hstable : (prefixWord ++ tailWord_78253).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_78253).length < 2 ^ (prefixWord ++ tailWord_78253).sum := by decide
  have hdescent : baseEnd_78253 < baseStart_78253 := by decide
  rcases family_descends (prefixWord ++ tailWord_78253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_78305 : List Nat := [1, 2, 3, 1, 2, 2, 11]
def baseStart_78305 : Nat := 118140960795 + 78305 * 2 ^ 59
def prefixEnd_78305 : Nat := 4983230072969 + 3 ^ 40 * 78305 * 2
def baseEnd_78305 : Nat := 992792658035095432775

theorem tailTrace_78305 : CollatzResearch.WordTrace tailWord_78305 prefixEnd_78305 992792658035095432775 := by
  unfold tailWord_78305
  simp only [CollatzResearch.WordTrace]
  refine ⟨2856017981321833274396369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1904011987547888849597579 2856017981321833274396369)
  ·
    refine ⟨2142013485991374955797277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2856017981321833274396369 2142013485991374955797277)
    ·
      refine ⟨803255057246765608423979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2142013485991374955797277 803255057246765608423979)
      ·
        refine ⟨1204882585870148412635969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 803255057246765608423979 1204882585870148412635969)
        ·
          refine ⟨903661939402611309476977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1204882585870148412635969 903661939402611309476977)
          ·
            refine ⟨677746454551958482107733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 903661939402611309476977 677746454551958482107733)
            ·
              refine ⟨992792658035095432775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 677746454551958482107733 992792658035095432775)
              ·
                rfl

theorem cell22_78305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 11].length) (baseStart_78305 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_78305 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_78305 prefixEnd_78305 := by exact prefixLift 78305
  have htrace : WordTrace (prefixWord ++ tailWord_78305) baseStart_78305 baseEnd_78305 := by
    simpa [prefixWord, tailWord_78305, baseEnd_78305] using wordTrace_append hprefix tailTrace_78305
  have hstable : (prefixWord ++ tailWord_78305).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_78305).length < 2 ^ (prefixWord ++ tailWord_78305).sum := by decide
  have hdescent : baseEnd_78305 < baseStart_78305 := by decide
  rcases family_descends (prefixWord ++ tailWord_78305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_78367 : List Nat := [1, 1, 2, 4, 1, 1, 1, 6, 5]
def baseStart_78367 : Nat := 118140960795 + 78367 * 2 ^ 59
def prefixEnd_78367 : Nat := 4983230072969 + 3 ^ 40 * 78367 * 2
def baseEnd_78367 : Nat := 8942208544666693878245

theorem tailTrace_78367 : CollatzResearch.WordTrace tailWord_78367 prefixEnd_78367 8942208544666693878245 := by
  unfold tailWord_78367
  simp only [CollatzResearch.WordTrace]
  refine ⟨2858279307097217863153355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1905519538064811908768903 2858279307097217863153355)
  ·
    refine ⟨4287418960645826794730033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2858279307097217863153355 4287418960645826794730033)
    ·
      refine ⟨3215564220484370096047525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4287418960645826794730033 3215564220484370096047525)
      ·
        refine ⟨602918291340819393008911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3215564220484370096047525 602918291340819393008911)
        ·
          refine ⟨904377437011229089513367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 602918291340819393008911 904377437011229089513367)
          ·
            refine ⟨1356566155516843634270051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 904377437011229089513367 1356566155516843634270051)
            ·
              refine ⟨2034849233275265451405077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1356566155516843634270051 2034849233275265451405077)
              ·
                refine ⟨95383557809778068034613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2034849233275265451405077 95383557809778068034613)
                ·
                  refine ⟨8942208544666693878245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 95383557809778068034613 8942208544666693878245)
                  ·
                    rfl

theorem cell22_78367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 6, 5].length) (baseStart_78367 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_78367 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_78367 prefixEnd_78367 := by exact prefixLift 78367
  have htrace : WordTrace (prefixWord ++ tailWord_78367) baseStart_78367 baseEnd_78367 := by
    simpa [prefixWord, tailWord_78367, baseEnd_78367] using wordTrace_append hprefix tailTrace_78367
  have hstable : (prefixWord ++ tailWord_78367).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_78367).length < 2 ^ (prefixWord ++ tailWord_78367).sum := by decide
  have hdescent : baseEnd_78367 < baseStart_78367 := by decide
  rcases family_descends (prefixWord ++ tailWord_78367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_78371 : List Nat := [1, 1, 1, 4, 4, 3, 1, 1, 3, 3]
def baseStart_78371 : Nat := 118140960795 + 78371 * 2 ^ 59
def prefixEnd_78371 : Nat := 4983230072969 + 3 ^ 40 * 78371 * 2
def baseEnd_78371 : Nat := 26827994915745404534723

theorem tailTrace_78371 : CollatzResearch.WordTrace tailWord_78371 prefixEnd_78371 26827994915745404534723 := by
  unfold tailWord_78371
  simp only [CollatzResearch.WordTrace]
  refine ⟨2858425199082726546298967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1905616799388484364199311 2858425199082726546298967)
  ·
    refine ⟨4287637798624089819448451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2858425199082726546298967 4287637798624089819448451)
    ·
      refine ⟨6431456697936134729172677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4287637798624089819448451 6431456697936134729172677)
      ·
        refine ⟨1205898130863025261719877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6431456697936134729172677 1205898130863025261719877)
        ·
          refine ⟨226105899536817236572477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1205898130863025261719877 226105899536817236572477)
          ·
            refine ⟨84789712326306463714679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 226105899536817236572477 84789712326306463714679)
            ·
              refine ⟨127184568489459695572019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84789712326306463714679 127184568489459695572019)
              ·
                refine ⟨190776852734189543358029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 127184568489459695572019 190776852734189543358029)
                ·
                  refine ⟨71541319775321078759261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 190776852734189543358029 71541319775321078759261)
                  ·
                    refine ⟨26827994915745404534723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 71541319775321078759261 26827994915745404534723)
                    ·
                      rfl

theorem cell22_78371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 3, 1, 1, 3, 3].length) (baseStart_78371 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_78371 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_78371 prefixEnd_78371 := by exact prefixLift 78371
  have htrace : WordTrace (prefixWord ++ tailWord_78371) baseStart_78371 baseEnd_78371 := by
    simpa [prefixWord, tailWord_78371, baseEnd_78371] using wordTrace_append hprefix tailTrace_78371
  have hstable : (prefixWord ++ tailWord_78371).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_78371).length < 2 ^ (prefixWord ++ tailWord_78371).sum := by decide
  have hdescent : baseEnd_78371 < baseStart_78371 := by decide
  rcases family_descends (prefixWord ++ tailWord_78371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_78384 : List Nat := [2, 1, 1, 1, 2, 3, 6, 1, 5]
def baseStart_78384 : Nat := 118140960795 + 78384 * 2 ^ 59
def prefixEnd_78384 : Nat := 4983230072969 + 3 ^ 40 * 78384 * 2
def baseEnd_78384 : Nat := 8944148360472567986561

theorem tailTrace_78384 : CollatzResearch.WordTrace tailWord_78384 prefixEnd_78384 8944148360472567986561 := by
  unfold tailWord_78384
  simp only [CollatzResearch.WordTrace]
  refine ⟨1429449674017814883261103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1905932898690419844348137 1429449674017814883261103)
  ·
    refine ⟨2144174511026722324891655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1429449674017814883261103 2144174511026722324891655)
    ·
      refine ⟨3216261766540083487337483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2144174511026722324891655 3216261766540083487337483)
      ·
        refine ⟨4824392649810125231006225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3216261766540083487337483 4824392649810125231006225)
        ·
          refine ⟨3618294487357593923254669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4824392649810125231006225 3618294487357593923254669)
          ·
            refine ⟨1356860432759097721220501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3618294487357593923254669 1356860432759097721220501)
            ·
              refine ⟨63602832785582705682211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1356860432759097721220501 63602832785582705682211)
              ·
                refine ⟨95404249178374058523317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63602832785582705682211 95404249178374058523317)
                ·
                  refine ⟨8944148360472567986561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 95404249178374058523317 8944148360472567986561)
                  ·
                    rfl

theorem cell22_78384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 6, 1, 5].length) (baseStart_78384 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_78384 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_78384 prefixEnd_78384 := by exact prefixLift 78384
  have htrace : WordTrace (prefixWord ++ tailWord_78384) baseStart_78384 baseEnd_78384 := by
    simpa [prefixWord, tailWord_78384, baseEnd_78384] using wordTrace_append hprefix tailTrace_78384
  have hstable : (prefixWord ++ tailWord_78384).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_78384).length < 2 ^ (prefixWord ++ tailWord_78384).sum := by decide
  have hdescent : baseEnd_78384 < baseStart_78384 := by decide
  rcases family_descends (prefixWord ++ tailWord_78384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_78414 : List Nat := [4, 1, 1, 1, 1, 2, 2, 5, 1, 4]
def baseStart_78414 : Nat := 118140960795 + 78414 * 2 ^ 59
def prefixEnd_78414 : Nat := 4983230072969 + 3 ^ 40 * 78414 * 2
def baseEnd_78414 : Nat := 26842714694507625709591

theorem tailTrace_78414 : CollatzResearch.WordTrace tailWord_78414 prefixEnd_78414 26842714694507625709591 := by
  unfold tailWord_78414
  simp only [CollatzResearch.WordTrace]
  refine ⟨357499192240868111264287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1906662358617963260076197 357499192240868111264287)
  ·
    refine ⟨536248788361302166896431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 357499192240868111264287 536248788361302166896431)
    ·
      refine ⟨804373182541953250344647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 536248788361302166896431 804373182541953250344647)
      ·
        refine ⟨1206559773812929875516971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 804373182541953250344647 1206559773812929875516971)
        ·
          refine ⟨1809839660719394813275457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1206559773812929875516971 1809839660719394813275457)
          ·
            refine ⟨1357379745539546109956593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1809839660719394813275457 1357379745539546109956593)
            ·
              refine ⟨1018034809154659582467445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1357379745539546109956593 1018034809154659582467445)
              ·
                refine ⟨95440763358249335856323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1018034809154659582467445 95440763358249335856323)
                ·
                  refine ⟨143161145037374003784485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 95440763358249335856323 143161145037374003784485)
                  ·
                    refine ⟨26842714694507625709591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 143161145037374003784485 26842714694507625709591)
                    ·
                      rfl

theorem cell22_78414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 5, 1, 4].length) (baseStart_78414 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_78414 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_78414 prefixEnd_78414 := by exact prefixLift 78414
  have htrace : WordTrace (prefixWord ++ tailWord_78414) baseStart_78414 baseEnd_78414 := by
    simpa [prefixWord, tailWord_78414, baseEnd_78414] using wordTrace_append hprefix tailTrace_78414
  have hstable : (prefixWord ++ tailWord_78414).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_78414).length < 2 ^ (prefixWord ++ tailWord_78414).sum := by decide
  have hdescent : baseEnd_78414 < baseStart_78414 := by decide
  rcases family_descends (prefixWord ++ tailWord_78414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_78474 : List Nat := [3, 1, 2, 3, 3, 1, 9]
def baseStart_78474 : Nat := 118140960795 + 78474 * 2 ^ 59
def prefixEnd_78474 : Nat := 4983230072969 + 3 ^ 40 * 78474 * 2
def baseEnd_78474 : Nat := 994935330395832192941

theorem tailTrace_78474 : CollatzResearch.WordTrace tailWord_78474 prefixEnd_78474 994935330395832192941 := by
  unfold tailWord_78474
  simp only [CollatzResearch.WordTrace]
  refine ⟨715545479427393784324619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1908121278473050091532317 715545479427393784324619)
  ·
    refine ⟨1073318219141090676486929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 715545479427393784324619 1073318219141090676486929)
    ·
      refine ⟨804988664355818007365197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1073318219141090676486929 804988664355818007365197)
      ·
        refine ⟨301870749133431752761949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 804988664355818007365197 301870749133431752761949)
        ·
          refine ⟨113201530925036907285731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 301870749133431752761949 113201530925036907285731)
          ·
            refine ⟨169802296387555360928597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113201530925036907285731 169802296387555360928597)
            ·
              refine ⟨994935330395832192941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 169802296387555360928597 994935330395832192941)
              ·
                rfl

theorem cell22_78474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 9].length) (baseStart_78474 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_78474 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_78474 prefixEnd_78474 := by exact prefixLift 78474
  have htrace : WordTrace (prefixWord ++ tailWord_78474) baseStart_78474 baseEnd_78474 := by
    simpa [prefixWord, tailWord_78474, baseEnd_78474] using wordTrace_append hprefix tailTrace_78474
  have hstable : (prefixWord ++ tailWord_78474).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_78474).length < 2 ^ (prefixWord ++ tailWord_78474).sum := by decide
  have hdescent : baseEnd_78474 < baseStart_78474 := by decide
  rcases family_descends (prefixWord ++ tailWord_78474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_78609 : List Nat := [1, 2, 2, 1, 1, 3, 5, 7]
def baseStart_78609 : Nat := 118140960795 + 78609 * 2 ^ 59
def prefixEnd_78609 : Nat := 4983230072969 + 3 ^ 40 * 78609 * 2
def baseEnd_78609 : Nat := 2989940797732457453777

theorem tailTrace_78609 : CollatzResearch.WordTrace tailWord_78609 prefixEnd_78609 2989940797732457453777 := by
  unfold tailWord_78609
  simp only [CollatzResearch.WordTrace]
  refine ⟨2867105772220493193462881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1911403848146995462308587 2867105772220493193462881)
  ·
    refine ⟨2150329329165369895097161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2867105772220493193462881 2150329329165369895097161)
    ·
      refine ⟨1612746996874027421322871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2150329329165369895097161 1612746996874027421322871)
      ·
        refine ⟨2419120495311041131984307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1612746996874027421322871 2419120495311041131984307)
        ·
          refine ⟨3628680742966561697976461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2419120495311041131984307 3628680742966561697976461)
          ·
            refine ⟨1360755278612460636741173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3628680742966561697976461 1360755278612460636741173)
            ·
              refine ⟨127570807369918184694485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1360755278612460636741173 127570807369918184694485)
              ·
                refine ⟨2989940797732457453777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 127570807369918184694485 2989940797732457453777)
                ·
                  rfl

theorem cell22_78609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 5, 7].length) (baseStart_78609 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_78609 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_78609 prefixEnd_78609 := by exact prefixLift 78609
  have htrace : WordTrace (prefixWord ++ tailWord_78609) baseStart_78609 baseEnd_78609 := by
    simpa [prefixWord, tailWord_78609, baseEnd_78609] using wordTrace_append hprefix tailTrace_78609
  have hstable : (prefixWord ++ tailWord_78609).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_78609).length < 2 ^ (prefixWord ++ tailWord_78609).sum := by decide
  have hdescent : baseEnd_78609 < baseStart_78609 := by decide
  rcases family_descends (prefixWord ++ tailWord_78609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_78634 : List Nat := [3, 1, 4, 3, 2, 1, 2, 1, 1, 4]
def baseStart_78634 : Nat := 118140960795 + 78634 * 2 ^ 59
def prefixEnd_78634 : Nat := 4983230072969 + 3 ^ 40 * 78634 * 2
def baseEnd_78634 : Nat := 26918025190500385208917

theorem tailTrace_78634 : CollatzResearch.WordTrace tailWord_78634 prefixEnd_78634 26918025190500385208917 := by
  unfold tailWord_78634
  simp only [CollatzResearch.WordTrace]
  refine ⟨717004399282480615780739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1912011731419948308748637 717004399282480615780739)
  ·
    refine ⟨1075506598923720923671109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 717004399282480615780739 1075506598923720923671109)
    ·
      refine ⟨201657487298197673188333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1075506598923720923671109 201657487298197673188333)
      ·
        refine ⟨75621557736824127445625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 201657487298197673188333 75621557736824127445625)
        ·
          refine ⟨56716168302618095584219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75621557736824127445625 56716168302618095584219)
          ·
            refine ⟨85074252453927143376329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56716168302618095584219 85074252453927143376329)
            ·
              refine ⟨63805689340445357532247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 85074252453927143376329 63805689340445357532247)
              ·
                refine ⟨95708534010668036298371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63805689340445357532247 95708534010668036298371)
                ·
                  refine ⟨143562801016002054447557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 95708534010668036298371 143562801016002054447557)
                  ·
                    refine ⟨26918025190500385208917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 143562801016002054447557 26918025190500385208917)
                    ·
                      rfl

theorem cell22_78634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 1, 2, 1, 1, 4].length) (baseStart_78634 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_78634 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_78634 prefixEnd_78634 := by exact prefixLift 78634
  have htrace : WordTrace (prefixWord ++ tailWord_78634) baseStart_78634 baseEnd_78634 := by
    simpa [prefixWord, tailWord_78634, baseEnd_78634] using wordTrace_append hprefix tailTrace_78634
  have hstable : (prefixWord ++ tailWord_78634).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_78634).length < 2 ^ (prefixWord ++ tailWord_78634).sum := by decide
  have hdescent : baseEnd_78634 < baseStart_78634 := by decide
  rcases family_descends (prefixWord ++ tailWord_78634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_78641 : List Nat := [1, 2, 2, 3, 2, 1, 1, 2, 5, 3]
def baseStart_78641 : Nat := 118140960795 + 78641 * 2 ^ 59
def prefixEnd_78641 : Nat := 4983230072969 + 3 ^ 40 * 78641 * 2
def baseEnd_78641 : Nat := 26920421433554700283895

theorem tailTrace_78641 : CollatzResearch.WordTrace tailWord_78641 prefixEnd_78641 26920421433554700283895 := by
  unfold tailWord_78641
  simp only [CollatzResearch.WordTrace]
  refine ⟨2868272908104562658627777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1912181938736375105751851 2868272908104562658627777)
  ·
    refine ⟨2151204681078421993970833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2868272908104562658627777 2151204681078421993970833)
    ·
      refine ⟨1613403510808816495478125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2151204681078421993970833 1613403510808816495478125)
      ·
        refine ⟨605026316553306185804297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1613403510808816495478125 605026316553306185804297)
        ·
          refine ⟨453769737414979639353223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 605026316553306185804297 453769737414979639353223)
          ·
            refine ⟨680654606122469459029835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 453769737414979639353223 680654606122469459029835)
            ·
              refine ⟨1020981909183704188544753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 680654606122469459029835 1020981909183704188544753)
              ·
                refine ⟨765736431887778141408565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1020981909183704188544753 765736431887778141408565)
                ·
                  refine ⟨71787790489479200757053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 765736431887778141408565 71787790489479200757053)
                  ·
                    refine ⟨26920421433554700283895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 71787790489479200757053 26920421433554700283895)
                    ·
                      rfl

theorem cell22_78641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 2, 5, 3].length) (baseStart_78641 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_78641 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_78641 prefixEnd_78641 := by exact prefixLift 78641
  have htrace : WordTrace (prefixWord ++ tailWord_78641) baseStart_78641 baseEnd_78641 := by
    simpa [prefixWord, tailWord_78641, baseEnd_78641] using wordTrace_append hprefix tailTrace_78641
  have hstable : (prefixWord ++ tailWord_78641).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_78641).length < 2 ^ (prefixWord ++ tailWord_78641).sum := by decide
  have hdescent : baseEnd_78641 < baseStart_78641 := by decide
  rcases family_descends (prefixWord ++ tailWord_78641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_78692 : List Nat := [2, 3, 1, 1, 4, 3, 1, 3, 1, 3]
def baseStart_78692 : Nat := 118140960795 + 78692 * 2 ^ 59
def prefixEnd_78692 : Nat := 4983230072969 + 3 ^ 40 * 78692 * 2
def baseEnd_78692 : Nat := 26937879775807567258739

theorem tailTrace_78692 : CollatzResearch.WordTrace tailWord_78692 prefixEnd_78692 26937879775807567258739 := by
  unfold tailWord_78692
  simp only [CollatzResearch.WordTrace]
  refine ⟨1435066515459899184367165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1913422020613198912489553 1435066515459899184367165)
  ·
    refine ⟨538149943297462194137687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1435066515459899184367165 538149943297462194137687)
    ·
      refine ⟨807224914946193291206531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 538149943297462194137687 807224914946193291206531)
      ·
        refine ⟨1210837372419289936809797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 807224914946193291206531 1210837372419289936809797)
        ·
          refine ⟨227032007328616863151837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1210837372419289936809797 227032007328616863151837)
          ·
            refine ⟨85137002748231323681939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 227032007328616863151837 85137002748231323681939)
            ·
              refine ⟨127705504122346985522909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85137002748231323681939 127705504122346985522909)
              ·
                refine ⟨47889564045880119571091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 127705504122346985522909 47889564045880119571091)
                ·
                  refine ⟨71834346068820179356637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47889564045880119571091 71834346068820179356637)
                  ·
                    refine ⟨26937879775807567258739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 71834346068820179356637 26937879775807567258739)
                    ·
                      rfl

theorem cell22_78692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 3, 1, 3, 1, 3].length) (baseStart_78692 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_78692 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_78692 prefixEnd_78692 := by exact prefixLift 78692
  have htrace : WordTrace (prefixWord ++ tailWord_78692) baseStart_78692 baseEnd_78692 := by
    simpa [prefixWord, tailWord_78692, baseEnd_78692] using wordTrace_append hprefix tailTrace_78692
  have hstable : (prefixWord ++ tailWord_78692).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_78692).length < 2 ^ (prefixWord ++ tailWord_78692).sum := by decide
  have hdescent : baseEnd_78692 < baseStart_78692 := by decide
  rcases family_descends (prefixWord ++ tailWord_78692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_78699 : List Nat := [1, 1, 1, 1, 2, 2, 4, 2, 8]
def baseStart_78699 : Nat := 118140960795 + 78699 * 2 ^ 59
def prefixEnd_78699 : Nat := 4983230072969 + 3 ^ 40 * 78699 * 2
def baseEnd_78699 : Nat := 8980092006287294111239

theorem tailTrace_78699 : CollatzResearch.WordTrace tailWord_78699 prefixEnd_78699 8980092006287294111239 := by
  unfold tailWord_78699
  simp only [CollatzResearch.WordTrace]
  refine ⟨2870388341894438564239151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1913592227929625709492767 2870388341894438564239151)
  ·
    refine ⟨4305582512841657846358727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2870388341894438564239151 4305582512841657846358727)
    ·
      refine ⟨6458373769262486769538091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4305582512841657846358727 6458373769262486769538091)
      ·
        refine ⟨9687560653893730154307137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6458373769262486769538091 9687560653893730154307137)
        ·
          refine ⟨7265670490420297615730353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9687560653893730154307137 7265670490420297615730353)
          ·
            refine ⟨5449252867815223211797765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7265670490420297615730353 5449252867815223211797765)
            ·
              refine ⟨1021734912715354352212081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5449252867815223211797765 1021734912715354352212081)
              ·
                refine ⟨766301184536515764159061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1021734912715354352212081 766301184536515764159061)
                ·
                  refine ⟨8980092006287294111239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 766301184536515764159061 8980092006287294111239)
                  ·
                    rfl

theorem cell22_78699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 2, 8].length) (baseStart_78699 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_78699 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_78699 prefixEnd_78699 := by exact prefixLift 78699
  have htrace : WordTrace (prefixWord ++ tailWord_78699) baseStart_78699 baseEnd_78699 := by
    simpa [prefixWord, tailWord_78699, baseEnd_78699] using wordTrace_append hprefix tailTrace_78699
  have hstable : (prefixWord ++ tailWord_78699).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_78699).length < 2 ^ (prefixWord ++ tailWord_78699).sum := by decide
  have hdescent : baseEnd_78699 < baseStart_78699 := by decide
  rcases family_descends (prefixWord ++ tailWord_78699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_78701 : List Nat := [1, 5, 1, 1, 1, 1, 1, 2, 5, 4]
def baseStart_78701 : Nat := 118140960795 + 78701 * 2 ^ 59
def prefixEnd_78701 : Nat := 4983230072969 + 3 ^ 40 * 78701 * 2
def baseEnd_78701 : Nat := 26940960659734543783711

theorem tailTrace_78701 : CollatzResearch.WordTrace tailWord_78701 prefixEnd_78701 26940960659734543783711 := by
  unfold tailWord_78701
  simp only [CollatzResearch.WordTrace]
  refine ⟨2870461287887192905811957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1913640858591461937207971 2870461287887192905811957)
  ·
    refine ⟨269105745739424334919871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2870461287887192905811957 269105745739424334919871)
    ·
      refine ⟨403658618609136502379807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 269105745739424334919871 403658618609136502379807)
      ·
        refine ⟨605487927913704753569711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 403658618609136502379807 605487927913704753569711)
        ·
          refine ⟨908231891870557130354567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 605487927913704753569711 908231891870557130354567)
          ·
            refine ⟨1362347837805835695531851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 908231891870557130354567 1362347837805835695531851)
            ·
              refine ⟨2043521756708753543297777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1362347837805835695531851 2043521756708753543297777)
              ·
                refine ⟨1532641317531565157473333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2043521756708753543297777 1532641317531565157473333)
                ·
                  refine ⟨143685123518584233513125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1532641317531565157473333 143685123518584233513125)
                  ·
                    refine ⟨26940960659734543783711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 143685123518584233513125 26940960659734543783711)
                    ·
                      rfl

theorem cell22_78701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 2, 5, 4].length) (baseStart_78701 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_78701 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_78701 prefixEnd_78701 := by exact prefixLift 78701
  have htrace : WordTrace (prefixWord ++ tailWord_78701) baseStart_78701 baseEnd_78701 := by
    simpa [prefixWord, tailWord_78701, baseEnd_78701] using wordTrace_append hprefix tailTrace_78701
  have hstable : (prefixWord ++ tailWord_78701).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_78701).length < 2 ^ (prefixWord ++ tailWord_78701).sum := by decide
  have hdescent : baseEnd_78701 < baseStart_78701 := by decide
  rcases family_descends (prefixWord ++ tailWord_78701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_78722 : List Nat := [3, 4, 2, 2, 1, 1, 1, 3, 5]
def baseStart_78722 : Nat := 118140960795 + 78722 * 2 ^ 59
def prefixEnd_78722 : Nat := 4983230072969 + 3 ^ 40 * 78722 * 2
def baseEnd_78722 : Nat := 8982716462965829669549

theorem tailTrace_78722 : CollatzResearch.WordTrace tailWord_78722 prefixEnd_78722 8982716462965829669549 := by
  unfold tailWord_78722
  simp only [CollatzResearch.WordTrace]
  refine ⟨717806805202778373081605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1914151480540742328217613 717806805202778373081605)
  ·
    refine ⟨134588775975520944952801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 717806805202778373081605 134588775975520944952801)
    ·
      refine ⟨100941581981640708714601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134588775975520944952801 100941581981640708714601)
      ·
        refine ⟨75706186486230531535951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100941581981640708714601 75706186486230531535951)
        ·
          refine ⟨113559279729345797303927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75706186486230531535951 113559279729345797303927)
          ·
            refine ⟨170338919594018695955891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113559279729345797303927 170338919594018695955891)
            ·
              refine ⟨255508379391028043933837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 170338919594018695955891 255508379391028043933837)
              ·
                refine ⟨95815642271635516475189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 255508379391028043933837 95815642271635516475189)
                ·
                  refine ⟨8982716462965829669549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 95815642271635516475189 8982716462965829669549)
                  ·
                    rfl

theorem cell22_78722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 1, 3, 5].length) (baseStart_78722 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_78722 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_78722 prefixEnd_78722 := by exact prefixLift 78722
  have htrace : WordTrace (prefixWord ++ tailWord_78722) baseStart_78722 baseEnd_78722 := by
    simpa [prefixWord, tailWord_78722, baseEnd_78722] using wordTrace_append hprefix tailTrace_78722
  have hstable : (prefixWord ++ tailWord_78722).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_78722).length < 2 ^ (prefixWord ++ tailWord_78722).sum := by decide
  have hdescent : baseEnd_78722 < baseStart_78722 := by decide
  rcases family_descends (prefixWord ++ tailWord_78722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_78823 : List Nat := [1, 1, 5, 2, 2, 2, 1, 1, 7]
def baseStart_78823 : Nat := 118140960795 + 78823 * 2 ^ 59
def prefixEnd_78823 : Nat := 4983230072969 + 3 ^ 40 * 78823 * 2
def baseEnd_78823 : Nat := 8994241250988964077779

theorem tailTrace_78823 : CollatzResearch.WordTrace tailWord_78823 prefixEnd_78823 8994241250988964077779 := by
  unfold tailWord_78823
  simp only [CollatzResearch.WordTrace]
  refine ⟨2874910993445207741753123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1916607328963471827835415 2874910993445207741753123)
  ·
    refine ⟨4312366490167811612629685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2874910993445207741753123 4312366490167811612629685)
    ·
      refine ⟨404284358453232338684033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4312366490167811612629685 404284358453232338684033)
      ·
        refine ⟨303213268839924254013025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 404284358453232338684033 303213268839924254013025)
        ·
          refine ⟨227409951629943190509769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 303213268839924254013025 227409951629943190509769)
          ·
            refine ⟨170557463722457392882327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 227409951629943190509769 170557463722457392882327)
            ·
              refine ⟨255836195583686089323491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 170557463722457392882327 255836195583686089323491)
              ·
                refine ⟨383754293375529133985237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 255836195583686089323491 383754293375529133985237)
                ·
                  refine ⟨8994241250988964077779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 383754293375529133985237 8994241250988964077779)
                  ·
                    rfl

theorem cell22_78823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 1, 1, 7].length) (baseStart_78823 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_78823 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_78823 prefixEnd_78823 := by exact prefixLift 78823
  have htrace : WordTrace (prefixWord ++ tailWord_78823) baseStart_78823 baseEnd_78823 := by
    simpa [prefixWord, tailWord_78823, baseEnd_78823] using wordTrace_append hprefix tailTrace_78823
  have hstable : (prefixWord ++ tailWord_78823).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_78823).length < 2 ^ (prefixWord ++ tailWord_78823).sum := by decide
  have hdescent : baseEnd_78823 < baseStart_78823 := by decide
  rcases family_descends (prefixWord ++ tailWord_78823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_78898 : List Nat := [3, 2, 1, 1, 2, 2, 1, 2, 4, 4]
def baseStart_78898 : Nat := 118140960795 + 78898 * 2 ^ 59
def prefixEnd_78898 : Nat := 4983230072969 + 3 ^ 40 * 78898 * 2
def baseEnd_78898 : Nat := 27008397785691696608107

theorem tailTrace_78898 : CollatzResearch.WordTrace tailWord_78898 prefixEnd_78898 27008397785691696608107 := by
  unfold tailWord_78898
  simp only [CollatzResearch.WordTrace]
  refine ⟨719411617043373887683337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1918430978782330367155565 719411617043373887683337)
  ·
    refine ⟨539558712782530415762503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 719411617043373887683337 539558712782530415762503)
    ·
      refine ⟨809338069173795623643755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 539558712782530415762503 809338069173795623643755)
      ·
        refine ⟨1214007103760693435465633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 809338069173795623643755 1214007103760693435465633)
        ·
          refine ⟨910505327820520076599225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1214007103760693435465633 910505327820520076599225)
          ·
            refine ⟨682878995865390057449419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 910505327820520076599225 682878995865390057449419)
            ·
              refine ⟨1024318493798085086174129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 682878995865390057449419 1024318493798085086174129)
              ·
                refine ⟨768238870348563814630597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1024318493798085086174129 768238870348563814630597)
                ·
                  refine ⟨144044788190355715243237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 768238870348563814630597 144044788190355715243237)
                  ·
                    refine ⟨27008397785691696608107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 144044788190355715243237 27008397785691696608107)
                    ·
                      rfl

theorem cell22_78898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 2, 4, 4].length) (baseStart_78898 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_78898 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_78898 prefixEnd_78898 := by exact prefixLift 78898
  have htrace : WordTrace (prefixWord ++ tailWord_78898) baseStart_78898 baseEnd_78898 := by
    simpa [prefixWord, tailWord_78898, baseEnd_78898] using wordTrace_append hprefix tailTrace_78898
  have hstable : (prefixWord ++ tailWord_78898).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_78898).length < 2 ^ (prefixWord ++ tailWord_78898).sum := by decide
  have hdescent : baseEnd_78898 < baseStart_78898 := by decide
  rcases family_descends (prefixWord ++ tailWord_78898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_78973 : List Nat := [1, 4, 1, 1, 3, 1, 1, 2, 1, 7]
def baseStart_78973 : Nat := 118140960795 + 78973 * 2 ^ 59
def prefixEnd_78973 : Nat := 4983230072969 + 3 ^ 40 * 78973 * 2
def baseEnd_78973 : Nat := 27034071818416500982877

theorem tailTrace_78973 : CollatzResearch.WordTrace tailWord_78973 prefixEnd_78973 27034071818416500982877 := by
  unfold tailWord_78973
  simp only [CollatzResearch.WordTrace]
  refine ⟨2880381942901783359713573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1920254628601188906475715 2880381942901783359713573)
  ·
    refine ⟨540071614294084379946295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2880381942901783359713573 540071614294084379946295)
    ·
      refine ⟨810107421441126569919443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 540071614294084379946295 810107421441126569919443)
      ·
        refine ⟨1215161132161689854879165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 810107421441126569919443 1215161132161689854879165)
        ·
          refine ⟨455685424560633695579687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1215161132161689854879165 455685424560633695579687)
          ·
            refine ⟨683528136840950543369531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 455685424560633695579687 683528136840950543369531)
            ·
              refine ⟨1025292205261425815054297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 683528136840950543369531 1025292205261425815054297)
              ·
                refine ⟨768969153946069361290723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1025292205261425815054297 768969153946069361290723)
                ·
                  refine ⟨1153453730919104041936085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 768969153946069361290723 1153453730919104041936085)
                  ·
                    refine ⟨27034071818416500982877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1153453730919104041936085 27034071818416500982877)
                    ·
                      rfl

theorem cell22_78973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 2, 1, 7].length) (baseStart_78973 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_78973 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_78973 prefixEnd_78973 := by exact prefixLift 78973
  have htrace : WordTrace (prefixWord ++ tailWord_78973) baseStart_78973 baseEnd_78973 := by
    simpa [prefixWord, tailWord_78973, baseEnd_78973] using wordTrace_append hprefix tailTrace_78973
  have hstable : (prefixWord ++ tailWord_78973).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_78973).length < 2 ^ (prefixWord ++ tailWord_78973).sum := by decide
  have hdescent : baseEnd_78973 < baseStart_78973 := by decide
  rcases family_descends (prefixWord ++ tailWord_78973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_78990 : List Nat := [4, 1, 1, 3, 2, 1, 1, 2, 2, 5]
def baseStart_78990 : Nat := 118140960795 + 78990 * 2 ^ 59
def prefixEnd_78990 : Nat := 4983230072969 + 3 ^ 40 * 78990 * 2
def baseEnd_78990 : Nat := 27039891265834123307825

theorem tailTrace_78990 : CollatzResearch.WordTrace tailWord_78990 prefixEnd_78990 27039891265834123307825 := by
  unfold tailWord_78990
  simp only [CollatzResearch.WordTrace]
  refine ⟨360125247980024407885303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1920667989226796842054949 360125247980024407885303)
  ·
    refine ⟨540187871970036611827955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 360125247980024407885303 540187871970036611827955)
    ·
      refine ⟨810281807955054917741933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 540187871970036611827955 810281807955054917741933)
      ·
        refine ⟨303855677983145594153225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 810281807955054917741933 303855677983145594153225)
        ·
          refine ⟨227891758487359195614919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 303855677983145594153225 227891758487359195614919)
          ·
            refine ⟨341837637731038793422379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 227891758487359195614919 341837637731038793422379)
            ·
              refine ⟨512756456596558190133569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 341837637731038793422379 512756456596558190133569)
              ·
                refine ⟨384567342447418642600177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 512756456596558190133569 384567342447418642600177)
                ·
                  refine ⟨288425506835563981950133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 384567342447418642600177 288425506835563981950133)
                  ·
                    refine ⟨27039891265834123307825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 288425506835563981950133 27039891265834123307825)
                    ·
                      rfl

theorem cell22_78990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 2, 2, 5].length) (baseStart_78990 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_78990 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_78990 prefixEnd_78990 := by exact prefixLift 78990
  have htrace : WordTrace (prefixWord ++ tailWord_78990) baseStart_78990 baseEnd_78990 := by
    simpa [prefixWord, tailWord_78990, baseEnd_78990] using wordTrace_append hprefix tailTrace_78990
  have hstable : (prefixWord ++ tailWord_78990).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_78990).length < 2 ^ (prefixWord ++ tailWord_78990).sum := by decide
  have hdescent : baseEnd_78990 < baseStart_78990 := by decide
  rcases family_descends (prefixWord ++ tailWord_78990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_79030 : List Nat := [5, 1, 3, 2, 1, 2, 1, 3, 1, 3]
def baseStart_79030 : Nat := 118140960795 + 79030 * 2 ^ 59
def prefixEnd_79030 : Nat := 4983230072969 + 3 ^ 40 * 79030 * 2
def baseEnd_79030 : Nat := 27053584083287352307703

theorem tailTrace_79030 : CollatzResearch.WordTrace tailWord_79030 prefixEnd_79030 27053584083287352307703 := by
  unfold tailWord_79030
  simp only [CollatzResearch.WordTrace]
  refine ⟨180153806480955130908659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1921640602463521396359029 180153806480955130908659)
  ·
    refine ⟨270230709721432696362989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180153806480955130908659 270230709721432696362989)
    ·
      refine ⟨101336516145537261136121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 270230709721432696362989 101336516145537261136121)
      ·
        refine ⟨76002387109152945852091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101336516145537261136121 76002387109152945852091)
        ·
          refine ⟨114003580663729418778137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76002387109152945852091 114003580663729418778137)
          ·
            refine ⟨85502685497797064083603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 114003580663729418778137 85502685497797064083603)
            ·
              refine ⟨128254028246695596125405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85502685497797064083603 128254028246695596125405)
              ·
                refine ⟨48095260592510848547027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 128254028246695596125405 48095260592510848547027)
                ·
                  refine ⟨72142890888766272820541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48095260592510848547027 72142890888766272820541)
                  ·
                    refine ⟨27053584083287352307703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 72142890888766272820541 27053584083287352307703)
                    ·
                      rfl

theorem cell22_79030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 2, 1, 3, 1, 3].length) (baseStart_79030 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_79030 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_79030 prefixEnd_79030 := by exact prefixLift 79030
  have htrace : WordTrace (prefixWord ++ tailWord_79030) baseStart_79030 baseEnd_79030 := by
    simpa [prefixWord, tailWord_79030, baseEnd_79030] using wordTrace_append hprefix tailTrace_79030
  have hstable : (prefixWord ++ tailWord_79030).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_79030).length < 2 ^ (prefixWord ++ tailWord_79030).sum := by decide
  have hdescent : baseEnd_79030 < baseStart_79030 := by decide
  rcases family_descends (prefixWord ++ tailWord_79030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_79037 : List Nat := [1, 4, 1, 2, 1, 1, 5, 3, 4]
def baseStart_79037 : Nat := 118140960795 + 79037 * 2 ^ 59
def prefixEnd_79037 : Nat := 4983230072969 + 3 ^ 40 * 79037 * 2
def baseEnd_79037 : Nat := 9018660108780555794227

theorem tailTrace_79037 : CollatzResearch.WordTrace tailWord_79037 prefixEnd_79037 9018660108780555794227 := by
  unfold tailWord_79037
  simp only [CollatzResearch.WordTrace]
  refine ⟨2882716214669922290043365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1921810809779948193362243 2882716214669922290043365)
  ·
    refine ⟨540509290250610429383131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2882716214669922290043365 540509290250610429383131)
    ·
      refine ⟨810763935375915644074697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 540509290250610429383131 810763935375915644074697)
      ·
        refine ⟨608072951531936733056023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 810763935375915644074697 608072951531936733056023)
        ·
          refine ⟨912109427297905099584035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 608072951531936733056023 912109427297905099584035)
          ·
            refine ⟨1368164140946857649376053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 912109427297905099584035 1368164140946857649376053)
            ·
              refine ⟨128265388213767904629005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1368164140946857649376053 128265388213767904629005)
              ·
                refine ⟨48099520580162964235877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 128265388213767904629005 48099520580162964235877)
                ·
                  refine ⟨9018660108780555794227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 48099520580162964235877 9018660108780555794227)
                  ·
                    rfl

theorem cell22_79037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 5, 3, 4].length) (baseStart_79037 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_79037 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_79037 prefixEnd_79037 := by exact prefixLift 79037
  have htrace : WordTrace (prefixWord ++ tailWord_79037) baseStart_79037 baseEnd_79037 := by
    simpa [prefixWord, tailWord_79037, baseEnd_79037] using wordTrace_append hprefix tailTrace_79037
  have hstable : (prefixWord ++ tailWord_79037).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_79037).length < 2 ^ (prefixWord ++ tailWord_79037).sum := by decide
  have hdescent : baseEnd_79037 < baseStart_79037 := by decide
  rcases family_descends (prefixWord ++ tailWord_79037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_79048 : List Nat := [2, 1, 3, 1, 2, 1, 12]
def baseStart_79048 : Nat := 118140960795 + 79048 * 2 ^ 59
def prefixEnd_79048 : Nat := 4983230072969 + 3 ^ 40 * 79048 * 2
def baseEnd_79048 : Nat := 1002212809301529828061

theorem tailTrace_79048 : CollatzResearch.WordTrace tailWord_79048 prefixEnd_79048 1002212809301529828061 := by
  unfold tailWord_79048
  simp only [CollatzResearch.WordTrace]
  refine ⟨1441558708815035584346899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1922078278420047445795865 1441558708815035584346899)
  ·
    refine ⟨2162338063222553376520349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1441558708815035584346899 2162338063222553376520349)
    ·
      refine ⟨810876773708457516195131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2162338063222553376520349 810876773708457516195131)
      ·
        refine ⟨1216315160562686274292697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 810876773708457516195131 1216315160562686274292697)
        ·
          refine ⟨912236370422014705719523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1216315160562686274292697 912236370422014705719523)
          ·
            refine ⟨1368354555633022058579285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 912236370422014705719523 1368354555633022058579285)
            ·
              refine ⟨1002212809301529828061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 1368354555633022058579285 1002212809301529828061)
              ·
                rfl

theorem cell22_79048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 12].length) (baseStart_79048 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_79048 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_79048 prefixEnd_79048 := by exact prefixLift 79048
  have htrace : WordTrace (prefixWord ++ tailWord_79048) baseStart_79048 baseEnd_79048 := by
    simpa [prefixWord, tailWord_79048, baseEnd_79048] using wordTrace_append hprefix tailTrace_79048
  have hstable : (prefixWord ++ tailWord_79048).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_79048).length < 2 ^ (prefixWord ++ tailWord_79048).sum := by decide
  have hdescent : baseEnd_79048 < baseStart_79048 := by decide
  rcases family_descends (prefixWord ++ tailWord_79048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_79050 : List Nat := [3, 1, 2, 1, 3, 2, 1, 1, 4, 4]
def baseStart_79050 : Nat := 118140960795 + 79050 * 2 ^ 59
def prefixEnd_79050 : Nat := 4983230072969 + 3 ^ 40 * 79050 * 2
def baseEnd_79050 : Nat := 27060430492013966807641

theorem tailTrace_79050 : CollatzResearch.WordTrace tailWord_79050 prefixEnd_79050 27060430492013966807641 := by
  unfold tailWord_79050
  simp only [CollatzResearch.WordTrace]
  refine ⟨720797590905706377566651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1922126909081883673511069 720797590905706377566651)
  ·
    refine ⟨1081196386358559566349977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 720797590905706377566651 1081196386358559566349977)
    ·
      refine ⟨810897289768919674762483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1081196386358559566349977 810897289768919674762483)
      ·
        refine ⟨1216345934653379512143725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 810897289768919674762483 1216345934653379512143725)
        ·
          refine ⟨456129725495017317053897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1216345934653379512143725 456129725495017317053897)
          ·
            refine ⟨342097294121262987790423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 456129725495017317053897 342097294121262987790423)
            ·
              refine ⟨513145941181894481685635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 342097294121262987790423 513145941181894481685635)
              ·
                refine ⟨769718911772841722528453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 513145941181894481685635 769718911772841722528453)
                ·
                  refine ⟨144322295957407822974085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 769718911772841722528453 144322295957407822974085)
                  ·
                    refine ⟨27060430492013966807641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 144322295957407822974085 27060430492013966807641)
                    ·
                      rfl

theorem cell22_79050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 1, 4, 4].length) (baseStart_79050 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_79050 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_79050 prefixEnd_79050 := by exact prefixLift 79050
  have htrace : WordTrace (prefixWord ++ tailWord_79050) baseStart_79050 baseEnd_79050 := by
    simpa [prefixWord, tailWord_79050, baseEnd_79050] using wordTrace_append hprefix tailTrace_79050
  have hstable : (prefixWord ++ tailWord_79050).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_79050).length < 2 ^ (prefixWord ++ tailWord_79050).sum := by decide
  have hdescent : baseEnd_79050 < baseStart_79050 := by decide
  rcases family_descends (prefixWord ++ tailWord_79050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_79054 : List Nat := [4, 1, 1, 1, 6, 1, 1, 1, 6]
def baseStart_79054 : Nat := 118140960795 + 79054 * 2 ^ 59
def prefixEnd_79054 : Nat := 4983230072969 + 3 ^ 40 * 79054 * 2
def baseEnd_79054 : Nat := 9020599924586429902543

theorem tailTrace_79054 : CollatzResearch.WordTrace tailWord_79054 prefixEnd_79054 9020599924586429902543 := by
  unfold tailWord_79054
  simp only [CollatzResearch.WordTrace]
  refine ⟨360417031951041774176527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1922224170405556128941477 360417031951041774176527)
  ·
    refine ⟨540625547926562661264791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 360417031951041774176527 540625547926562661264791)
    ·
      refine ⟨810938321889843991897187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 540625547926562661264791 810938321889843991897187)
      ·
        refine ⟨1216407482834765987845781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 810938321889843991897187 1216407482834765987845781)
        ·
          refine ⟨57019100757879655680271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 1216407482834765987845781 57019100757879655680271)
          ·
            refine ⟨85528651136819483520407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57019100757879655680271 85528651136819483520407)
            ·
              refine ⟨128292976705229225280611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85528651136819483520407 128292976705229225280611)
              ·
                refine ⟨192439465057843837920917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 128292976705229225280611 192439465057843837920917)
                ·
                  refine ⟨9020599924586429902543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 192439465057843837920917 9020599924586429902543)
                  ·
                    rfl

theorem cell22_79054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 1, 1, 1, 6].length) (baseStart_79054 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_79054 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_79054 prefixEnd_79054 := by exact prefixLift 79054
  have htrace : WordTrace (prefixWord ++ tailWord_79054) baseStart_79054 baseEnd_79054 := by
    simpa [prefixWord, tailWord_79054, baseEnd_79054] using wordTrace_append hprefix tailTrace_79054
  have hstable : (prefixWord ++ tailWord_79054).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_79054).length < 2 ^ (prefixWord ++ tailWord_79054).sum := by decide
  have hdescent : baseEnd_79054 < baseStart_79054 := by decide
  rcases family_descends (prefixWord ++ tailWord_79054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_79161 : List Nat := [1, 2, 1, 6, 3, 1, 1, 2, 5]
def baseStart_79161 : Nat := 118140960795 + 79161 * 2 ^ 59
def prefixEnd_79161 : Nat := 4983230072969 + 3 ^ 40 * 79161 * 2
def baseEnd_79161 : Nat := 9032809353482225760767

theorem tailTrace_79161 : CollatzResearch.WordTrace tailWord_79161 prefixEnd_79161 9032809353482225760767 := by
  unfold tailWord_79161
  simp only [CollatzResearch.WordTrace]
  refine ⟨2887238866220691467557337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1924825910813794311704891 2887238866220691467557337)
  ·
    refine ⟨2165429149665518600668003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2887238866220691467557337 2165429149665518600668003)
    ·
      refine ⟨3248143724498277901002005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2165429149665518600668003 3248143724498277901002005)
      ·
        refine ⟨152256737085856776609469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 3248143724498277901002005 152256737085856776609469)
        ·
          refine ⟨57096276407196291228551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 152256737085856776609469 57096276407196291228551)
          ·
            refine ⟨85644414610794436842827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57096276407196291228551 85644414610794436842827)
            ·
              refine ⟨128466621916191655264241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85644414610794436842827 128466621916191655264241)
              ·
                refine ⟨96349966437143741448181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 128466621916191655264241 96349966437143741448181)
                ·
                  refine ⟨9032809353482225760767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 96349966437143741448181 9032809353482225760767)
                  ·
                    rfl

theorem cell22_79161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 1, 1, 2, 5].length) (baseStart_79161 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_79161 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_79161 prefixEnd_79161 := by exact prefixLift 79161
  have htrace : WordTrace (prefixWord ++ tailWord_79161) baseStart_79161 baseEnd_79161 := by
    simpa [prefixWord, tailWord_79161, baseEnd_79161] using wordTrace_append hprefix tailTrace_79161
  have hstable : (prefixWord ++ tailWord_79161).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_79161).length < 2 ^ (prefixWord ++ tailWord_79161).sum := by decide
  have hdescent : baseEnd_79161 < baseStart_79161 := by decide
  rcases family_descends (prefixWord ++ tailWord_79161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_79185 : List Nat := [1, 2, 2, 1, 4, 1, 1, 1, 3, 6]
def baseStart_79185 : Nat := 118140960795 + 79185 * 2 ^ 59
def prefixEnd_79185 : Nat := 4983230072969 + 3 ^ 40 * 79185 * 2
def baseEnd_79185 : Nat := 27106643750918614682227

theorem tailTrace_79185 : CollatzResearch.WordTrace tailWord_79185 prefixEnd_79185 27106643750918614682227 := by
  unfold tailWord_79185
  simp only [CollatzResearch.WordTrace]
  refine ⟨2888114218133743566431009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1925409478755829044287339 2888114218133743566431009)
  ·
    refine ⟨2166085663600307674823257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2888114218133743566431009 2166085663600307674823257)
    ·
      refine ⟨1624564247700230756117443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2166085663600307674823257 1624564247700230756117443)
      ·
        refine ⟨2436846371550346134176165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1624564247700230756117443 2436846371550346134176165)
        ·
          refine ⟨456908694665689900158031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2436846371550346134176165 456908694665689900158031)
          ·
            refine ⟨685363041998534850237047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 456908694665689900158031 685363041998534850237047)
            ·
              refine ⟨1028044562997802275355571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 685363041998534850237047 1028044562997802275355571)
              ·
                refine ⟨1542066844496703413033357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1028044562997802275355571 1542066844496703413033357)
                ·
                  refine ⟨578275066686263779887509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1542066844496703413033357 578275066686263779887509)
                  ·
                    refine ⟨27106643750918614682227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 578275066686263779887509 27106643750918614682227)
                    ·
                      rfl

theorem cell22_79185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 1, 3, 6].length) (baseStart_79185 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_79185 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_79185 prefixEnd_79185 := by exact prefixLift 79185
  have htrace : WordTrace (prefixWord ++ tailWord_79185) baseStart_79185 baseEnd_79185 := by
    simpa [prefixWord, tailWord_79185, baseEnd_79185] using wordTrace_append hprefix tailTrace_79185
  have hstable : (prefixWord ++ tailWord_79185).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_79185).length < 2 ^ (prefixWord ++ tailWord_79185).sum := by decide
  have hdescent : baseEnd_79185 < baseStart_79185 := by decide
  rcases family_descends (prefixWord ++ tailWord_79185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_79202 : List Nat := [3, 3, 2, 1, 1, 1, 1, 3, 1, 6]
def baseStart_79202 : Nat := 118140960795 + 79202 * 2 ^ 59
def prefixEnd_79202 : Nat := 4983230072969 + 3 ^ 40 * 79202 * 2
def baseEnd_79202 : Nat := 27112463198336237007175

theorem tailTrace_79202 : CollatzResearch.WordTrace tailWord_79202 prefixEnd_79202 27112463198336237007175 := by
  unfold tailWord_79202
  simp only [CollatzResearch.WordTrace]
  refine ⟨722183564768038867449965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1925822839381436979866573 722183564768038867449965)
  ·
    refine ⟨270818836788014575293737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 722183564768038867449965 270818836788014575293737)
    ·
      refine ⟨203114127591010931470303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 270818836788014575293737 203114127591010931470303)
      ·
        refine ⟨304671191386516397205455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 203114127591010931470303 304671191386516397205455)
        ·
          refine ⟨457006787079774595808183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 304671191386516397205455 457006787079774595808183)
          ·
            refine ⟨685510180619661893712275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 457006787079774595808183 685510180619661893712275)
            ·
              refine ⟨1028265270929492840568413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 685510180619661893712275 1028265270929492840568413)
              ·
                refine ⟨385599476598559815213155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1028265270929492840568413 385599476598559815213155)
                ·
                  refine ⟨578399214897839722819733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 385599476598559815213155 578399214897839722819733)
                  ·
                    refine ⟨27112463198336237007175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 578399214897839722819733 27112463198336237007175)
                    ·
                      rfl

theorem cell22_79202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 3, 1, 6].length) (baseStart_79202 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_79202 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_79202 prefixEnd_79202 := by exact prefixLift 79202
  have htrace : WordTrace (prefixWord ++ tailWord_79202) baseStart_79202 baseEnd_79202 := by
    simpa [prefixWord, tailWord_79202, baseEnd_79202] using wordTrace_append hprefix tailTrace_79202
  have hstable : (prefixWord ++ tailWord_79202).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_79202).length < 2 ^ (prefixWord ++ tailWord_79202).sum := by decide
  have hdescent : baseEnd_79202 < baseStart_79202 := by decide
  rcases family_descends (prefixWord ++ tailWord_79202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_79234 : List Nat := [3, 4, 2, 1, 1, 1, 1, 9]
def baseStart_79234 : Nat := 118140960795 + 79234 * 2 ^ 59
def prefixEnd_79234 : Nat := 4983230072969 + 3 ^ 40 * 79234 * 2
def baseEnd_79234 : Nat := 3013713050255424467453

theorem tailTrace_79234 : CollatzResearch.WordTrace tailWord_79234 prefixEnd_79234 3013713050255424467453 := by
  unfold tailWord_79234
  simp only [CollatzResearch.WordTrace]
  refine ⟨722475348739056233741189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1926600929970816623309837 722475348739056233741189)
  ·
    refine ⟨135464127888573043826473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 722475348739056233741189 135464127888573043826473)
    ·
      refine ⟨101598095916429782869855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135464127888573043826473 101598095916429782869855)
      ·
        refine ⟨152397143874644674304783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101598095916429782869855 152397143874644674304783)
        ·
          refine ⟨228595715811967011457175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 152397143874644674304783 228595715811967011457175)
          ·
            refine ⟨342893573717950517185763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 228595715811967011457175 342893573717950517185763)
            ·
              refine ⟨514340360576925775778645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 342893573717950517185763 514340360576925775778645)
              ·
                refine ⟨3013713050255424467453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 514340360576925775778645 3013713050255424467453)
                ·
                  rfl

theorem cell22_79234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 9].length) (baseStart_79234 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_79234 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_79234 prefixEnd_79234 := by exact prefixLift 79234
  have htrace : WordTrace (prefixWord ++ tailWord_79234) baseStart_79234 baseEnd_79234 := by
    simpa [prefixWord, tailWord_79234, baseEnd_79234] using wordTrace_append hprefix tailTrace_79234
  have hstable : (prefixWord ++ tailWord_79234).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_79234).length < 2 ^ (prefixWord ++ tailWord_79234).sum := by decide
  have hdescent : baseEnd_79234 < baseStart_79234 := by decide
  rcases family_descends (prefixWord ++ tailWord_79234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_79275 : List Nat := [1, 1, 1, 1, 2, 1, 1, 2, 4, 8]
def baseStart_79275 : Nat := 118140960795 + 79275 * 2 ^ 59
def prefixEnd_79275 : Nat := 4983230072969 + 3 ^ 40 * 79275 * 2
def baseEnd_79275 : Nat := 27137452590188379931951

theorem tailTrace_79275 : CollatzResearch.WordTrace tailWord_79275 prefixEnd_79275 27137452590188379931951 := by
  unfold tailWord_79275
  simp only [CollatzResearch.WordTrace]
  refine ⟨2891396787807688937207279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1927597858538459291471519 2891396787807688937207279)
  ·
    refine ⟨4337095181711533405810919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2891396787807688937207279 4337095181711533405810919)
    ·
      refine ⟨6505642772567300108716379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4337095181711533405810919 6505642772567300108716379)
      ·
        refine ⟨9758464158850950163074569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6505642772567300108716379 9758464158850950163074569)
        ·
          refine ⟨7318848119138212622305927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9758464158850950163074569 7318848119138212622305927)
          ·
            refine ⟨10978272178707318933458891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7318848119138212622305927 10978272178707318933458891)
            ·
              refine ⟨16467408268060978400188337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10978272178707318933458891 16467408268060978400188337)
              ·
                refine ⟨12350556201045733800141253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16467408268060978400188337 12350556201045733800141253)
                ·
                  refine ⟨2315729287696075087526485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12350556201045733800141253 2315729287696075087526485)
                  ·
                    refine ⟨27137452590188379931951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 2315729287696075087526485 27137452590188379931951)
                    ·
                      rfl

theorem cell22_79275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 4, 8].length) (baseStart_79275 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_79275 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_79275 prefixEnd_79275 := by exact prefixLift 79275
  have htrace : WordTrace (prefixWord ++ tailWord_79275) baseStart_79275 baseEnd_79275 := by
    simpa [prefixWord, tailWord_79275, baseEnd_79275] using wordTrace_append hprefix tailTrace_79275
  have hstable : (prefixWord ++ tailWord_79275).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_79275).length < 2 ^ (prefixWord ++ tailWord_79275).sum := by decide
  have hdescent : baseEnd_79275 < baseStart_79275 := by decide
  rcases family_descends (prefixWord ++ tailWord_79275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_79339 : List Nat := [1, 1, 1, 1, 2, 3, 2, 6, 2, 3]
def baseStart_79339 : Nat := 118140960795 + 79339 * 2 ^ 59
def prefixEnd_79339 : Nat := 4983230072969 + 3 ^ 40 * 79339 * 2
def baseEnd_79339 : Nat := 27159361098113546331755

theorem tailTrace_79339 : CollatzResearch.WordTrace tailWord_79339 prefixEnd_79339 27159361098113546331755 := by
  unfold tailWord_79339
  simp only [CollatzResearch.WordTrace]
  refine ⟨2893731059575827867537071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1929154039717218578358047 2893731059575827867537071)
  ·
    refine ⟨4340596589363741801305607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2893731059575827867537071 4340596589363741801305607)
    ·
      refine ⟨6510894884045612701958411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4340596589363741801305607 6510894884045612701958411)
      ·
        refine ⟨9766342326068419052937617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6510894884045612701958411 9766342326068419052937617)
        ·
          refine ⟨7324756744551314289703213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9766342326068419052937617 7324756744551314289703213)
          ·
            refine ⟨2746783779206742858638705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7324756744551314289703213 2746783779206742858638705)
            ·
              refine ⟨2060087834405057143979029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2746783779206742858638705 2060087834405057143979029)
              ·
                refine ⟨96566617237737053624017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2060087834405057143979029 96566617237737053624017)
                ·
                  refine ⟨72424962928302790218013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 96566617237737053624017 72424962928302790218013)
                  ·
                    refine ⟨27159361098113546331755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 72424962928302790218013 27159361098113546331755)
                    ·
                      rfl

theorem cell22_79339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 6, 2, 3].length) (baseStart_79339 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_79339 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_79339 prefixEnd_79339 := by exact prefixLift 79339
  have htrace : WordTrace (prefixWord ++ tailWord_79339) baseStart_79339 baseEnd_79339 := by
    simpa [prefixWord, tailWord_79339, baseEnd_79339] using wordTrace_append hprefix tailTrace_79339
  have hstable : (prefixWord ++ tailWord_79339).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_79339).length < 2 ^ (prefixWord ++ tailWord_79339).sum := by decide
  have hdescent : baseEnd_79339 < baseStart_79339 := by decide
  rcases family_descends (prefixWord ++ tailWord_79339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_79341 : List Nat := [1, 5, 1, 3, 2, 1, 2, 1, 6]
def baseStart_79341 : Nat := 118140960795 + 79341 * 2 ^ 59
def prefixEnd_79341 : Nat := 4983230072969 + 3 ^ 40 * 79341 * 2
def baseEnd_79341 : Nat := 9053348579662069260583

theorem tailTrace_79341 : CollatzResearch.WordTrace tailWord_79341 prefixEnd_79341 9053348579662069260583 := by
  unfold tailWord_79341
  simp only [CollatzResearch.WordTrace]
  refine ⟨2893804005568582209109877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1929202670379054806073251 2893804005568582209109877)
  ·
    refine ⟨271294125522054582104051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2893804005568582209109877 271294125522054582104051)
    ·
      refine ⟨406941188283081873156077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 271294125522054582104051 406941188283081873156077)
      ·
        refine ⟨152602945606155702433529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 406941188283081873156077 152602945606155702433529)
        ·
          refine ⟨114452209204616776825147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 152602945606155702433529 114452209204616776825147)
          ·
            refine ⟨171678313806925165237721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114452209204616776825147 171678313806925165237721)
            ·
              refine ⟨128758735355193873928291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 171678313806925165237721 128758735355193873928291)
              ·
                refine ⟨193138103032790810892437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 128758735355193873928291 193138103032790810892437)
                ·
                  refine ⟨9053348579662069260583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 193138103032790810892437 9053348579662069260583)
                  ·
                    rfl

theorem cell22_79341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 2, 1, 6].length) (baseStart_79341 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_79341 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_79341 prefixEnd_79341 := by exact prefixLift 79341
  have htrace : WordTrace (prefixWord ++ tailWord_79341) baseStart_79341 baseEnd_79341 := by
    simpa [prefixWord, tailWord_79341, baseEnd_79341] using wordTrace_append hprefix tailTrace_79341
  have hstable : (prefixWord ++ tailWord_79341).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_79341).length < 2 ^ (prefixWord ++ tailWord_79341).sum := by decide
  have hdescent : baseEnd_79341 < baseStart_79341 := by decide
  rcases family_descends (prefixWord ++ tailWord_79341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_79452 : List Nat := [2, 2, 4, 1, 2, 3, 2, 2, 1, 3]
def baseStart_79452 : Nat := 118140960795 + 79452 * 2 ^ 59
def prefixEnd_79452 : Nat := 4983230072969 + 3 ^ 40 * 79452 * 2
def baseEnd_79452 : Nat := 27198043307418918256409

theorem tailTrace_79452 : CollatzResearch.WordTrace tailWord_79452 prefixEnd_79452 27198043307418918256409 := by
  unfold tailWord_79452
  simp only [CollatzResearch.WordTrace]
  refine ⟨1448926254083224083200305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1931901672110965444267073 1448926254083224083200305)
  ·
    refine ⟨1086694690562418062400229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1448926254083224083200305 1086694690562418062400229)
    ·
      refine ⟨203755254480453386700043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1086694690562418062400229 203755254480453386700043)
      ·
        refine ⟨305632881720680080050065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 203755254480453386700043 305632881720680080050065)
        ·
          refine ⟨229224661290510060037549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 305632881720680080050065 229224661290510060037549)
          ·
            refine ⟨85959247983941272514081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 229224661290510060037549 85959247983941272514081)
            ·
              refine ⟨64469435987955954385561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 85959247983941272514081 64469435987955954385561)
              ·
                refine ⟨48352076990966965789171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64469435987955954385561 48352076990966965789171)
                ·
                  refine ⟨72528115486450448683757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48352076990966965789171 72528115486450448683757)
                  ·
                    refine ⟨27198043307418918256409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 72528115486450448683757 27198043307418918256409)
                    ·
                      rfl

theorem cell22_79452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 3, 2, 2, 1, 3].length) (baseStart_79452 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_79452 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_79452 prefixEnd_79452 := by exact prefixLift 79452
  have htrace : WordTrace (prefixWord ++ tailWord_79452) baseStart_79452 baseEnd_79452 := by
    simpa [prefixWord, tailWord_79452, baseEnd_79452] using wordTrace_append hprefix tailTrace_79452
  have hstable : (prefixWord ++ tailWord_79452).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_79452).length < 2 ^ (prefixWord ++ tailWord_79452).sum := by decide
  have hdescent : baseEnd_79452 < baseStart_79452 := by decide
  rcases family_descends (prefixWord ++ tailWord_79452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_79536 : List Nat := [2, 1, 1, 1, 2, 1, 6, 2, 3, 3]
def baseStart_79536 : Nat := 118140960795 + 79536 * 2 ^ 59
def prefixEnd_79536 : Nat := 4983230072969 + 3 ^ 40 * 79536 * 2
def baseEnd_79536 : Nat := 27226798224070699156151

theorem tailTrace_79536 : CollatzResearch.WordTrace tailWord_79536 prefixEnd_79536 27226798224070699156151 := by
  unfold tailWord_79536
  simp only [CollatzResearch.WordTrace]
  refine ⟨1450458119931065256229231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1933944159908087008305641 1450458119931065256229231)
  ·
    refine ⟨2175687179896597884343847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1450458119931065256229231 2175687179896597884343847)
    ·
      refine ⟨3263530769844896826515771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2175687179896597884343847 3263530769844896826515771)
      ·
        refine ⟨4895296154767345239773657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3263530769844896826515771 4895296154767345239773657)
        ·
          refine ⟨3671472116075508929830243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4895296154767345239773657 3671472116075508929830243)
          ·
            refine ⟨5507208174113263394745365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3671472116075508929830243 5507208174113263394745365)
            ·
              refine ⟨258150383161559221628689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 5507208174113263394745365 258150383161559221628689)
              ·
                refine ⟨193612787371169416221517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 258150383161559221628689 193612787371169416221517)
                ·
                  refine ⟨72604795264188531083069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 193612787371169416221517 72604795264188531083069)
                  ·
                    refine ⟨27226798224070699156151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 72604795264188531083069 27226798224070699156151)
                    ·
                      rfl

theorem cell22_79536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 6, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 6, 2, 3, 3].length) (baseStart_79536 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_79536 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_79536 prefixEnd_79536 := by exact prefixLift 79536
  have htrace : WordTrace (prefixWord ++ tailWord_79536) baseStart_79536 baseEnd_79536 := by
    simpa [prefixWord, tailWord_79536, baseEnd_79536] using wordTrace_append hprefix tailTrace_79536
  have hstable : (prefixWord ++ tailWord_79536).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_79536).length < 2 ^ (prefixWord ++ tailWord_79536).sum := by decide
  have hdescent : baseEnd_79536 < baseStart_79536 := by decide
  rcases family_descends (prefixWord ++ tailWord_79536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_79549 : List Nat := [1, 4, 1, 2, 1, 2, 1, 1, 9]
def baseStart_79549 : Nat := 118140960795 + 79549 * 2 ^ 59
def prefixEnd_79549 : Nat := 4983230072969 + 3 ^ 40 * 79549 * 2
def baseEnd_79549 : Nat := 9077082796580999527037

theorem tailTrace_79549 : CollatzResearch.WordTrace tailWord_79549 prefixEnd_79549 9077082796580999527037 := by
  unfold tailWord_79549
  simp only [CollatzResearch.WordTrace]
  refine ⟨2901390388815033732681701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1934260259210022488454467 2901390388815033732681701)
  ·
    refine ⟨544010697902818824877819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2901390388815033732681701 544010697902818824877819)
    ·
      refine ⟨816016046854228237316729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 544010697902818824877819 816016046854228237316729)
      ·
        refine ⟨612012035140671177987547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 816016046854228237316729 612012035140671177987547)
        ·
          refine ⟨918018052711006766981321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 612012035140671177987547 918018052711006766981321)
          ·
            refine ⟨688513539533255075235991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 918018052711006766981321 688513539533255075235991)
            ·
              refine ⟨1032770309299882612853987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 688513539533255075235991 1032770309299882612853987)
              ·
                refine ⟨1549155463949823919280981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1032770309299882612853987 1549155463949823919280981)
                ·
                  refine ⟨9077082796580999527037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 1549155463949823919280981 9077082796580999527037)
                  ·
                    rfl

theorem cell22_79549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 1, 9].length) (baseStart_79549 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_79549 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_79549 prefixEnd_79549 := by exact prefixLift 79549
  have htrace : WordTrace (prefixWord ++ tailWord_79549) baseStart_79549 baseEnd_79549 := by
    simpa [prefixWord, tailWord_79549, baseEnd_79549] using wordTrace_append hprefix tailTrace_79549
  have hstable : (prefixWord ++ tailWord_79549).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_79549).length < 2 ^ (prefixWord ++ tailWord_79549).sum := by decide
  have hdescent : baseEnd_79549 < baseStart_79549 := by decide
  rcases family_descends (prefixWord ++ tailWord_79549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_79566 : List Nat := [4, 1, 1, 1, 3, 1, 2, 4, 5]
def baseStart_79566 : Nat := 118140960795 + 79566 * 2 ^ 59
def prefixEnd_79566 : Nat := 4983230072969 + 3 ^ 40 * 79566 * 2
def baseEnd_79566 : Nat := 9079022612386873635353

theorem tailTrace_79566 : CollatzResearch.WordTrace tailWord_79566 prefixEnd_79566 9079022612386873635353 := by
  unfold tailWord_79566
  simp only [CollatzResearch.WordTrace]
  refine ⟨362751303719180704506319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1934673619835630424033701 362751303719180704506319)
  ·
    refine ⟨544126955578771056759479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 362751303719180704506319 544126955578771056759479)
    ·
      refine ⟨816190433368156585139219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 544126955578771056759479 816190433368156585139219)
      ·
        refine ⟨1224285650052234877708829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 816190433368156585139219 1224285650052234877708829)
        ·
          refine ⟨459107118769588079140811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1224285650052234877708829 459107118769588079140811)
          ·
            refine ⟨688660678154382118711217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 459107118769588079140811 688660678154382118711217)
            ·
              refine ⟨516495508615786589033413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 688660678154382118711217 516495508615786589033413)
              ·
                refine ⟨96842907865459985443765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 516495508615786589033413 96842907865459985443765)
                ·
                  refine ⟨9079022612386873635353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 96842907865459985443765 9079022612386873635353)
                  ·
                    rfl

theorem cell22_79566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 4, 5].length) (baseStart_79566 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_79566 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_79566 prefixEnd_79566 := by exact prefixLift 79566
  have htrace : WordTrace (prefixWord ++ tailWord_79566) baseStart_79566 baseEnd_79566 := by
    simpa [prefixWord, tailWord_79566, baseEnd_79566] using wordTrace_append hprefix tailTrace_79566
  have hstable : (prefixWord ++ tailWord_79566).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_79566).length < 2 ^ (prefixWord ++ tailWord_79566).sum := by decide
  have hdescent : baseEnd_79566 < baseStart_79566 := by decide
  rcases family_descends (prefixWord ++ tailWord_79566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_79570 : List Nat := [3, 2, 2, 2, 2, 3, 1, 1, 3, 3]
def baseStart_79570 : Nat := 118140960795 + 79570 * 2 ^ 59
def prefixEnd_79570 : Nat := 4983230072969 + 3 ^ 40 * 79570 * 2
def baseEnd_79570 : Nat := 27238437118905943806047

theorem tailTrace_79570 : CollatzResearch.WordTrace tailWord_79570 prefixEnd_79570 27238437118905943806047 := by
  unfold tailWord_79570
  simp only [CollatzResearch.WordTrace]
  refine ⟨725539080434738579799041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1934770881159302879464109 725539080434738579799041)
  ·
    refine ⟨544154310326053934849281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 725539080434738579799041 544154310326053934849281)
    ·
      refine ⟨408115732744540451136961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 544154310326053934849281 408115732744540451136961)
      ·
        refine ⟨306086799558405338352721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 408115732744540451136961 306086799558405338352721)
        ·
          refine ⟨229565099668804003764541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 306086799558405338352721 229565099668804003764541)
          ·
            refine ⟨86086912375801501411703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 229565099668804003764541 86086912375801501411703)
            ·
              refine ⟨129130368563702252117555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86086912375801501411703 129130368563702252117555)
              ·
                refine ⟨193695552845553378176333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 129130368563702252117555 193695552845553378176333)
                ·
                  refine ⟨72635832317082516816125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 193695552845553378176333 72635832317082516816125)
                  ·
                    refine ⟨27238437118905943806047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 72635832317082516816125 27238437118905943806047)
                    ·
                      rfl

theorem cell22_79570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 3, 1, 1, 3, 3].length) (baseStart_79570 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_79570 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_79570 prefixEnd_79570 := by exact prefixLift 79570
  have htrace : WordTrace (prefixWord ++ tailWord_79570) baseStart_79570 baseEnd_79570 := by
    simpa [prefixWord, tailWord_79570, baseEnd_79570] using wordTrace_append hprefix tailTrace_79570
  have hstable : (prefixWord ++ tailWord_79570).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_79570).length < 2 ^ (prefixWord ++ tailWord_79570).sum := by decide
  have hdescent : baseEnd_79570 < baseStart_79570 := by decide
  rcases family_descends (prefixWord ++ tailWord_79570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_79662 : List Nat := [4, 1, 3, 2, 2, 1, 2, 3, 4]
def baseStart_79662 : Nat := 118140960795 + 79662 * 2 ^ 59
def prefixEnd_79662 : Nat := 4983230072969 + 3 ^ 40 * 79662 * 2
def baseEnd_79662 : Nat := 9089976866349456835255

theorem tailTrace_79662 : CollatzResearch.WordTrace tailWord_79662 prefixEnd_79662 9089976866349456835255 := by
  unfold tailWord_79662
  simp only [CollatzResearch.WordTrace]
  refine ⟨363188979675706753943155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1937007891603769354363493 363188979675706753943155)
  ·
    refine ⟨544783469513560130914733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 363188979675706753943155 544783469513560130914733)
    ·
      refine ⟨204293801067585049093025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 544783469513560130914733 204293801067585049093025)
      ·
        refine ⟨153220350800688786819769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 204293801067585049093025 153220350800688786819769)
        ·
          refine ⟨114915263100516590114827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 153220350800688786819769 114915263100516590114827)
          ·
            refine ⟨172372894650774885172241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114915263100516590114827 172372894650774885172241)
            ·
              refine ⟨129279670988081163879181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 172372894650774885172241 129279670988081163879181)
              ·
                refine ⟨48479876620530436454693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 129279670988081163879181 48479876620530436454693)
                ·
                  refine ⟨9089976866349456835255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 48479876620530436454693 9089976866349456835255)
                  ·
                    rfl

theorem cell22_79662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 2, 3, 4].length) (baseStart_79662 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_79662 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_79662 prefixEnd_79662 := by exact prefixLift 79662
  have htrace : WordTrace (prefixWord ++ tailWord_79662) baseStart_79662 baseEnd_79662 := by
    simpa [prefixWord, tailWord_79662, baseEnd_79662] using wordTrace_append hprefix tailTrace_79662
  have hstable : (prefixWord ++ tailWord_79662).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_79662).length < 2 ^ (prefixWord ++ tailWord_79662).sum := by decide
  have hdescent : baseEnd_79662 < baseStart_79662 := by decide
  rcases family_descends (prefixWord ++ tailWord_79662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_79673 : List Nat := [1, 2, 1, 7, 1, 1, 9]
def baseStart_79673 : Nat := 118140960795 + 79673 * 2 ^ 59
def prefixEnd_79673 : Nat := 4983230072969 + 3 ^ 40 * 79673 * 2
def baseEnd_79673 : Nat := 1010136893475852165953

theorem tailTrace_79673 : CollatzResearch.WordTrace tailWord_79673 prefixEnd_79673 1010136893475852165953 := by
  unfold tailWord_79673
  simp only [CollatzResearch.WordTrace]
  refine ⟨2905913040365802910195673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1937275360243868606797115 2905913040365802910195673)
  ·
    refine ⟨2179434780274352182646755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2905913040365802910195673 2179434780274352182646755)
    ·
      refine ⟨3269152170411528273970133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2179434780274352182646755 3269152170411528273970133)
      ·
        refine ⟨76620753994020193921175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 3269152170411528273970133 76620753994020193921175)
        ·
          refine ⟨114931130991030290881763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76620753994020193921175 114931130991030290881763)
          ·
            refine ⟨172396696486545436322645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114931130991030290881763 172396696486545436322645)
            ·
              refine ⟨1010136893475852165953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 172396696486545436322645 1010136893475852165953)
              ·
                rfl

theorem cell22_79673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 9].length) (baseStart_79673 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_79673 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_79673 prefixEnd_79673 := by exact prefixLift 79673
  have htrace : WordTrace (prefixWord ++ tailWord_79673) baseStart_79673 baseEnd_79673 := by
    simpa [prefixWord, tailWord_79673, baseEnd_79673] using wordTrace_append hprefix tailTrace_79673
  have hstable : (prefixWord ++ tailWord_79673).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_79673).length < 2 ^ (prefixWord ++ tailWord_79673).sum := by decide
  have hdescent : baseEnd_79673 < baseStart_79673 := by decide
  rcases family_descends (prefixWord ++ tailWord_79673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_79677 : List Nat := [1, 4, 1, 4, 1, 3, 1, 2, 2, 3]
def baseStart_79677 : Nat := 118140960795 + 79677 * 2 ^ 59
def prefixEnd_79677 : Nat := 4983230072969 + 3 ^ 40 * 79677 * 2
def baseEnd_79677 : Nat := 27275065405593331380719

theorem tailTrace_79677 : CollatzResearch.WordTrace tailWord_79677 prefixEnd_79677 27275065405593331380719 := by
  unfold tailWord_79677
  simp only [CollatzResearch.WordTrace]
  refine ⟨2906058932351311593341285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1937372621567541062227523 2906058932351311593341285)
  ·
    refine ⟨544886049815870923751491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2906058932351311593341285 544886049815870923751491)
    ·
      refine ⟨817329074723806385627237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 544886049815870923751491 817329074723806385627237)
      ·
        refine ⟨153249201510713697305107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 817329074723806385627237 153249201510713697305107)
        ·
          refine ⟨229873802266070545957661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 153249201510713697305107 229873802266070545957661)
          ·
            refine ⟨86202675849776454734123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 229873802266070545957661 86202675849776454734123)
            ·
              refine ⟨129304013774664682101185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86202675849776454734123 129304013774664682101185)
              ·
                refine ⟨96978010330998511575889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 129304013774664682101185 96978010330998511575889)
                ·
                  refine ⟨72733507748248883681917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 96978010330998511575889 72733507748248883681917)
                  ·
                    refine ⟨27275065405593331380719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 72733507748248883681917 27275065405593331380719)
                    ·
                      rfl

theorem cell22_79677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 3, 1, 2, 2, 3].length) (baseStart_79677 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_79677 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_79677 prefixEnd_79677 := by exact prefixLift 79677
  have htrace : WordTrace (prefixWord ++ tailWord_79677) baseStart_79677 baseEnd_79677 := by
    simpa [prefixWord, tailWord_79677, baseEnd_79677] using wordTrace_append hprefix tailTrace_79677
  have hstable : (prefixWord ++ tailWord_79677).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_79677).length < 2 ^ (prefixWord ++ tailWord_79677).sum := by decide
  have hdescent : baseEnd_79677 < baseStart_79677 := by decide
  rcases family_descends (prefixWord ++ tailWord_79677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_79688 : List Nat := [2, 1, 3, 1, 1, 4, 1, 3, 3, 3]
def baseStart_79688 : Nat := 118140960795 + 79688 * 2 ^ 59
def prefixEnd_79688 : Nat := 4983230072969 + 3 ^ 40 * 79688 * 2
def baseEnd_79688 : Nat := 27278830930392969355685

theorem tailTrace_79688 : CollatzResearch.WordTrace tailWord_79688 prefixEnd_79688 27278830930392969355685 := by
  unfold tailWord_79688
  simp only [CollatzResearch.WordTrace]
  refine ⟨1453230067655730235995859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1937640090207640314661145 1453230067655730235995859)
  ·
    refine ⟨2179845101483595353993789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1453230067655730235995859 2179845101483595353993789)
    ·
      refine ⟨817441913056348257747671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2179845101483595353993789 817441913056348257747671)
      ·
        refine ⟨1226162869584522386621507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 817441913056348257747671 1226162869584522386621507)
        ·
          refine ⟨1839244304376783579932261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1226162869584522386621507 1839244304376783579932261)
          ·
            refine ⟨344858307070646921237299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1839244304376783579932261 344858307070646921237299)
            ·
              refine ⟨517287460605970381855949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 344858307070646921237299 517287460605970381855949)
              ·
                refine ⟨193982797727238893195981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 517287460605970381855949 193982797727238893195981)
                ·
                  refine ⟨72743549147714584948493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 193982797727238893195981 72743549147714584948493)
                  ·
                    refine ⟨27278830930392969355685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 72743549147714584948493 27278830930392969355685)
                    ·
                      rfl

theorem cell22_79688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 3, 3, 3].length) (baseStart_79688 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_79688 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_79688 prefixEnd_79688 := by exact prefixLift 79688
  have htrace : WordTrace (prefixWord ++ tailWord_79688) baseStart_79688 baseEnd_79688 := by
    simpa [prefixWord, tailWord_79688, baseEnd_79688] using wordTrace_append hprefix tailTrace_79688
  have hstable : (prefixWord ++ tailWord_79688).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_79688).length < 2 ^ (prefixWord ++ tailWord_79688).sum := by decide
  have hdescent : baseEnd_79688 < baseStart_79688 := by decide
  rcases family_descends (prefixWord ++ tailWord_79688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_79731 : List Nat := [1, 1, 1, 2, 2, 1, 3, 2, 5, 4]
def baseStart_79731 : Nat := 118140960795 + 79731 * 2 ^ 59
def prefixEnd_79731 : Nat := 4983230072969 + 3 ^ 40 * 79731 * 2
def baseEnd_79731 : Nat := 27293550709155190530553

theorem tailTrace_79731 : CollatzResearch.WordTrace tailWord_79731 prefixEnd_79731 27293550709155190530553 := by
  unfold tailWord_79731
  simp only [CollatzResearch.WordTrace]
  refine ⟨2908028474155678815807047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1938685649437119210538031 2908028474155678815807047)
  ·
    refine ⟨4362042711233518223710571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2908028474155678815807047 4362042711233518223710571)
    ·
      refine ⟨6543064066850277335565857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4362042711233518223710571 6543064066850277335565857)
      ·
        refine ⟨4907298050137708001674393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6543064066850277335565857 4907298050137708001674393)
        ·
          refine ⟨3680473537603281001255795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4907298050137708001674393 3680473537603281001255795)
          ·
            refine ⟨5520710306404921501883693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3680473537603281001255795 5520710306404921501883693)
            ·
              refine ⟨2070266364901845563206385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5520710306404921501883693 2070266364901845563206385)
              ·
                refine ⟨1552699773676384172404789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2070266364901845563206385 1552699773676384172404789)
                ·
                  refine ⟨145565603782161016162949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1552699773676384172404789 145565603782161016162949)
                  ·
                    refine ⟨27293550709155190530553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 145565603782161016162949 27293550709155190530553)
                    ·
                      rfl

theorem cell22_79731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 2, 5, 4].length) (baseStart_79731 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_79731 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_79731 prefixEnd_79731 := by exact prefixLift 79731
  have htrace : WordTrace (prefixWord ++ tailWord_79731) baseStart_79731 baseEnd_79731 := by
    simpa [prefixWord, tailWord_79731, baseEnd_79731] using wordTrace_append hprefix tailTrace_79731
  have hstable : (prefixWord ++ tailWord_79731).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_79731).length < 2 ^ (prefixWord ++ tailWord_79731).sum := by decide
  have hdescent : baseEnd_79731 < baseStart_79731 := by decide
  rcases family_descends (prefixWord ++ tailWord_79731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_79752 : List Nat := [2, 1, 3, 3, 3, 2, 2, 1, 5]
def baseStart_79752 : Nat := 118140960795 + 79752 * 2 ^ 59
def prefixEnd_79752 : Nat := 4983230072969 + 3 ^ 40 * 79752 * 2
def baseEnd_79752 : Nat := 9100246479439378585163

theorem tailTrace_79752 : CollatzResearch.WordTrace tailWord_79752 prefixEnd_79752 9100246479439378585163 := by
  unfold tailWord_79752
  simp only [CollatzResearch.WordTrace]
  refine ⟨1454397203539799701160755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1939196271386399601547673 1454397203539799701160755)
  ·
    refine ⟨2181595805309699551741133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1454397203539799701160755 2181595805309699551741133)
    ·
      refine ⟨818098426991137331902925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2181595805309699551741133 818098426991137331902925)
      ·
        refine ⟨306786910121676499463597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 818098426991137331902925 306786910121676499463597)
        ·
          refine ⟨115045091295628687298849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 306786910121676499463597 115045091295628687298849)
          ·
            refine ⟨86283818471721515474137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 115045091295628687298849 86283818471721515474137)
            ·
              refine ⟨64712863853791136605603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86283818471721515474137 64712863853791136605603)
              ·
                refine ⟨97069295780686704908405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64712863853791136605603 97069295780686704908405)
                ·
                  refine ⟨9100246479439378585163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 97069295780686704908405 9100246479439378585163)
                  ·
                    rfl

theorem cell22_79752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 2, 2, 1, 5].length) (baseStart_79752 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_79752 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_79752 prefixEnd_79752 := by exact prefixLift 79752
  have htrace : WordTrace (prefixWord ++ tailWord_79752) baseStart_79752 baseEnd_79752 := by
    simpa [prefixWord, tailWord_79752, baseEnd_79752] using wordTrace_append hprefix tailTrace_79752
  have hstable : (prefixWord ++ tailWord_79752).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_79752).length < 2 ^ (prefixWord ++ tailWord_79752).sum := by decide
  have hdescent : baseEnd_79752 < baseStart_79752 := by decide
  rcases family_descends (prefixWord ++ tailWord_79752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_79790 : List Nat := [4, 1, 5, 1, 1, 2, 2, 2, 1, 3]
def baseStart_79790 : Nat := 118140960795 + 79790 * 2 ^ 59
def prefixEnd_79790 : Nat := 4983230072969 + 3 ^ 40 * 79790 * 2
def baseEnd_79790 : Nat := 27313747614898703305373

theorem tailTrace_79790 : CollatzResearch.WordTrace tailWord_79790 prefixEnd_79790 27313747614898703305373 := by
  unfold tailWord_79790
  simp only [CollatzResearch.WordTrace]
  refine ⟨363772547617741486525603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1940120253961287928136549 363772547617741486525603)
  ·
    refine ⟨545658821426612229788405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 363772547617741486525603 545658821426612229788405)
    ·
      refine ⟨51155514508744896542663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 545658821426612229788405 51155514508744896542663)
      ·
        refine ⟨76733271763117344813995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51155514508744896542663 76733271763117344813995)
        ·
          refine ⟨115099907644676017220993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76733271763117344813995 115099907644676017220993)
          ·
            refine ⟨86324930733507012915745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 115099907644676017220993 86324930733507012915745)
            ·
              refine ⟨64743698050130259686809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86324930733507012915745 64743698050130259686809)
              ·
                refine ⟨48557773537597694765107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64743698050130259686809 48557773537597694765107)
                ·
                  refine ⟨72836660306396542147661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48557773537597694765107 72836660306396542147661)
                  ·
                    refine ⟨27313747614898703305373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 72836660306396542147661 27313747614898703305373)
                    ·
                      rfl

theorem cell22_79790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 2, 2, 2, 1, 3].length) (baseStart_79790 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_79790 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_79790 prefixEnd_79790 := by exact prefixLift 79790
  have htrace : WordTrace (prefixWord ++ tailWord_79790) baseStart_79790 baseEnd_79790 := by
    simpa [prefixWord, tailWord_79790, baseEnd_79790] using wordTrace_append hprefix tailTrace_79790
  have hstable : (prefixWord ++ tailWord_79790).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_79790).length < 2 ^ (prefixWord ++ tailWord_79790).sum := by decide
  have hdescent : baseEnd_79790 < baseStart_79790 := by decide
  rcases family_descends (prefixWord ++ tailWord_79790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_79795 : List Nat := [1, 1, 1, 2, 3, 1, 6, 2, 2, 3]
def baseStart_79795 : Nat := 118140960795 + 79795 * 2 ^ 59
def prefixEnd_79795 : Nat := 4983230072969 + 3 ^ 40 * 79795 * 2
def baseEnd_79795 : Nat := 27315459217080356930357

theorem tailTrace_79795 : CollatzResearch.WordTrace tailWord_79795 prefixEnd_79795 27315459217080356930357 := by
  unfold tailWord_79795
  simp only [CollatzResearch.WordTrace]
  refine ⟨2910362745923817746136839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1940241830615878497424559 2910362745923817746136839)
  ·
    refine ⟨4365544118885726619205259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2910362745923817746136839 4365544118885726619205259)
    ·
      refine ⟨6548316178328589928807889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4365544118885726619205259 6548316178328589928807889)
      ·
        refine ⟨4911237133746442446605917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6548316178328589928807889 4911237133746442446605917)
        ·
          refine ⟨1841713925154915917477219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4911237133746442446605917 1841713925154915917477219)
          ·
            refine ⟨2762570887732373876215829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1841713925154915917477219 2762570887732373876215829)
            ·
              refine ⟨129495510362455025447617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 2762570887732373876215829 129495510362455025447617)
              ·
                refine ⟨97121632771841269085713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 129495510362455025447617 97121632771841269085713)
                ·
                  refine ⟨72841224578880951814285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 97121632771841269085713 72841224578880951814285)
                  ·
                    refine ⟨27315459217080356930357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 72841224578880951814285 27315459217080356930357)
                    ·
                      rfl

theorem cell22_79795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 6, 2, 2, 3].length) (baseStart_79795 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_79795 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_79795 prefixEnd_79795 := by exact prefixLift 79795
  have htrace : WordTrace (prefixWord ++ tailWord_79795) baseStart_79795 baseEnd_79795 := by
    simpa [prefixWord, tailWord_79795, baseEnd_79795] using wordTrace_append hprefix tailTrace_79795
  have hstable : (prefixWord ++ tailWord_79795).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_79795).length < 2 ^ (prefixWord ++ tailWord_79795).sum := by decide
  have hdescent : baseEnd_79795 < baseStart_79795 := by decide
  rcases family_descends (prefixWord ++ tailWord_79795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_79797 : List Nat := [1, 3, 3, 2, 1, 2, 4, 2, 4]
def baseStart_79797 : Nat := 118140960795 + 79797 * 2 ^ 59
def prefixEnd_79797 : Nat := 4983230072969 + 3 ^ 40 * 79797 * 2
def baseEnd_79797 : Nat := 9105381285984339460117

theorem tailTrace_79797 : CollatzResearch.WordTrace tailWord_79797 prefixEnd_79797 9105381285984339460117 := by
  unfold tailWord_79797
  simp only [CollatzResearch.WordTrace]
  refine ⟨2910435691916572087709645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1940290461277714725139763 2910435691916572087709645)
  ·
    refine ⟨1091413384468714532891117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2910435691916572087709645 1091413384468714532891117)
    ·
      refine ⟨409280019175767949834169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1091413384468714532891117 409280019175767949834169)
      ·
        refine ⟨306960014381825962375627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 409280019175767949834169 306960014381825962375627)
        ·
          refine ⟨460440021572738943563441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 306960014381825962375627 460440021572738943563441)
          ·
            refine ⟨345330016179554207672581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 460440021572738943563441 345330016179554207672581)
            ·
              refine ⟨64749378033666413938609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 345330016179554207672581 64749378033666413938609)
              ·
                refine ⟨48562033525249810453957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64749378033666413938609 48562033525249810453957)
                ·
                  refine ⟨9105381285984339460117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 48562033525249810453957 9105381285984339460117)
                  ·
                    rfl

theorem cell22_79797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 4, 2, 4].length) (baseStart_79797 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_79797 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_79797 prefixEnd_79797 := by exact prefixLift 79797
  have htrace : WordTrace (prefixWord ++ tailWord_79797) baseStart_79797 baseEnd_79797 := by
    simpa [prefixWord, tailWord_79797, baseEnd_79797] using wordTrace_append hprefix tailTrace_79797
  have hstable : (prefixWord ++ tailWord_79797).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_79797).length < 2 ^ (prefixWord ++ tailWord_79797).sum := by decide
  have hdescent : baseEnd_79797 < baseStart_79797 := by decide
  rcases family_descends (prefixWord ++ tailWord_79797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_79857 : List Nat := [1, 2, 2, 2, 5, 1, 2, 1, 3, 3]
def baseStart_79857 : Nat := 118140960795 + 79857 * 2 ^ 59
def prefixEnd_79857 : Nat := 4983230072969 + 3 ^ 40 * 79857 * 2
def baseEnd_79857 : Nat := 27336683084132861880167

theorem tailTrace_79857 : CollatzResearch.WordTrace tailWord_79857 prefixEnd_79857 27336683084132861880167 := by
  unfold tailWord_79857
  simp only [CollatzResearch.WordTrace]
  refine ⟨2912624071699202334893825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1941749381132801556595883 2912624071699202334893825)
  ·
    refine ⟨2184468053774401751170369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2912624071699202334893825 2184468053774401751170369)
    ·
      refine ⟨1638351040330801313377777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2184468053774401751170369 1638351040330801313377777)
      ·
        refine ⟨1228763280248100985033333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1638351040330801313377777 1228763280248100985033333)
        ·
          refine ⟨115196557523259467346875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1228763280248100985033333 115196557523259467346875)
          ·
            refine ⟨172794836284889201020313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115196557523259467346875 172794836284889201020313)
            ·
              refine ⟨129596127213666900765235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 172794836284889201020313 129596127213666900765235)
              ·
                refine ⟨194394190820500351147853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 129596127213666900765235 194394190820500351147853)
                ·
                  refine ⟨72897821557687631680445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 194394190820500351147853 72897821557687631680445)
                  ·
                    refine ⟨27336683084132861880167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 72897821557687631680445 27336683084132861880167)
                    ·
                      rfl

theorem cell22_79857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 2, 1, 3, 3].length) (baseStart_79857 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_79857 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_79857 prefixEnd_79857 := by exact prefixLift 79857
  have htrace : WordTrace (prefixWord ++ tailWord_79857) baseStart_79857 baseEnd_79857 := by
    simpa [prefixWord, tailWord_79857, baseEnd_79857] using wordTrace_append hprefix tailTrace_79857
  have hstable : (prefixWord ++ tailWord_79857).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_79857).length < 2 ^ (prefixWord ++ tailWord_79857).sum := by decide
  have hdescent : baseEnd_79857 < baseStart_79857 := by decide
  rcases family_descends (prefixWord ++ tailWord_79857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_79868 : List Nat := [2, 2, 2, 1, 2, 2, 1, 3, 2, 5]
def baseStart_79868 : Nat := 118140960795 + 79868 * 2 ^ 59
def prefixEnd_79868 : Nat := 4983230072969 + 3 ^ 40 * 79868 * 2
def baseEnd_79868 : Nat := 27340448608932499855133

theorem tailTrace_79868 : CollatzResearch.WordTrace tailWord_79868 prefixEnd_79868 27340448608932499855133 := by
  unfold tailWord_79868
  simp only [CollatzResearch.WordTrace]
  refine ⟨1456512637329675606772129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1942016849772900809029505 1456512637329675606772129)
  ·
    refine ⟨1092384477997256705079097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1456512637329675606772129 1092384477997256705079097)
    ·
      refine ⟨819288358497942528809323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1092384477997256705079097 819288358497942528809323)
      ·
        refine ⟨1228932537746913793213985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 819288358497942528809323 1228932537746913793213985)
        ·
          refine ⟨921699403310185344910489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1228932537746913793213985 921699403310185344910489)
          ·
            refine ⟨691274552482639008682867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 921699403310185344910489 691274552482639008682867)
            ·
              refine ⟨1036911828723958513024301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 691274552482639008682867 1036911828723958513024301)
              ·
                refine ⟨388841935771484442384113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1036911828723958513024301 388841935771484442384113)
                ·
                  refine ⟨291631451828613331788085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 388841935771484442384113 291631451828613331788085)
                  ·
                    refine ⟨27340448608932499855133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 291631451828613331788085 27340448608932499855133)
                    ·
                      rfl

theorem cell22_79868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 3, 2, 5].length) (baseStart_79868 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_79868 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_79868 prefixEnd_79868 := by exact prefixLift 79868
  have htrace : WordTrace (prefixWord ++ tailWord_79868) baseStart_79868 baseEnd_79868 := by
    simpa [prefixWord, tailWord_79868, baseEnd_79868] using wordTrace_append hprefix tailTrace_79868
  have hstable : (prefixWord ++ tailWord_79868).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_79868).length < 2 ^ (prefixWord ++ tailWord_79868).sum := by decide
  have hdescent : baseEnd_79868 < baseStart_79868 := by decide
  rcases family_descends (prefixWord ++ tailWord_79868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_79943 : List Nat := [1, 1, 4, 1, 3, 1, 1, 10]
def baseStart_79943 : Nat := 118140960795 + 79943 * 2 ^ 59
def prefixEnd_79943 : Nat := 4983230072969 + 3 ^ 40 * 79943 * 2
def baseEnd_79943 : Nat := 3040680293517478247767

theorem tailTrace_79943 : CollatzResearch.WordTrace tailWord_79943 prefixEnd_79943 3040680293517478247767 := by
  unfold tailWord_79943
  simp only [CollatzResearch.WordTrace]
  refine ⟨2915760749387639022524483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1943840499591759348349655 2915760749387639022524483)
  ·
    refine ⟨4373641124081458533786725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2915760749387639022524483 4373641124081458533786725)
    ·
      refine ⟨820057710765273475085011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4373641124081458533786725 820057710765273475085011)
      ·
        refine ⟨1230086566147910212627517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 820057710765273475085011 1230086566147910212627517)
        ·
          refine ⟨461282462305466329735319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1230086566147910212627517 461282462305466329735319)
          ·
            refine ⟨691923693458199494602979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 461282462305466329735319 691923693458199494602979)
            ·
              refine ⟨1037885540187299241904469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 691923693458199494602979 1037885540187299241904469)
              ·
                refine ⟨3040680293517478247767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 1037885540187299241904469 3040680293517478247767)
                ·
                  rfl

theorem cell22_79943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 10].length) (baseStart_79943 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_79943 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_79943 prefixEnd_79943 := by exact prefixLift 79943
  have htrace : WordTrace (prefixWord ++ tailWord_79943) baseStart_79943 baseEnd_79943 := by
    simpa [prefixWord, tailWord_79943, baseEnd_79943] using wordTrace_append hprefix tailTrace_79943
  have hstable : (prefixWord ++ tailWord_79943).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_79943).length < 2 ^ (prefixWord ++ tailWord_79943).sum := by decide
  have hdescent : baseEnd_79943 < baseStart_79943 := by decide
  rcases family_descends (prefixWord ++ tailWord_79943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_79945 : List Nat := [1, 2, 1, 1, 2, 2, 6, 1, 2, 4]
def baseStart_79945 : Nat := 118140960795 + 79945 * 2 ^ 59
def prefixEnd_79945 : Nat := 4983230072969 + 3 ^ 40 * 79945 * 2
def baseEnd_79945 : Nat := 27366807282529965679897

theorem tailTrace_79945 : CollatzResearch.WordTrace tailWord_79945 prefixEnd_79945 27366807282529965679897 := by
  unfold tailWord_79945
  simp only [CollatzResearch.WordTrace]
  refine ⟨2915833695380393364097289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1943889130253595576064859 2915833695380393364097289)
  ·
    refine ⟨2186875271535295023072967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2915833695380393364097289 2186875271535295023072967)
    ·
      refine ⟨3280312907302942534609451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2186875271535295023072967 3280312907302942534609451)
      ·
        refine ⟨4920469360954413801914177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3280312907302942534609451 4920469360954413801914177)
        ·
          refine ⟨3690352020715810351435633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4920469360954413801914177 3690352020715810351435633)
          ·
            refine ⟨2767764015536857763576725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3690352020715810351435633 2767764015536857763576725)
            ·
              refine ⟨129738938228290207667659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 2767764015536857763576725 129738938228290207667659)
              ·
                refine ⟨194608407342435311501489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 129738938228290207667659 194608407342435311501489)
                ·
                  refine ⟨145956305506826483626117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 194608407342435311501489 145956305506826483626117)
                  ·
                    refine ⟨27366807282529965679897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 145956305506826483626117 27366807282529965679897)
                    ·
                      rfl

theorem cell22_79945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 6, 1, 2, 4].length) (baseStart_79945 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_79945 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_79945 prefixEnd_79945 := by exact prefixLift 79945
  have htrace : WordTrace (prefixWord ++ tailWord_79945) baseStart_79945 baseEnd_79945 := by
    simpa [prefixWord, tailWord_79945, baseEnd_79945] using wordTrace_append hprefix tailTrace_79945
  have hstable : (prefixWord ++ tailWord_79945).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_79945).length < 2 ^ (prefixWord ++ tailWord_79945).sum := by decide
  have hdescent : baseEnd_79945 < baseStart_79945 := by decide
  rcases family_descends (prefixWord ++ tailWord_79945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_79964 : List Nat := [2, 2, 4, 1, 1, 3, 2, 2, 2, 3]
def baseStart_79964 : Nat := 118140960795 + 79964 * 2 ^ 59
def prefixEnd_79964 : Nat := 4983230072969 + 3 ^ 40 * 79964 * 2
def baseEnd_79964 : Nat := 27373311370820249454839

theorem tailTrace_79964 : CollatzResearch.WordTrace tailWord_79964 prefixEnd_79964 27373311370820249454839 := by
  unfold tailWord_79964
  simp only [CollatzResearch.WordTrace]
  refine ⟨1458263341155779804519473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1944351121541039739359297 1458263341155779804519473)
  ·
    refine ⟨1093697505866834853389605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1458263341155779804519473 1093697505866834853389605)
    ·
      refine ⟨205068282350031535010551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1093697505866834853389605 205068282350031535010551)
      ·
        refine ⟨307602423525047302515827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 205068282350031535010551 307602423525047302515827)
        ·
          refine ⟨461403635287570953773741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 307602423525047302515827 461403635287570953773741)
          ·
            refine ⟨173026363232839107665153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 461403635287570953773741 173026363232839107665153)
            ·
              refine ⟨129769772424629330748865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 173026363232839107665153 129769772424629330748865)
              ·
                refine ⟨97327329318471998061649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 129769772424629330748865 97327329318471998061649)
                ·
                  refine ⟨72995496988853998546237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 97327329318471998061649 72995496988853998546237)
                  ·
                    refine ⟨27373311370820249454839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 72995496988853998546237 27373311370820249454839)
                    ·
                      rfl

theorem cell22_79964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 2, 2, 2, 3].length) (baseStart_79964 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_79964 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_79964 prefixEnd_79964 := by exact prefixLift 79964
  have htrace : WordTrace (prefixWord ++ tailWord_79964) baseStart_79964 baseEnd_79964 := by
    simpa [prefixWord, tailWord_79964, baseEnd_79964] using wordTrace_append hprefix tailTrace_79964
  have hstable : (prefixWord ++ tailWord_79964).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_79964).length < 2 ^ (prefixWord ++ tailWord_79964).sum := by decide
  have hdescent : baseEnd_79964 < baseStart_79964 := by decide
  rcases family_descends (prefixWord ++ tailWord_79964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_80009 : List Nat := [1, 2, 1, 1, 4, 2, 4, 3, 1, 3]
def baseStart_80009 : Nat := 118140960795 + 80009 * 2 ^ 59
def prefixEnd_80009 : Nat := 4983230072969 + 3 ^ 40 * 80009 * 2
def baseEnd_80009 : Nat := 27388715790455132079701

theorem tailTrace_80009 : CollatzResearch.WordTrace tailWord_80009 prefixEnd_80009 27388715790455132079701 := by
  unfold tailWord_80009
  simp only [CollatzResearch.WordTrace]
  refine ⟨2918167967148532294427081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1945445311432354862951387 2918167967148532294427081)
  ·
    refine ⟨2188625975361399220820311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2918167967148532294427081 2188625975361399220820311)
    ·
      refine ⟨3282938963042098831230467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2188625975361399220820311 3282938963042098831230467)
      ·
        refine ⟨4924408444563148246845701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3282938963042098831230467 4924408444563148246845701)
        ·
          refine ⟨923326583355590296283569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4924408444563148246845701 923326583355590296283569)
          ·
            refine ⟨692494937516692722212677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 923326583355590296283569 692494937516692722212677)
            ·
              refine ⟨129842800784379885414877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 692494937516692722212677 129842800784379885414877)
              ·
                refine ⟨48691050294142457030579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 129842800784379885414877 48691050294142457030579)
                ·
                  refine ⟨73036575441213685545869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48691050294142457030579 73036575441213685545869)
                  ·
                    refine ⟨27388715790455132079701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 73036575441213685545869 27388715790455132079701)
                    ·
                      rfl

theorem cell22_80009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 4, 3, 1, 3].length) (baseStart_80009 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_80009 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_80009 prefixEnd_80009 := by exact prefixLift 80009
  have htrace : WordTrace (prefixWord ++ tailWord_80009) baseStart_80009 baseEnd_80009 := by
    simpa [prefixWord, tailWord_80009, baseEnd_80009] using wordTrace_append hprefix tailTrace_80009
  have hstable : (prefixWord ++ tailWord_80009).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80009).length < 2 ^ (prefixWord ++ tailWord_80009).sum := by decide
  have hdescent : baseEnd_80009 < baseStart_80009 := by decide
  rcases family_descends (prefixWord ++ tailWord_80009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_80050 : List Nat := [3, 2, 1, 1, 1, 3, 1, 4, 6]
def baseStart_80050 : Nat := 118140960795 + 80050 * 2 ^ 59
def prefixEnd_80050 : Nat := 4983230072969 + 3 ^ 40 * 80050 * 2
def baseEnd_80050 : Nat := 9134250309448230601525

theorem tailTrace_80050 : CollatzResearch.WordTrace tailWord_80050 prefixEnd_80050 9134250309448230601525 := by
  unfold tailWord_80050
  simp only [CollatzResearch.WordTrace]
  refine ⟨729915839999999074167401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1946442239999997531113069 729915839999999074167401)
  ·
    refine ⟨547436879999999305625551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 729915839999999074167401 547436879999999305625551)
    ·
      refine ⟨821155319999998958438327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 547436879999999305625551 821155319999998958438327)
      ·
        refine ⟨1231732979999998437657491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 821155319999998958438327 1231732979999998437657491)
        ·
          refine ⟨1847599469999997656486237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1231732979999998437657491 1847599469999997656486237)
          ·
            refine ⟨692849801249999121182339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1847599469999997656486237 692849801249999121182339)
            ·
              refine ⟨1039274701874998681773509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 692849801249999121182339 1039274701874998681773509)
              ·
                refine ⟨194864006601562252832533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1039274701874998681773509 194864006601562252832533)
                ·
                  refine ⟨9134250309448230601525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 194864006601562252832533 9134250309448230601525)
                  ·
                    rfl

theorem cell22_80050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 4, 6].length) (baseStart_80050 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_80050 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_80050 prefixEnd_80050 := by exact prefixLift 80050
  have htrace : WordTrace (prefixWord ++ tailWord_80050) baseStart_80050 baseEnd_80050 := by
    simpa [prefixWord, tailWord_80050, baseEnd_80050] using wordTrace_append hprefix tailTrace_80050
  have hstable : (prefixWord ++ tailWord_80050).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80050).length < 2 ^ (prefixWord ++ tailWord_80050).sum := by decide
  have hdescent : baseEnd_80050 < baseStart_80050 := by decide
  rcases family_descends (prefixWord ++ tailWord_80050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_80114 : List Nat := [3, 2, 1, 3, 2, 2, 2, 1, 2, 4]
def baseStart_80114 : Nat := 118140960795 + 80114 * 2 ^ 59
def prefixEnd_80114 : Nat := 4983230072969 + 3 ^ 40 * 80114 * 2
def baseEnd_80114 : Nat := 27424659436269858204379

theorem tailTrace_80114 : CollatzResearch.WordTrace tailWord_80114 prefixEnd_80114 27424659436269858204379 := by
  unfold tailWord_80114
  simp only [CollatzResearch.WordTrace]
  refine ⟨730499407942033806749849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1947998421178756817999597 730499407942033806749849)
  ·
    refine ⟨547874555956525355062387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 730499407942033806749849 547874555956525355062387)
    ·
      refine ⟨821811833934788032593581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 547874555956525355062387 821811833934788032593581)
      ·
        refine ⟨308179437725545512222593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 821811833934788032593581 308179437725545512222593)
        ·
          refine ⟨231134578294159134166945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 308179437725545512222593 231134578294159134166945)
          ·
            refine ⟨173350933720619350625209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 231134578294159134166945 173350933720619350625209)
            ·
              refine ⟨130013200290464512968907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 173350933720619350625209 130013200290464512968907)
              ·
                refine ⟨195019800435696769453361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 130013200290464512968907 195019800435696769453361)
                ·
                  refine ⟨146264850326772577090021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 195019800435696769453361 146264850326772577090021)
                  ·
                    refine ⟨27424659436269858204379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 146264850326772577090021 27424659436269858204379)
                    ·
                      rfl

theorem cell22_80114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 2, 1, 2, 4].length) (baseStart_80114 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_80114 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_80114 prefixEnd_80114 := by exact prefixLift 80114
  have htrace : WordTrace (prefixWord ++ tailWord_80114) baseStart_80114 baseEnd_80114 := by
    simpa [prefixWord, tailWord_80114, baseEnd_80114] using wordTrace_append hprefix tailTrace_80114
  have hstable : (prefixWord ++ tailWord_80114).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80114).length < 2 ^ (prefixWord ++ tailWord_80114).sum := by decide
  have hdescent : baseEnd_80114 < baseStart_80114 := by decide
  rcases family_descends (prefixWord ++ tailWord_80114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
