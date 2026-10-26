import V185TrunkScan23Chunk1337

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_7923696 : List Nat := [2, 1, 1, 1, 3, 2, 2, 1, 10]
def baseStart_7923696 : Nat := 118140960795 + 7923696 * 2 ^ 59
def prefixEnd_7923696 : Nat := 4983230072969 + 3 ^ 40 * 7923696 * 2
def baseEnd_7923696 : Nat := 452073845345348415184399

theorem tailTrace_7923696 : CollatzResearch.WordTrace tailWord_7923696 prefixEnd_7923696 452073845345348415184399 := by
  unfold tailWord_7923696
  simp only [CollatzResearch.WordTrace]
  refine ⟨144500467750905063191707471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192667290334540084255609961 144500467750905063191707471)
  ·
    refine ⟨216750701626357594787561207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144500467750905063191707471 216750701626357594787561207)
    ·
      refine ⟨325126052439536392181341811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216750701626357594787561207 325126052439536392181341811)
      ·
        refine ⟨487689078659304588272012717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 325126052439536392181341811 487689078659304588272012717)
        ·
          refine ⟨182883404497239220602004769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 487689078659304588272012717 182883404497239220602004769)
          ·
            refine ⟨137162553372929415451503577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 182883404497239220602004769 137162553372929415451503577)
            ·
              refine ⟨102871915029697061588627683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137162553372929415451503577 102871915029697061588627683)
              ·
                refine ⟨154307872544545592382941525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102871915029697061588627683 154307872544545592382941525)
                ·
                  refine ⟨452073845345348415184399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 154307872544545592382941525 452073845345348415184399)
                  ·
                    rfl

theorem cell23_7923696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 1, 10].length) (baseStart_7923696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7923696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7923696 prefixEnd_7923696 := by exact prefixLift 7923696
  have htrace : WordTrace (prefixWord ++ tailWord_7923696) baseStart_7923696 baseEnd_7923696 := by
    simpa [prefixWord, tailWord_7923696, baseEnd_7923696] using wordTrace_append hprefix tailTrace_7923696
  have hstable : (prefixWord ++ tailWord_7923696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7923696).length < 2 ^ (prefixWord ++ tailWord_7923696).sum := by decide
  have hdescent : baseEnd_7923696 < baseStart_7923696 := by decide
  rcases family_descends (prefixWord ++ tailWord_7923696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7923717 : List Nat := [1, 3, 1, 1, 2, 5, 1, 4, 1, 4]
def baseStart_7923717 : Nat := 118140960795 + 7923717 * 2 ^ 59
def prefixEnd_7923717 : Nat := 4983230072969 + 3 ^ 40 * 7923717 * 2
def baseEnd_7923717 : Nat := 1356225130400626718165665

theorem tailTrace_7923717 : CollatzResearch.WordTrace tailWord_7923717 prefixEnd_7923717 1356225130400626718165665 := by
  unfold tailWord_7923717
  simp only [CollatzResearch.WordTrace]
  refine ⟨289001701434734046969929405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192667800956489364646619603 289001701434734046969929405)
  ·
    refine ⟨108375638038025267613723527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 289001701434734046969929405 108375638038025267613723527)
    ·
      refine ⟨162563457057037901420585291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108375638038025267613723527 162563457057037901420585291)
      ·
        refine ⟨243845185585556852130877937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162563457057037901420585291 243845185585556852130877937)
        ·
          refine ⟨182883889189167639098158453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 243845185585556852130877937 182883889189167639098158453)
          ·
            refine ⟨17145364611484466165452355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 182883889189167639098158453 17145364611484466165452355)
            ·
              refine ⟨25718046917226699248178533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17145364611484466165452355 25718046917226699248178533)
              ·
                refine ⟨4822133796980006109033475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25718046917226699248178533 4822133796980006109033475)
                ·
                  refine ⟨7233200695470009163550213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4822133796980006109033475 7233200695470009163550213)
                  ·
                    refine ⟨1356225130400626718165665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7233200695470009163550213 1356225130400626718165665)
                    ·
                      rfl

theorem cell23_7923717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 1, 4, 1, 4].length) (baseStart_7923717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7923717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7923717 prefixEnd_7923717 := by exact prefixLift 7923717
  have htrace : WordTrace (prefixWord ++ tailWord_7923717) baseStart_7923717 baseEnd_7923717 := by
    simpa [prefixWord, tailWord_7923717, baseEnd_7923717] using wordTrace_append hprefix tailTrace_7923717
  have hstable : (prefixWord ++ tailWord_7923717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7923717).length < 2 ^ (prefixWord ++ tailWord_7923717).sum := by decide
  have hdescent : baseEnd_7923717 < baseStart_7923717 := by decide
  rcases family_descends (prefixWord ++ tailWord_7923717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7923743 : List Nat := [1, 1, 2, 4, 1, 2, 1, 3, 3, 5]
def baseStart_7923743 : Nat := 118140960795 + 7923743 * 2 ^ 59
def prefixEnd_7923743 : Nat := 4983230072969 + 3 ^ 40 * 7923743 * 2
def baseEnd_7923743 : Nat := 1356229580566299017590625

theorem tailTrace_7923743 : CollatzResearch.WordTrace tailWord_7923743 prefixEnd_7923743 1356229580566299017590625 := by
  unfold tailWord_7923743
  simp only [CollatzResearch.WordTrace]
  refine ⟨289002649732639853410375883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192668433155093235606917255 289002649732639853410375883)
  ·
    refine ⟨433503974598959780115563825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289002649732639853410375883 433503974598959780115563825)
    ·
      refine ⟨325127980949219835086672869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 433503974598959780115563825 325127980949219835086672869)
      ·
        refine ⟨60961496427978719078751163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 325127980949219835086672869 60961496427978719078751163)
        ·
          refine ⟨91442244641968078618126745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60961496427978719078751163 91442244641968078618126745)
          ·
            refine ⟨68581683481476058963595059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91442244641968078618126745 68581683481476058963595059)
            ·
              refine ⟨102872525222214088445392589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68581683481476058963595059 102872525222214088445392589)
              ·
                refine ⟨38577196958330283167022221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 102872525222214088445392589 38577196958330283167022221)
                ·
                  refine ⟨14466448859373856187633333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38577196958330283167022221 14466448859373856187633333)
                  ·
                    refine ⟨1356229580566299017590625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14466448859373856187633333 1356229580566299017590625)
                    ·
                      rfl

theorem cell23_7923743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 3, 3, 5].length) (baseStart_7923743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7923743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7923743 prefixEnd_7923743 := by exact prefixLift 7923743
  have htrace : WordTrace (prefixWord ++ tailWord_7923743) baseStart_7923743 baseEnd_7923743 := by
    simpa [prefixWord, tailWord_7923743, baseEnd_7923743] using wordTrace_append hprefix tailTrace_7923743
  have hstable : (prefixWord ++ tailWord_7923743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7923743).length < 2 ^ (prefixWord ++ tailWord_7923743).sum := by decide
  have hdescent : baseEnd_7923743 < baseStart_7923743 := by decide
  rcases family_descends (prefixWord ++ tailWord_7923743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7923751 : List Nat := [1, 1, 7, 1, 2, 1, 2, 3, 1, 4]
def baseStart_7923751 : Nat := 118140960795 + 7923751 * 2 ^ 59
def prefixEnd_7923751 : Nat := 4983230072969 + 3 ^ 40 * 7923751 * 2
def baseEnd_7923751 : Nat := 1356230949848044340490613

theorem tailTrace_7923751 : CollatzResearch.WordTrace tailWord_7923751 prefixEnd_7923751 1356230949848044340490613 := by
  unfold tailWord_7923751
  simp only [CollatzResearch.WordTrace]
  refine ⟨289002941516610870776667107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192668627677740580517778071 289002941516610870776667107)
  ·
    refine ⟨433504412274916306165000661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289002941516610870776667107 433504412274916306165000661)
    ·
      refine ⟨10160259662693350925742203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 433504412274916306165000661 10160259662693350925742203)
      ·
        refine ⟨15240389494040026388613305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10160259662693350925742203 15240389494040026388613305)
        ·
          refine ⟨11430292120530019791459979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15240389494040026388613305 11430292120530019791459979)
          ·
            refine ⟨17145438180795029687189969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11430292120530019791459979 17145438180795029687189969)
            ·
              refine ⟨12859078635596272265392477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17145438180795029687189969 12859078635596272265392477)
              ·
                refine ⟨4822154488348602099522179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12859078635596272265392477 4822154488348602099522179)
                ·
                  refine ⟨7233231732522903149283269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4822154488348602099522179 7233231732522903149283269)
                  ·
                    refine ⟨1356230949848044340490613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7233231732522903149283269 1356230949848044340490613)
                    ·
                      rfl

theorem cell23_7923751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 2, 3, 1, 4].length) (baseStart_7923751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7923751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7923751 prefixEnd_7923751 := by exact prefixLift 7923751
  have htrace : WordTrace (prefixWord ++ tailWord_7923751) baseStart_7923751 baseEnd_7923751 := by
    simpa [prefixWord, tailWord_7923751, baseEnd_7923751] using wordTrace_append hprefix tailTrace_7923751
  have hstable : (prefixWord ++ tailWord_7923751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7923751).length < 2 ^ (prefixWord ++ tailWord_7923751).sum := by decide
  have hdescent : baseEnd_7923751 < baseStart_7923751 := by decide
  rcases family_descends (prefixWord ++ tailWord_7923751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7923760 : List Nat := [2, 1, 1, 1, 2, 6, 1, 3, 1, 5]
def baseStart_7923760 : Nat := 118140960795 + 7923760 * 2 ^ 59
def prefixEnd_7923760 : Nat := 4983230072969 + 3 ^ 40 * 7923760 * 2
def baseEnd_7923760 : Nat := 1356232490290007828753099

theorem tailTrace_7923760 : CollatzResearch.WordTrace tailWord_7923760 prefixEnd_7923760 1356232490290007828753099 := by
  unfold tailWord_7923760
  simp only [CollatzResearch.WordTrace]
  refine ⟨144501634886789132656872367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192668846515718843542496489 144501634886789132656872367)
  ·
    refine ⟨216752452330183698985308551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144501634886789132656872367 216752452330183698985308551)
    ·
      refine ⟨325128678495275548477962827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216752452330183698985308551 325128678495275548477962827)
      ·
        refine ⟨487693017742913322716944241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 325128678495275548477962827 487693017742913322716944241)
        ·
          refine ⟨365769763307184992037708181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 487693017742913322716944241 365769763307184992037708181)
          ·
            refine ⟨17145457655024296501767571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 365769763307184992037708181 17145457655024296501767571)
            ·
              refine ⟨25718186482536444752651357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17145457655024296501767571 25718186482536444752651357)
              ·
                refine ⟨9644319930951166782244259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25718186482536444752651357 9644319930951166782244259)
                ·
                  refine ⟨14466479896426750173366389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9644319930951166782244259 14466479896426750173366389)
                  ·
                    refine ⟨1356232490290007828753099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14466479896426750173366389 1356232490290007828753099)
                    ·
                      rfl

theorem cell23_7923760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 1, 3, 1, 5].length) (baseStart_7923760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7923760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7923760 prefixEnd_7923760 := by exact prefixLift 7923760
  have htrace : WordTrace (prefixWord ++ tailWord_7923760) baseStart_7923760 baseEnd_7923760 := by
    simpa [prefixWord, tailWord_7923760, baseEnd_7923760] using wordTrace_append hprefix tailTrace_7923760
  have hstable : (prefixWord ++ tailWord_7923760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7923760).length < 2 ^ (prefixWord ++ tailWord_7923760).sum := by decide
  have hdescent : baseEnd_7923760 < baseStart_7923760 := by decide
  rcases family_descends (prefixWord ++ tailWord_7923760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7923764 : List Nat := [2, 5, 1, 2, 2, 2, 1, 2, 6]
def baseStart_7923764 : Nat := 118140960795 + 7923764 * 2 ^ 59
def prefixEnd_7923764 : Nat := 4983230072969 + 3 ^ 40 * 7923764 * 2
def baseEnd_7923764 : Nat := 452077724976960163401031

theorem tailTrace_7923764 : CollatzResearch.WordTrace tailWord_7923764 prefixEnd_7923764 452077724976960163401031 := by
  unfold tailWord_7923764
  simp only [CollatzResearch.WordTrace]
  refine ⟨144501707832781886998445173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192668943777042515997926897 144501707832781886998445173)
  ·
    refine ⟨13547035109323301906104235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 144501707832781886998445173 13547035109323301906104235)
    ·
      refine ⟨20320552663984952859156353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13547035109323301906104235 20320552663984952859156353)
      ·
        refine ⟨15240414497988714644367265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20320552663984952859156353 15240414497988714644367265)
        ·
          refine ⟨11430310873491535983275449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15240414497988714644367265 11430310873491535983275449)
          ·
            refine ⟨8572733155118651987456587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11430310873491535983275449 8572733155118651987456587)
            ·
              refine ⟨12859099732677977981184881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8572733155118651987456587 12859099732677977981184881)
              ·
                refine ⟨9644324799508483485888661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12859099732677977981184881 9644324799508483485888661)
                ·
                  refine ⟨452077724976960163401031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9644324799508483485888661 452077724976960163401031)
                  ·
                    rfl

theorem cell23_7923764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 2, 1, 2, 6].length) (baseStart_7923764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7923764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7923764 prefixEnd_7923764 := by exact prefixLift 7923764
  have htrace : WordTrace (prefixWord ++ tailWord_7923764) baseStart_7923764 baseEnd_7923764 := by
    simpa [prefixWord, tailWord_7923764, baseEnd_7923764] using wordTrace_append hprefix tailTrace_7923764
  have hstable : (prefixWord ++ tailWord_7923764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7923764).length < 2 ^ (prefixWord ++ tailWord_7923764).sum := by decide
  have hdescent : baseEnd_7923764 < baseStart_7923764 := by decide
  rcases family_descends (prefixWord ++ tailWord_7923764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7923790 : List Nat := [4, 1, 1, 1, 1, 4, 3, 1, 1, 6]
def baseStart_7923790 : Nat := 118140960795 + 7923790 * 2 ^ 59
def prefixEnd_7923790 : Nat := 4983230072969 + 3 ^ 40 * 7923790 * 2
def baseEnd_7923790 : Nat := 1356237625096552789628053

theorem tailTrace_7923790 : CollatzResearch.WordTrace tailWord_7923790 prefixEnd_7923790 1356237625096552789628053 := by
  unfold tailWord_7923790
  simp only [CollatzResearch.WordTrace]
  refine ⟨36125545495433697554667103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 192669575975646386958224549 36125545495433697554667103)
  ·
    refine ⟨54188318243150546332000655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36125545495433697554667103 54188318243150546332000655)
    ·
      refine ⟨81282477364725819498000983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54188318243150546332000655 81282477364725819498000983)
      ·
        refine ⟨121923716047088729247001475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81282477364725819498000983 121923716047088729247001475)
        ·
          refine ⟨182885574070633093870502213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121923716047088729247001475 182885574070633093870502213)
          ·
            refine ⟨34291045138243705100719165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 182885574070633093870502213 34291045138243705100719165)
            ·
              refine ⟨12859141926841389412769687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34291045138243705100719165 12859141926841389412769687)
              ·
                refine ⟨19288712890262084119154531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12859141926841389412769687 19288712890262084119154531)
                ·
                  refine ⟨28933069335393126178731797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19288712890262084119154531 28933069335393126178731797)
                  ·
                    refine ⟨1356237625096552789628053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28933069335393126178731797 1356237625096552789628053)
                    ·
                      rfl

theorem cell23_7923790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 3, 1, 1, 6].length) (baseStart_7923790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7923790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7923790 prefixEnd_7923790 := by exact prefixLift 7923790
  have htrace : WordTrace (prefixWord ++ tailWord_7923790) baseStart_7923790 baseEnd_7923790 := by
    simpa [prefixWord, tailWord_7923790, baseEnd_7923790] using wordTrace_append hprefix tailTrace_7923790
  have hstable : (prefixWord ++ tailWord_7923790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7923790).length < 2 ^ (prefixWord ++ tailWord_7923790).sum := by decide
  have hdescent : baseEnd_7923790 < baseStart_7923790 := by decide
  rcases family_descends (prefixWord ++ tailWord_7923790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7923797 : List Nat := [1, 3, 2, 2, 1, 4, 2, 2, 1, 1, 4]
def baseStart_7923797 : Nat := 118140960795 + 7923797 * 2 ^ 59
def prefixEnd_7923797 : Nat := 4983230072969 + 3 ^ 40 * 7923797 * 2
def baseEnd_7923797 : Nat := 4068716469654239841496627

theorem tailTrace_7923797 : CollatzResearch.WordTrace tailWord_7923797 prefixEnd_7923797 4068716469654239841496627 := by
  unfold tailWord_7923797
  simp only [CollatzResearch.WordTrace]
  refine ⟨289004619274444220632841645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192669746182962813755227763 289004619274444220632841645)
  ·
    refine ⟨108376732227916582737315617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 289004619274444220632841645 108376732227916582737315617)
    ·
      refine ⟨81282549170937437052986713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108376732227916582737315617 81282549170937437052986713)
      ·
        refine ⟨60961911878203077789740035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81282549170937437052986713 60961911878203077789740035)
        ·
          refine ⟨91442867817304616684610053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60961911878203077789740035 91442867817304616684610053)
          ·
            refine ⟨17145537715744615628364385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 91442867817304616684610053 17145537715744615628364385)
            ·
              refine ⟨12859153286808461721273289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17145537715744615628364385 12859153286808461721273289)
              ·
                refine ⟨9644364965106346290954967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12859153286808461721273289 9644364965106346290954967)
                ·
                  refine ⟨14466547447659519436432451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9644364965106346290954967 14466547447659519436432451)
                  ·
                    refine ⟨21699821171489279154648677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14466547447659519436432451 21699821171489279154648677)
                    ·
                      refine ⟨4068716469654239841496627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21699821171489279154648677 4068716469654239841496627)
                      ·
                        rfl

theorem cell23_7923797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 2, 2, 1, 1, 4].length) (baseStart_7923797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7923797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7923797 prefixEnd_7923797 := by exact prefixLift 7923797
  have htrace : WordTrace (prefixWord ++ tailWord_7923797) baseStart_7923797 baseEnd_7923797 := by
    simpa [prefixWord, tailWord_7923797, baseEnd_7923797] using wordTrace_append hprefix tailTrace_7923797
  have hstable : (prefixWord ++ tailWord_7923797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7923797).length < 2 ^ (prefixWord ++ tailWord_7923797).sum := by decide
  have hdescent : baseEnd_7923797 < baseStart_7923797 := by decide
  rcases family_descends (prefixWord ++ tailWord_7923797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7923840 : List Nat := [2, 1, 1, 2, 1, 3, 1, 1, 2, 7, 2]
def baseStart_7923840 : Nat := 118140960795 + 7923840 * 2 ^ 59
def prefixEnd_7923840 : Nat := 4983230072969 + 3 ^ 40 * 7923840 * 2
def baseEnd_7923840 : Nat := 4068738549322383173258929

theorem tailTrace_7923840 : CollatzResearch.WordTrace tailWord_7923840 prefixEnd_7923840 4068738549322383173258929 := by
  unfold tailWord_7923840
  simp only [CollatzResearch.WordTrace]
  refine ⟨144503093806644219488328487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192670791742192292651104649 144503093806644219488328487)
  ·
    refine ⟨216754640709966329232492731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144503093806644219488328487 216754640709966329232492731)
    ·
      refine ⟨325131961064949493848739097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216754640709966329232492731 325131961064949493848739097)
      ·
        refine ⟨243848970798712120386554323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 325131961064949493848739097 243848970798712120386554323)
        ·
          refine ⟨365773456198068180579831485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 243848970798712120386554323 365773456198068180579831485)
          ·
            refine ⟨137165046074275567717436807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 365773456198068180579831485 137165046074275567717436807)
            ·
              refine ⟨205747569111413351576155211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137165046074275567717436807 205747569111413351576155211)
              ·
                refine ⟨308621353667120027364232817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 205747569111413351576155211 308621353667120027364232817)
                ·
                  refine ⟨231466015250340020523174613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 308621353667120027364232817 231466015250340020523174613)
                  ·
                    refine ⟨5424984732429844231011905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 231466015250340020523174613 5424984732429844231011905)
                    ·
                      refine ⟨4068738549322383173258929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5424984732429844231011905 4068738549322383173258929)
                      ·
                        rfl

theorem cell23_7923840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 1, 2, 7, 2].length) (baseStart_7923840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7923840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7923840 prefixEnd_7923840 := by exact prefixLift 7923840
  have htrace : WordTrace (prefixWord ++ tailWord_7923840) baseStart_7923840 baseEnd_7923840 := by
    simpa [prefixWord, tailWord_7923840, baseEnd_7923840] using wordTrace_append hprefix tailTrace_7923840
  have hstable : (prefixWord ++ tailWord_7923840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7923840).length < 2 ^ (prefixWord ++ tailWord_7923840).sum := by decide
  have hdescent : baseEnd_7923840 < baseStart_7923840 := by decide
  rcases family_descends (prefixWord ++ tailWord_7923840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7923841 : List Nat := [1, 2, 4, 2, 3, 2, 2, 1, 2, 4]
def baseStart_7923841 : Nat := 118140960795 + 7923841 * 2 ^ 59
def prefixEnd_7923841 : Nat := 4983230072969 + 3 ^ 40 * 7923841 * 2
def baseEnd_7923841 : Nat := 1356246354267679223115475

theorem tailTrace_7923841 : CollatzResearch.WordTrace tailWord_7923841 prefixEnd_7923841 1356246354267679223115475 := by
  unfold tailWord_7923841
  simp only [CollatzResearch.WordTrace]
  refine ⟨289006224086284816147443377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192670816057523210764962251 289006224086284816147443377)
  ·
    refine ⟨216754668064713612110582533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 289006224086284816147443377 216754668064713612110582533)
    ·
      refine ⟨40641500262133802270734225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 216754668064713612110582533 40641500262133802270734225)
      ·
        refine ⟨30481125196600351703050669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40641500262133802270734225 30481125196600351703050669)
        ·
          refine ⟨11430421948725131888644001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30481125196600351703050669 11430421948725131888644001)
          ·
            refine ⟨8572816461543848916483001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11430421948725131888644001 8572816461543848916483001)
            ·
              refine ⟨6429612346157886687362251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8572816461543848916483001 6429612346157886687362251)
              ·
                refine ⟨9644418519236830031043377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6429612346157886687362251 9644418519236830031043377)
                ·
                  refine ⟨7233313889427622523282533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9644418519236830031043377 7233313889427622523282533)
                  ·
                    refine ⟨1356246354267679223115475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7233313889427622523282533 1356246354267679223115475)
                    ·
                      rfl

theorem cell23_7923841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 2, 2, 1, 2, 4].length) (baseStart_7923841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7923841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7923841 prefixEnd_7923841 := by exact prefixLift 7923841
  have htrace : WordTrace (prefixWord ++ tailWord_7923841) baseStart_7923841 baseEnd_7923841 := by
    simpa [prefixWord, tailWord_7923841, baseEnd_7923841] using wordTrace_append hprefix tailTrace_7923841
  have hstable : (prefixWord ++ tailWord_7923841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7923841).length < 2 ^ (prefixWord ++ tailWord_7923841).sum := by decide
  have hdescent : baseEnd_7923841 < baseStart_7923841 := by decide
  rcases family_descends (prefixWord ++ tailWord_7923841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7923882 : List Nat := [3, 1, 5, 1, 2, 2, 2, 2, 1, 2, 2]
def baseStart_7923882 : Nat := 118140960795 + 7923882 * 2 ^ 59
def prefixEnd_7923882 : Nat := 4983230072969 + 3 ^ 40 * 7923882 * 2
def baseEnd_7923882 : Nat := 4068760115509872008933737

theorem tailTrace_7923882 : CollatzResearch.WordTrace tailWord_7923882 prefixEnd_7923882 4068760115509872008933737 := by
  unfold tailWord_7923882
  simp only [CollatzResearch.WordTrace]
  refine ⟨72251929869784070037421475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192671812986090853433123933 72251929869784070037421475)
  ·
    refine ⟨108377894804676105056132213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72251929869784070037421475 108377894804676105056132213)
    ·
      refine ⟨10160427637938384849012395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 108377894804676105056132213 10160427637938384849012395)
      ·
        refine ⟨15240641456907577273518593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10160427637938384849012395 15240641456907577273518593)
        ·
          refine ⟨11430481092680682955138945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15240641456907577273518593 11430481092680682955138945)
          ·
            refine ⟨8572860819510512216354209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11430481092680682955138945 8572860819510512216354209)
            ·
              refine ⟨6429645614632884162265657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8572860819510512216354209 6429645614632884162265657)
              ·
                refine ⟨4822234210974663121699243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6429645614632884162265657 4822234210974663121699243)
                ·
                  refine ⟨7233351316461994682548865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4822234210974663121699243 7233351316461994682548865)
                  ·
                    refine ⟨5425013487346496011911649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7233351316461994682548865 5425013487346496011911649)
                    ·
                      refine ⟨4068760115509872008933737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5425013487346496011911649 4068760115509872008933737)
                      ·
                        rfl

theorem cell23_7923882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 2, 2, 2, 1, 2, 2].length) (baseStart_7923882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7923882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7923882 prefixEnd_7923882 := by exact prefixLift 7923882
  have htrace : WordTrace (prefixWord ++ tailWord_7923882) baseStart_7923882 baseEnd_7923882 := by
    simpa [prefixWord, tailWord_7923882, baseEnd_7923882] using wordTrace_append hprefix tailTrace_7923882
  have hstable : (prefixWord ++ tailWord_7923882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7923882).length < 2 ^ (prefixWord ++ tailWord_7923882).sum := by decide
  have hdescent : baseEnd_7923882 < baseStart_7923882 := by decide
  rcases family_descends (prefixWord ++ tailWord_7923882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7923890 : List Nat := [3, 2, 1, 1, 1, 3, 1, 1, 1, 6, 3]
def baseStart_7923890 : Nat := 118140960795 + 7923890 * 2 ^ 59
def prefixEnd_7923890 : Nat := 4983230072969 + 3 ^ 40 * 7923890 * 2
def baseEnd_7923890 : Nat := 4068764223355107977633699

theorem tailTrace_7923890 : CollatzResearch.WordTrace tailWord_7923890 prefixEnd_7923890 4068764223355107977633699 := by
  unfold tailWord_7923890
  simp only [CollatzResearch.WordTrace]
  refine ⟨72252002815776824378994281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192672007508738198343984749 72252002815776824378994281)
  ·
    refine ⟨54189002111832618284245711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72252002815776824378994281 54189002111832618284245711)
    ·
      refine ⟨81283503167748927426368567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54189002111832618284245711 81283503167748927426368567)
      ·
        refine ⟨121925254751623391139552851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81283503167748927426368567 121925254751623391139552851)
        ·
          refine ⟨182887882127435086709329277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121925254751623391139552851 182887882127435086709329277)
          ·
            refine ⟨68582955797788157515998479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 182887882127435086709329277 68582955797788157515998479)
            ·
              refine ⟨102874433696682236273997719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68582955797788157515998479 102874433696682236273997719)
              ·
                refine ⟨154311650545023354410996579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102874433696682236273997719 154311650545023354410996579)
                ·
                  refine ⟨231467475817535031616494869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 154311650545023354410996579 231467475817535031616494869)
                  ·
                    refine ⟨10850037928946954607023197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 231467475817535031616494869 10850037928946954607023197)
                    ·
                      refine ⟨4068764223355107977633699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10850037928946954607023197 4068764223355107977633699)
                      ·
                        rfl

theorem cell23_7923890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 1, 1, 6, 3].length) (baseStart_7923890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7923890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7923890 prefixEnd_7923890 := by exact prefixLift 7923890
  have htrace : WordTrace (prefixWord ++ tailWord_7923890) baseStart_7923890 baseEnd_7923890 := by
    simpa [prefixWord, tailWord_7923890, baseEnd_7923890] using wordTrace_append hprefix tailTrace_7923890
  have hstable : (prefixWord ++ tailWord_7923890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7923890).length < 2 ^ (prefixWord ++ tailWord_7923890).sum := by decide
  have hdescent : baseEnd_7923890 < baseStart_7923890 := by decide
  rcases family_descends (prefixWord ++ tailWord_7923890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7923904 : List Nat := [2, 1, 1, 2, 5, 2, 2, 1, 1, 4, 2]
def baseStart_7923904 : Nat := 118140960795 + 7923904 * 2 ^ 59
def prefixEnd_7923904 : Nat := 4983230072969 + 3 ^ 40 * 7923904 * 2
def baseEnd_7923904 : Nat := 4068771412084270922858635

theorem tailTrace_7923904 : CollatzResearch.WordTrace tailWord_7923904 prefixEnd_7923904 4068771412084270922858635 := by
  unfold tailWord_7923904
  simp only [CollatzResearch.WordTrace]
  refine ⟨144504260942528288953493383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192672347923371051937991177 144504260942528288953493383)
  ·
    refine ⟨216756391413792433430240075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144504260942528288953493383 216756391413792433430240075)
    ·
      refine ⟨325134587120688650145360113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216756391413792433430240075 325134587120688650145360113)
      ·
        refine ⟨243850940340516487609020085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 325134587120688650145360113 243850940340516487609020085)
        ·
          refine ⟨22861025656923420713345633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 243850940340516487609020085 22861025656923420713345633)
          ·
            refine ⟨17145769242692565535009225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22861025656923420713345633 17145769242692565535009225)
            ·
              refine ⟨12859326932019424151256919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17145769242692565535009225 12859326932019424151256919)
              ·
                refine ⟨19288990398029136226885379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12859326932019424151256919 19288990398029136226885379)
                ·
                  refine ⟨28933485597043704340328069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19288990398029136226885379 28933485597043704340328069)
                  ·
                    refine ⟨5425028549445694563811513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28933485597043704340328069 5425028549445694563811513)
                    ·
                      refine ⟨4068771412084270922858635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5425028549445694563811513 4068771412084270922858635)
                      ·
                        rfl

theorem cell23_7923904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 2, 1, 1, 4, 2].length) (baseStart_7923904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7923904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7923904 prefixEnd_7923904 := by exact prefixLift 7923904
  have htrace : WordTrace (prefixWord ++ tailWord_7923904) baseStart_7923904 baseEnd_7923904 := by
    simpa [prefixWord, tailWord_7923904, baseEnd_7923904] using wordTrace_append hprefix tailTrace_7923904
  have hstable : (prefixWord ++ tailWord_7923904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7923904).length < 2 ^ (prefixWord ++ tailWord_7923904).sum := by decide
  have hdescent : baseEnd_7923904 < baseStart_7923904 := by decide
  rcases family_descends (prefixWord ++ tailWord_7923904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7923925 : List Nat := [1, 3, 2, 4, 3, 1, 2, 1, 1, 3, 2]
def baseStart_7923925 : Nat := 118140960795 + 7923925 * 2 ^ 59
def prefixEnd_7923925 : Nat := 4983230072969 + 3 ^ 40 * 7923925 * 2
def baseEnd_7923925 : Nat := 4068782195178015340696039

theorem tailTrace_7923925 : CollatzResearch.WordTrace tailWord_7923925 prefixEnd_7923925 4068782195178015340696039 := by
  unfold tailWord_7923925
  simp only [CollatzResearch.WordTrace]
  refine ⟨289009287817980498493501229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192672858545320332329000819 289009287817980498493501229)
  ·
    refine ⟨108378482931742686935062961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 289009287817980498493501229 108378482931742686935062961)
    ·
      refine ⟨81283862198807015201297221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108378482931742686935062961 81283862198807015201297221)
      ·
        refine ⟨15240724162276315350243229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81283862198807015201297221 15240724162276315350243229)
        ·
          refine ⟨5715271560853618256341211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15240724162276315350243229 5715271560853618256341211)
          ·
            refine ⟨8572907341280427384511817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5715271560853618256341211 8572907341280427384511817)
            ·
              refine ⟨6429680505960320538383863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8572907341280427384511817 6429680505960320538383863)
              ·
                refine ⟨9644520758940480807575795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6429680505960320538383863 9644520758940480807575795)
                ·
                  refine ⟨14466781138410721211363693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9644520758940480807575795 14466781138410721211363693)
                  ·
                    refine ⟨5425042926904020454261385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14466781138410721211363693 5425042926904020454261385)
                    ·
                      refine ⟨4068782195178015340696039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5425042926904020454261385 4068782195178015340696039)
                      ·
                        rfl

theorem cell23_7923925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 1, 2, 1, 1, 3, 2].length) (baseStart_7923925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7923925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7923925 prefixEnd_7923925 := by exact prefixLift 7923925
  have htrace : WordTrace (prefixWord ++ tailWord_7923925) baseStart_7923925 baseEnd_7923925 := by
    simpa [prefixWord, tailWord_7923925, baseEnd_7923925] using wordTrace_append hprefix tailTrace_7923925
  have hstable : (prefixWord ++ tailWord_7923925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7923925).length < 2 ^ (prefixWord ++ tailWord_7923925).sum := by decide
  have hdescent : baseEnd_7923925 < baseStart_7923925 := by decide
  rcases family_descends (prefixWord ++ tailWord_7923925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7923940 : List Nat := [2, 3, 1, 1, 1, 2, 1, 3, 4, 5]
def baseStart_7923940 : Nat := 118140960795 + 7923940 * 2 ^ 59
def prefixEnd_7923940 : Nat := 4983230072969 + 3 ^ 40 * 7923940 * 2
def baseEnd_7923940 : Nat := 1356263299129277594002823

theorem tailTrace_7923940 : CollatzResearch.WordTrace tailWord_7923940 prefixEnd_7923940 1356263299129277594002823 := by
  unfold tailWord_7923940
  simp only [CollatzResearch.WordTrace]
  refine ⟨144504917456463078027648637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192673223275284104036864849 144504917456463078027648637)
  ·
    refine ⟨54189344046173654260368239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144504917456463078027648637 54189344046173654260368239)
    ·
      refine ⟨81284016069260481390552359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54189344046173654260368239 81284016069260481390552359)
      ·
        refine ⟨121926024103890722085828539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81284016069260481390552359 121926024103890722085828539)
        ·
          refine ⟨182889036155836083128742809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121926024103890722085828539 182889036155836083128742809)
          ·
            refine ⟨137166777116877062346557107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 182889036155836083128742809 137166777116877062346557107)
            ·
              refine ⟨205750165675315593519835661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137166777116877062346557107 205750165675315593519835661)
              ·
                refine ⟨77156312128243347569938373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 205750165675315593519835661 77156312128243347569938373)
                ·
                  refine ⟨14466808524045627669363445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 77156312128243347569938373 14466808524045627669363445)
                  ·
                    refine ⟨1356263299129277594002823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14466808524045627669363445 1356263299129277594002823)
                    ·
                      rfl

theorem cell23_7923940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 3, 4, 5].length) (baseStart_7923940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7923940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7923940 prefixEnd_7923940 := by exact prefixLift 7923940
  have htrace : WordTrace (prefixWord ++ tailWord_7923940) baseStart_7923940 baseEnd_7923940 := by
    simpa [prefixWord, tailWord_7923940, baseEnd_7923940] using wordTrace_append hprefix tailTrace_7923940
  have hstable : (prefixWord ++ tailWord_7923940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7923940).length < 2 ^ (prefixWord ++ tailWord_7923940).sum := by decide
  have hdescent : baseEnd_7923940 < baseStart_7923940 := by decide
  rcases family_descends (prefixWord ++ tailWord_7923940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7923950 : List Nat := [4, 1, 2, 1, 1, 1, 1, 3, 1, 1, 7]
def baseStart_7923950 : Nat := 118140960795 + 7923950 * 2 ^ 59
def prefixEnd_7923950 : Nat := 4983230072969 + 3 ^ 40 * 7923950 * 2
def baseEnd_7923950 : Nat := 4068795032194377742883423

theorem tailTrace_7923950 : CollatzResearch.WordTrace tailWord_7923950 prefixEnd_7923950 4068795032194377742883423 := by
  unfold tailWord_7923950
  simp only [CollatzResearch.WordTrace]
  refine ⟨36126274955361240970395163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 192673466428593285175440869 36126274955361240970395163)
  ·
    refine ⟨54189412433041861455592745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36126274955361240970395163 54189412433041861455592745)
    ·
      refine ⟨40642059324781396091694559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54189412433041861455592745 40642059324781396091694559)
      ·
        refine ⟨60963088987172094137541839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40642059324781396091694559 60963088987172094137541839)
        ·
          refine ⟨91444633480758141206312759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60963088987172094137541839 91444633480758141206312759)
          ·
            refine ⟨137166950221137211809469139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91444633480758141206312759 137166950221137211809469139)
            ·
              refine ⟨205750425331705817714203709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137166950221137211809469139 205750425331705817714203709)
              ·
                refine ⟨77156409499389681642826391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 205750425331705817714203709 77156409499389681642826391)
                ·
                  refine ⟨115734614249084522464239587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77156409499389681642826391 115734614249084522464239587)
                  ·
                    refine ⟨173601921373626783696359381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 115734614249084522464239587 173601921373626783696359381)
                    ·
                      refine ⟨4068795032194377742883423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 173601921373626783696359381 4068795032194377742883423)
                      ·
                        rfl

theorem cell23_7923950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 3, 1, 1, 7].length) (baseStart_7923950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7923950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7923950 prefixEnd_7923950 := by exact prefixLift 7923950
  have htrace : WordTrace (prefixWord ++ tailWord_7923950) baseStart_7923950 baseEnd_7923950 := by
    simpa [prefixWord, tailWord_7923950, baseEnd_7923950] using wordTrace_append hprefix tailTrace_7923950
  have hstable : (prefixWord ++ tailWord_7923950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7923950).length < 2 ^ (prefixWord ++ tailWord_7923950).sum := by decide
  have hdescent : baseEnd_7923950 < baseStart_7923950 := by decide
  rcases family_descends (prefixWord ++ tailWord_7923950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7923994 : List Nat := [3, 1, 1, 3, 4, 1, 1, 2, 2, 1, 4]
def baseStart_7923994 : Nat := 118140960795 + 7923994 * 2 ^ 59
def prefixEnd_7923994 : Nat := 4983230072969 + 3 ^ 40 * 7923994 * 2
def baseEnd_7923994 : Nat := 4068817625343175570733221

theorem tailTrace_7923994 : CollatzResearch.WordTrace tailWord_7923994 prefixEnd_7923994 4068817625343175570733221 := by
  unfold tailWord_7923994
  simp only [CollatzResearch.WordTrace]
  refine ⟨72252951113682630819440759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192674536303153682185175357 72252951113682630819440759)
  ·
    refine ⟨108379426670523946229161139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72252951113682630819440759 108379426670523946229161139)
    ·
      refine ⟨162569140005785919343741709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108379426670523946229161139 162569140005785919343741709)
      ·
        refine ⟨60963427502169719753903141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 162569140005785919343741709 60963427502169719753903141)
        ·
          refine ⟨11430642656656822453856839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60963427502169719753903141 11430642656656822453856839)
          ·
            refine ⟨17145963984985233680785259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11430642656656822453856839 17145963984985233680785259)
            ·
              refine ⟨25718945977477850521177889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17145963984985233680785259 25718945977477850521177889)
              ·
                refine ⟨19289209483108387890883417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25718945977477850521177889 19289209483108387890883417)
                ·
                  refine ⟨14466907112331290918162563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19289209483108387890883417 14466907112331290918162563)
                  ·
                    refine ⟨21700360668496936377243845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14466907112331290918162563 21700360668496936377243845)
                    ·
                      refine ⟨4068817625343175570733221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21700360668496936377243845 4068817625343175570733221)
                      ·
                        rfl

theorem cell23_7923994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 1, 2, 2, 1, 4].length) (baseStart_7923994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7923994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7923994 prefixEnd_7923994 := by exact prefixLift 7923994
  have htrace : WordTrace (prefixWord ++ tailWord_7923994) baseStart_7923994 baseEnd_7923994 := by
    simpa [prefixWord, tailWord_7923994, baseEnd_7923994] using wordTrace_append hprefix tailTrace_7923994
  have hstable : (prefixWord ++ tailWord_7923994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7923994).length < 2 ^ (prefixWord ++ tailWord_7923994).sum := by decide
  have hdescent : baseEnd_7923994 < baseStart_7923994 := by decide
  rcases family_descends (prefixWord ++ tailWord_7923994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7924004 : List Nat := [2, 3, 1, 3, 1, 2, 3, 1, 3, 4]
def baseStart_7924004 : Nat := 118140960795 + 7924004 * 2 ^ 59
def prefixEnd_7924004 : Nat := 4983230072969 + 3 ^ 40 * 7924004 * 2
def baseEnd_7924004 : Nat := 1356274253383240177202725

theorem tailTrace_7924004 : CollatzResearch.WordTrace tailWord_7924004 prefixEnd_7924004 1356274253383240177202725 := by
  unfold tailWord_7924004
  simp only [CollatzResearch.WordTrace]
  refine ⟨144506084592347147492813533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192674779456462863323751377 144506084592347147492813533)
  ·
    refine ⟨54189781722130180309805075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144506084592347147492813533 54189781722130180309805075)
    ·
      refine ⟨81284672583195270464707613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54189781722130180309805075 81284672583195270464707613)
      ·
        refine ⟨30481752218698226424265355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81284672583195270464707613 30481752218698226424265355)
        ·
          refine ⟨45722628328047339636398033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30481752218698226424265355 45722628328047339636398033)
          ·
            refine ⟨34291971246035504727298525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45722628328047339636398033 34291971246035504727298525)
            ·
              refine ⟨12859489217263314272736947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34291971246035504727298525 12859489217263314272736947)
              ·
                refine ⟨19289233825894971409105421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12859489217263314272736947 19289233825894971409105421)
                ·
                  refine ⟨7233462684710614278414533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19289233825894971409105421 7233462684710614278414533)
                  ·
                    refine ⟨1356274253383240177202725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7233462684710614278414533 1356274253383240177202725)
                    ·
                      rfl

theorem cell23_7924004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 3, 1, 3, 4].length) (baseStart_7924004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7924004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7924004 prefixEnd_7924004 := by exact prefixLift 7924004
  have htrace : WordTrace (prefixWord ++ tailWord_7924004) baseStart_7924004 baseEnd_7924004 := by
    simpa [prefixWord, tailWord_7924004, baseEnd_7924004] using wordTrace_append hprefix tailTrace_7924004
  have hstable : (prefixWord ++ tailWord_7924004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7924004).length < 2 ^ (prefixWord ++ tailWord_7924004).sum := by decide
  have hdescent : baseEnd_7924004 < baseStart_7924004 := by decide
  rcases family_descends (prefixWord ++ tailWord_7924004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7924062 : List Nat := [4, 4, 2, 1, 1, 1, 1, 1, 2, 4, 2]
def baseStart_7924062 : Nat := 118140960795 + 7924062 * 2 ^ 59
def prefixEnd_7924062 : Nat := 4983230072969 + 3 ^ 40 * 7924062 * 2
def baseEnd_7924062 : Nat := 4068852542027681304682909

theorem tailTrace_7924062 : CollatzResearch.WordTrace tailWord_7924062 prefixEnd_7924062 4068852542027681304682909 := by
  unfold tailWord_7924062
  simp only [CollatzResearch.WordTrace]
  refine ⟨36126785577310521361404805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 192676189745656113927492293 36126785577310521361404805)
  ·
    refine ⟨6773772295745722755263401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36126785577310521361404805 6773772295745722755263401)
    ·
      refine ⟨5080329221809292066447551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6773772295745722755263401 5080329221809292066447551)
      ·
        refine ⟨7620493832713938099671327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5080329221809292066447551 7620493832713938099671327)
        ·
          refine ⟨11430740749070907149506991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7620493832713938099671327 11430740749070907149506991)
          ·
            refine ⟨17146111123606360724260487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11430740749070907149506991 17146111123606360724260487)
            ·
              refine ⟨25719166685409541086390731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17146111123606360724260487 25719166685409541086390731)
              ·
                refine ⟨38578750028114311629586097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25719166685409541086390731 38578750028114311629586097)
                ·
                  refine ⟨28934062521085733722189573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38578750028114311629586097 28934062521085733722189573)
                  ·
                    refine ⟨5425136722703575072910545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28934062521085733722189573 5425136722703575072910545)
                    ·
                      refine ⟨4068852542027681304682909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5425136722703575072910545 4068852542027681304682909)
                      ·
                        rfl

theorem cell23_7924062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 1, 1, 2, 4, 2].length) (baseStart_7924062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7924062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7924062 prefixEnd_7924062 := by exact prefixLift 7924062
  have htrace : WordTrace (prefixWord ++ tailWord_7924062) baseStart_7924062 baseEnd_7924062 := by
    simpa [prefixWord, tailWord_7924062, baseEnd_7924062] using wordTrace_append hprefix tailTrace_7924062
  have hstable : (prefixWord ++ tailWord_7924062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7924062).length < 2 ^ (prefixWord ++ tailWord_7924062).sum := by decide
  have hdescent : baseEnd_7924062 < baseStart_7924062 := by decide
  rcases family_descends (prefixWord ++ tailWord_7924062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7924067 : List Nat := [1, 1, 1, 5, 2, 1, 1, 1, 5, 1, 4]
def baseStart_7924067 : Nat := 118140960795 + 7924067 * 2 ^ 59
def prefixEnd_7924067 : Nat := 4983230072969 + 3 ^ 40 * 7924067 * 2
def baseEnd_7924067 : Nat := 4068855109430953785120385

theorem tailTrace_7924067 : CollatzResearch.WordTrace tailWord_7924067 prefixEnd_7924067 4068855109430953785120385 := by
  unfold tailWord_7924067
  simp only [CollatzResearch.WordTrace]
  refine ⟨289014466983466056745170455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192676311322310704496780303 289014466983466056745170455)
  ·
    refine ⟨433521700475199085117755683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289014466983466056745170455 433521700475199085117755683)
    ·
      refine ⟨650282550712798627676633525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 433521700475199085117755683 650282550712798627676633525)
      ·
        refine ⟨60963989129324871344684393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 650282550712798627676633525 60963989129324871344684393)
        ·
          refine ⟨45722991846993653508513295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60963989129324871344684393 45722991846993653508513295)
          ·
            refine ⟨68584487770490480262769943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45722991846993653508513295 68584487770490480262769943)
            ·
              refine ⟨102876731655735720394154915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68584487770490480262769943 102876731655735720394154915)
              ·
                refine ⟨154315097483603580591232373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102876731655735720394154915 154315097483603580591232373)
                ·
                  refine ⟨14467040389087835680428035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 154315097483603580591232373 14467040389087835680428035)
                  ·
                    refine ⟨21700560583631753520642053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14467040389087835680428035 21700560583631753520642053)
                    ·
                      refine ⟨4068855109430953785120385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21700560583631753520642053 4068855109430953785120385)
                      ·
                        rfl

theorem cell23_7924067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 1, 5, 1, 4].length) (baseStart_7924067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7924067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7924067 prefixEnd_7924067 := by exact prefixLift 7924067
  have htrace : WordTrace (prefixWord ++ tailWord_7924067) baseStart_7924067 baseEnd_7924067 := by
    simpa [prefixWord, tailWord_7924067, baseEnd_7924067] using wordTrace_append hprefix tailTrace_7924067
  have hstable : (prefixWord ++ tailWord_7924067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7924067).length < 2 ^ (prefixWord ++ tailWord_7924067).sum := by decide
  have hdescent : baseEnd_7924067 < baseStart_7924067 := by decide
  rcases family_descends (prefixWord ++ tailWord_7924067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7924098 : List Nat := [3, 4, 2, 1, 2, 1, 1, 3, 1, 5]
def baseStart_7924098 : Nat := 118140960795 + 7924098 * 2 ^ 59
def prefixEnd_7924098 : Nat := 4983230072969 + 3 ^ 40 * 7924098 * 2
def baseEnd_7924098 : Nat := 1356290342443747721277581

theorem tailTrace_7924098 : CollatzResearch.WordTrace tailWord_7924098 prefixEnd_7924098 1356290342443747721277581 := by
  unfold tailWord_7924098
  simp only [CollatzResearch.WordTrace]
  refine ⟨72253899411588437259887237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192677065097569166026365965 72253899411588437259887237)
  ·
    refine ⟨13547606139672831986228857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72253899411588437259887237 13547606139672831986228857)
    ·
      refine ⟨10160704604754623989671643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13547606139672831986228857 10160704604754623989671643)
      ·
        refine ⟨15241056907131935984507465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10160704604754623989671643 15241056907131935984507465)
        ·
          refine ⟨11430792680348951988380599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15241056907131935984507465 11430792680348951988380599)
          ·
            refine ⟨17146189020523427982570899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11430792680348951988380599 17146189020523427982570899)
            ·
              refine ⟨25719283530785141973856349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17146189020523427982570899 25719283530785141973856349)
              ·
                refine ⟨9644731324044428240196131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25719283530785141973856349 9644731324044428240196131)
                ·
                  refine ⟨14467096986066642360294197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9644731324044428240196131 14467096986066642360294197)
                  ·
                    refine ⟨1356290342443747721277581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14467096986066642360294197 1356290342443747721277581)
                    ·
                      rfl

theorem cell23_7924098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 1, 3, 1, 5].length) (baseStart_7924098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7924098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7924098 prefixEnd_7924098 := by exact prefixLift 7924098
  have htrace : WordTrace (prefixWord ++ tailWord_7924098) baseStart_7924098 baseEnd_7924098 := by
    simpa [prefixWord, tailWord_7924098, baseEnd_7924098] using wordTrace_append hprefix tailTrace_7924098
  have hstable : (prefixWord ++ tailWord_7924098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7924098).length < 2 ^ (prefixWord ++ tailWord_7924098).sum := by decide
  have hdescent : baseEnd_7924098 < baseStart_7924098 := by decide
  rcases family_descends (prefixWord ++ tailWord_7924098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7924144 : List Nat := [2, 1, 1, 1, 2, 1, 1, 2, 7, 3, 2]
def baseStart_7924144 : Nat := 118140960795 + 7924144 * 2 ^ 59
def prefixEnd_7924144 : Nat := 4983230072969 + 3 ^ 40 * 7924144 * 2
def baseEnd_7924144 : Nat := 4068894647441349983857531

theorem tailTrace_7924144 : CollatzResearch.WordTrace tailWord_7924144 prefixEnd_7924144 4068894647441349983857531 := by
  unfold tailWord_7924144
  simp only [CollatzResearch.WordTrace]
  refine ⟨144508637702093549447861743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192678183602791399263815657 144508637702093549447861743)
  ·
    refine ⟨216762956553140324171792615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144508637702093549447861743 216762956553140324171792615)
    ·
      refine ⟨325144434829710486257688923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216762956553140324171792615 325144434829710486257688923)
      ·
        refine ⟨487716652244565729386533385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 325144434829710486257688923 487716652244565729386533385)
        ·
          refine ⟨365787489183424297039900039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 487716652244565729386533385 365787489183424297039900039)
          ·
            refine ⟨548681233775136445559850059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 365787489183424297039900039 548681233775136445559850059)
            ·
              refine ⟨823021850662704668339775089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 548681233775136445559850059 823021850662704668339775089)
              ·
                refine ⟨617266387997028501254831317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 823021850662704668339775089 617266387997028501254831317)
                ·
                  refine ⟨14467180968680355498160109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 617266387997028501254831317 14467180968680355498160109)
                  ·
                    refine ⟨5425192863255133311810041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14467180968680355498160109 5425192863255133311810041)
                    ·
                      refine ⟨4068894647441349983857531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5425192863255133311810041 4068894647441349983857531)
                      ·
                        rfl

theorem cell23_7924144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 7, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 7, 3, 2].length) (baseStart_7924144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7924144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7924144 prefixEnd_7924144 := by exact prefixLift 7924144
  have htrace : WordTrace (prefixWord ++ tailWord_7924144) baseStart_7924144 baseEnd_7924144 := by
    simpa [prefixWord, tailWord_7924144, baseEnd_7924144] using wordTrace_append hprefix tailTrace_7924144
  have hstable : (prefixWord ++ tailWord_7924144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7924144).length < 2 ^ (prefixWord ++ tailWord_7924144).sum := by decide
  have hdescent : baseEnd_7924144 < baseStart_7924144 := by decide
  rcases family_descends (prefixWord ++ tailWord_7924144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7924195 : List Nat := [1, 1, 1, 6, 3, 2, 1, 2, 1, 3, 2]
def baseStart_7924195 : Nat := 118140960795 + 7924195 * 2 ^ 59
def prefixEnd_7924195 : Nat := 4983230072969 + 3 ^ 40 * 7924195 * 2
def baseEnd_7924195 : Nat := 4068920834954729284319797

theorem tailTrace_7924195 : CollatzResearch.WordTrace tailWord_7924195 prefixEnd_7924195 4068920834954729284319797 := by
  unfold tailWord_7924195
  simp only [CollatzResearch.WordTrace]
  refine ⟨289019135527002334605830039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192679423684668223070553359 289019135527002334605830039)
  ·
    refine ⟨433528703290503501908745059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289019135527002334605830039 433528703290503501908745059)
    ·
      refine ⟨650293054935755252863117589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 433528703290503501908745059 650293054935755252863117589)
      ·
        refine ⟨30482486950113527477958637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 650293054935755252863117589 30482486950113527477958637)
        ·
          refine ⟨11430932606292572804234489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30482486950113527477958637 11430932606292572804234489)
          ·
            refine ⟨8573199454719429603175867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11430932606292572804234489 8573199454719429603175867)
            ·
              refine ⟨12859799182079144404763801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8573199454719429603175867 12859799182079144404763801)
              ·
                refine ⟨9644849386559358303572851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12859799182079144404763801 9644849386559358303572851)
                ·
                  refine ⟨14467274079839037455359277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9644849386559358303572851 14467274079839037455359277)
                  ·
                    refine ⟨5425227779939639045759729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14467274079839037455359277 5425227779939639045759729)
                    ·
                      refine ⟨4068920834954729284319797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5425227779939639045759729 4068920834954729284319797)
                      ·
                        rfl

theorem cell23_7924195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 2, 1, 2, 1, 3, 2].length) (baseStart_7924195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7924195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7924195 prefixEnd_7924195 := by exact prefixLift 7924195
  have htrace : WordTrace (prefixWord ++ tailWord_7924195) baseStart_7924195 baseEnd_7924195 := by
    simpa [prefixWord, tailWord_7924195, baseEnd_7924195] using wordTrace_append hprefix tailTrace_7924195
  have hstable : (prefixWord ++ tailWord_7924195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7924195).length < 2 ^ (prefixWord ++ tailWord_7924195).sum := by decide
  have hdescent : baseEnd_7924195 < baseStart_7924195 := by decide
  rcases family_descends (prefixWord ++ tailWord_7924195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7924225 : List Nat := [1, 2, 4, 1, 3, 2, 2, 2, 2, 2, 2]
def baseStart_7924225 : Nat := 118140960795 + 7924225 * 2 ^ 59
def prefixEnd_7924225 : Nat := 4983230072969 + 3 ^ 40 * 7924225 * 2
def baseEnd_7924225 : Nat := 4068936239374364166944659

theorem tailTrace_7924225 : CollatzResearch.WordTrace tailWord_7924225 prefixEnd_7924225 4068936239374364166944659 := by
  unfold tailWord_7924225
  simp only [CollatzResearch.WordTrace]
  refine ⟨289020229716893649729422129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192680153144595766486281419 289020229716893649729422129)
  ·
    refine ⟨216765172287670237297066597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 289020229716893649729422129 216765172287670237297066597)
    ·
      refine ⟨40643469803938169493199987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 216765172287670237297066597 40643469803938169493199987)
      ·
        refine ⟨60965204705907254239799981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40643469803938169493199987 60965204705907254239799981)
        ·
          refine ⟨22861951764715220339924993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60965204705907254239799981 22861951764715220339924993)
          ·
            refine ⟨17146463823536415254943745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22861951764715220339924993 17146463823536415254943745)
            ·
              refine ⟨12859847867652311441207809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17146463823536415254943745 12859847867652311441207809)
              ·
                refine ⟨9644885900739233580905857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12859847867652311441207809 9644885900739233580905857)
                ·
                  refine ⟨7233664425554425185679393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9644885900739233580905857 7233664425554425185679393)
                  ·
                    refine ⟨5425248319165818889259545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7233664425554425185679393 5425248319165818889259545)
                    ·
                      refine ⟨4068936239374364166944659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5425248319165818889259545 4068936239374364166944659)
                      ·
                        rfl

theorem cell23_7924225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 2, 2, 2, 2, 2].length) (baseStart_7924225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7924225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7924225 prefixEnd_7924225 := by exact prefixLift 7924225
  have htrace : WordTrace (prefixWord ++ tailWord_7924225) baseStart_7924225 baseEnd_7924225 := by
    simpa [prefixWord, tailWord_7924225, baseEnd_7924225] using wordTrace_append hprefix tailTrace_7924225
  have hstable : (prefixWord ++ tailWord_7924225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7924225).length < 2 ^ (prefixWord ++ tailWord_7924225).sum := by decide
  have hdescent : baseEnd_7924225 < baseStart_7924225 := by decide
  rcases family_descends (prefixWord ++ tailWord_7924225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7924276 : List Nat := [2, 5, 1, 3, 2, 1, 1, 2, 2, 2, 2]
def baseStart_7924276 : Nat := 118140960795 + 7924276 * 2 ^ 59
def prefixEnd_7924276 : Nat := 4983230072969 + 3 ^ 40 * 7924276 * 2
def baseEnd_7924276 : Nat := 4068962426887743467406925

theorem tailTrace_7924276 : CollatzResearch.WordTrace tailWord_7924276 prefixEnd_7924276 4068962426887743467406925 := by
  unfold tailWord_7924276
  simp only [CollatzResearch.WordTrace]
  refine ⟨144511044919854442719764341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192681393226472590293019121 144511044919854442719764341)
  ·
    refine ⟨13547910461236354004977907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 144511044919854442719764341 13547910461236354004977907)
    ·
      refine ⟨20321865691854531007466861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13547910461236354004977907 20321865691854531007466861)
      ·
        refine ⟨7620699634445449127800073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20321865691854531007466861 7620699634445449127800073)
        ·
          refine ⟨5715524725834086845850055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7620699634445449127800073 5715524725834086845850055)
          ·
            refine ⟨8573287088751130268775083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5715524725834086845850055 8573287088751130268775083)
            ·
              refine ⟨12859930633126695403162625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8573287088751130268775083 12859930633126695403162625)
              ·
                refine ⟨9644947974845021552371969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12859930633126695403162625 9644947974845021552371969)
                ·
                  refine ⟨7233710981133766164278977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9644947974845021552371969 7233710981133766164278977)
                  ·
                    refine ⟨5425283235850324623209233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7233710981133766164278977 5425283235850324623209233)
                    ·
                      refine ⟨4068962426887743467406925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5425283235850324623209233 4068962426887743467406925)
                      ·
                        rfl

theorem cell23_7924276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 1, 1, 2, 2, 2, 2].length) (baseStart_7924276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7924276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7924276 prefixEnd_7924276 := by exact prefixLift 7924276
  have htrace : WordTrace (prefixWord ++ tailWord_7924276) baseStart_7924276 baseEnd_7924276 := by
    simpa [prefixWord, tailWord_7924276, baseEnd_7924276] using wordTrace_append hprefix tailTrace_7924276
  have hstable : (prefixWord ++ tailWord_7924276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7924276).length < 2 ^ (prefixWord ++ tailWord_7924276).sum := by decide
  have hdescent : baseEnd_7924276 < baseStart_7924276 := by decide
  rcases family_descends (prefixWord ++ tailWord_7924276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7924281 : List Nat := [1, 2, 1, 5, 1, 1, 1, 1, 4, 4, 2]
def baseStart_7924281 : Nat := 118140960795 + 7924281 * 2 ^ 59
def prefixEnd_7924281 : Nat := 4983230072969 + 3 ^ 40 * 7924281 * 2
def baseEnd_7924281 : Nat := 4068964994291015947844401

theorem tailTrace_7924281 : CollatzResearch.WordTrace tailWord_7924281 prefixEnd_7924281 4068964994291015947844401 := by
  unfold tailWord_7924281
  simp only [CollatzResearch.WordTrace]
  refine ⟨289022272204690771293460697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192681514803127180862307131 289022272204690771293460697)
  ·
    refine ⟨216766704153518078470095523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 289022272204690771293460697 216766704153518078470095523)
    ·
      refine ⟨325150056230277117705143285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216766704153518078470095523 325150056230277117705143285)
      ·
        refine ⟨30482817771588479784857183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 325150056230277117705143285 30482817771588479784857183)
        ·
          refine ⟨45724226657382719677285775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30482817771588479784857183 45724226657382719677285775)
          ·
            refine ⟨68586339986074079515928663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45724226657382719677285775 68586339986074079515928663)
            ·
              refine ⟨102879509979111119273892995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68586339986074079515928663 102879509979111119273892995)
              ·
                refine ⟨154319264968666678910839493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102879509979111119273892995 154319264968666678910839493)
                ·
                  refine ⟨28934862181625002295782405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 154319264968666678910839493 28934862181625002295782405)
                  ·
                    refine ⟨5425286659054687930459201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28934862181625002295782405 5425286659054687930459201)
                    ·
                      refine ⟨4068964994291015947844401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5425286659054687930459201 4068964994291015947844401)
                      ·
                        rfl

theorem cell23_7924281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 1, 4, 4, 2].length) (baseStart_7924281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7924281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7924281 prefixEnd_7924281 := by exact prefixLift 7924281
  have htrace : WordTrace (prefixWord ++ tailWord_7924281) baseStart_7924281 baseEnd_7924281 := by
    simpa [prefixWord, tailWord_7924281, baseEnd_7924281] using wordTrace_append hprefix tailTrace_7924281
  have hstable : (prefixWord ++ tailWord_7924281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7924281).length < 2 ^ (prefixWord ++ tailWord_7924281).sum := by decide
  have hdescent : baseEnd_7924281 < baseStart_7924281 := by decide
  rcases family_descends (prefixWord ++ tailWord_7924281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7924342 : List Nat := [5, 1, 1, 2, 4, 1, 1, 1, 3, 4]
def baseStart_7924342 : Nat := 118140960795 + 7924342 * 2 ^ 59
def prefixEnd_7924342 : Nat := 4983230072969 + 3 ^ 40 * 7924342 * 2
def baseEnd_7924342 : Nat := 1356332105536980069727207

theorem tailTrace_7924342 : CollatzResearch.WordTrace tailWord_7924342 prefixEnd_7924342 1356332105536980069727207 := by
  unfold tailWord_7924342
  simp only [CollatzResearch.WordTrace]
  refine ⟨18064031066091861169464455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 192682998038313185807620853 18064031066091861169464455)
  ·
    refine ⟨27096046599137791754196683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18064031066091861169464455 27096046599137791754196683)
    ·
      refine ⟨40644069898706687631295025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27096046599137791754196683 40644069898706687631295025)
      ·
        refine ⟨30483052424030015723471269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40644069898706687631295025 30483052424030015723471269)
        ·
          refine ⟨5715572329505627948150863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30483052424030015723471269 5715572329505627948150863)
          ·
            refine ⟨8573358494258441922226295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5715572329505627948150863 8573358494258441922226295)
            ·
              refine ⟨12860037741387662883339443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8573358494258441922226295 12860037741387662883339443)
              ·
                refine ⟨19290056612081494325009165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12860037741387662883339443 19290056612081494325009165)
                ·
                  refine ⟨7233771229530560371878437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19290056612081494325009165 7233771229530560371878437)
                  ·
                    refine ⟨1356332105536980069727207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7233771229530560371878437 1356332105536980069727207)
                    ·
                      rfl

theorem cell23_7924342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 1, 1, 1, 3, 4].length) (baseStart_7924342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7924342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7924342 prefixEnd_7924342 := by exact prefixLift 7924342
  have htrace : WordTrace (prefixWord ++ tailWord_7924342) baseStart_7924342 baseEnd_7924342 := by
    simpa [prefixWord, tailWord_7924342, baseEnd_7924342] using wordTrace_append hprefix tailTrace_7924342
  have hstable : (prefixWord ++ tailWord_7924342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7924342).length < 2 ^ (prefixWord ++ tailWord_7924342).sum := by decide
  have hdescent : baseEnd_7924342 < baseStart_7924342 := by decide
  rcases family_descends (prefixWord ++ tailWord_7924342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7924348 : List Nat := [2, 2, 2, 1, 1, 2, 5, 1, 3, 1, 3]
def baseStart_7924348 : Nat := 118140960795 + 7924348 * 2 ^ 59
def prefixEnd_7924348 : Nat := 4983230072969 + 3 ^ 40 * 7924348 * 2
def baseEnd_7924348 : Nat := 4068999397494867185706593

theorem tailTrace_7924348 : CollatzResearch.WordTrace tailWord_7924348 prefixEnd_7924348 4068999397494867185706593 := by
  unfold tailWord_7924348
  simp only [CollatzResearch.WordTrace]
  refine ⟨144512357947724020868074849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192683143930298694490766465 144512357947724020868074849)
  ·
    refine ⟨108384268460793015651056137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144512357947724020868074849 108384268460793015651056137)
    ·
      refine ⟨81288201345594761738292103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108384268460793015651056137 81288201345594761738292103)
      ·
        refine ⟨121932302018392142607438155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81288201345594761738292103 121932302018392142607438155)
        ·
          refine ⟨182898453027588213911157233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121932302018392142607438155 182898453027588213911157233)
          ·
            refine ⟨137173839770691160433367925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 182898453027588213911157233 137173839770691160433367925)
            ·
              refine ⟨12860047478502296290628243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 137173839770691160433367925 12860047478502296290628243)
              ·
                refine ⟨19290071217753444435942365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12860047478502296290628243 19290071217753444435942365)
                ·
                  refine ⟨7233776706657541663478387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19290071217753444435942365 7233776706657541663478387)
                  ·
                    refine ⟨10850665059986312495217581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7233776706657541663478387 10850665059986312495217581)
                    ·
                      refine ⟨4068999397494867185706593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10850665059986312495217581 4068999397494867185706593)
                      ·
                        rfl

theorem cell23_7924348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 5, 1, 3, 1, 3].length) (baseStart_7924348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7924348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7924348 prefixEnd_7924348 := by exact prefixLift 7924348
  have htrace : WordTrace (prefixWord ++ tailWord_7924348) baseStart_7924348 baseEnd_7924348 := by
    simpa [prefixWord, tailWord_7924348, baseEnd_7924348] using wordTrace_append hprefix tailTrace_7924348
  have hstable : (prefixWord ++ tailWord_7924348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7924348).length < 2 ^ (prefixWord ++ tailWord_7924348).sum := by decide
  have hdescent : baseEnd_7924348 < baseStart_7924348 := by decide
  rcases family_descends (prefixWord ++ tailWord_7924348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7924381 : List Nat := [1, 4, 2, 1, 1, 1, 2, 1, 6, 4]
def baseStart_7924381 : Nat := 118140960795 + 7924381 * 2 ^ 59
def prefixEnd_7924381 : Nat := 4983230072969 + 3 ^ 40 * 7924381 * 2
def baseEnd_7924381 : Nat := 1356338780785488518864647

theorem tailTrace_7924381 : CollatzResearch.WordTrace tailWord_7924381 prefixEnd_7924381 1356338780785488518864647 := by
  unfold tailWord_7924381
  simp only [CollatzResearch.WordTrace]
  refine ⟨289025919504328488372100997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192683946336218992248067331 289025919504328488372100997)
  ·
    refine ⟨54192359907061591569768937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 289025919504328488372100997 54192359907061591569768937)
    ·
      refine ⟨40644269930296193677326703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54192359907061591569768937 40644269930296193677326703)
      ·
        refine ⟨60966404895444290515990055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40644269930296193677326703 60966404895444290515990055)
        ·
          refine ⟨91449607343166435773985083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60966404895444290515990055 91449607343166435773985083)
          ·
            refine ⟨137174411014749653660977625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91449607343166435773985083 137174411014749653660977625)
            ·
              refine ⟨102880808261062240245733219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137174411014749653660977625 102880808261062240245733219)
              ·
                refine ⟨154321212391593360368599829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102880808261062240245733219 154321212391593360368599829)
                ·
                  refine ⟨7233806830855938767278117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 154321212391593360368599829 7233806830855938767278117)
                  ·
                    refine ⟨1356338780785488518864647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7233806830855938767278117 1356338780785488518864647)
                    ·
                      rfl

theorem cell23_7924381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 1, 6, 4].length) (baseStart_7924381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7924381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7924381 prefixEnd_7924381 := by exact prefixLift 7924381
  have htrace : WordTrace (prefixWord ++ tailWord_7924381) baseStart_7924381 baseEnd_7924381 := by
    simpa [prefixWord, tailWord_7924381, baseEnd_7924381] using wordTrace_append hprefix tailTrace_7924381
  have hstable : (prefixWord ++ tailWord_7924381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7924381).length < 2 ^ (prefixWord ++ tailWord_7924381).sum := by decide
  have hdescent : baseEnd_7924381 < baseStart_7924381 := by decide
  rcases family_descends (prefixWord ++ tailWord_7924381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7924382 : List Nat := [4, 3, 1, 1, 1, 1, 2, 5, 1, 1, 3]
def baseStart_7924382 : Nat := 118140960795 + 7924382 * 2 ^ 59
def prefixEnd_7924382 : Nat := 4983230072969 + 3 ^ 40 * 7924382 * 2
def baseEnd_7924382 : Nat := 4069016855837120052681437

theorem tailTrace_7924382 : CollatzResearch.WordTrace tailWord_7924382 prefixEnd_7924382 4069016855837120052681437 := by
  unfold tailWord_7924382
  simp only [CollatzResearch.WordTrace]
  refine ⟨36128244497165608192860925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 192683970651549910361924933 36128244497165608192860925)
  ·
    refine ⟨13548091686437103072322847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36128244497165608192860925 13548091686437103072322847)
    ·
      refine ⟨20322137529655654608484271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13548091686437103072322847 20322137529655654608484271)
      ·
        refine ⟨30483206294483481912726407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20322137529655654608484271 30483206294483481912726407)
        ·
          refine ⟨45724809441725222869089611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30483206294483481912726407 45724809441725222869089611)
          ·
            refine ⟨68587214162587834303634417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45724809441725222869089611 68587214162587834303634417)
            ·
              refine ⟨51440410621940875727725813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68587214162587834303634417 51440410621940875727725813)
              ·
                refine ⟨4822538495806957099474295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 51440410621940875727725813 4822538495806957099474295)
                ·
                  refine ⟨7233807743710435649211443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4822538495806957099474295 7233807743710435649211443)
                  ·
                    refine ⟨10850711615565653473817165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7233807743710435649211443 10850711615565653473817165)
                    ·
                      refine ⟨4069016855837120052681437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10850711615565653473817165 4069016855837120052681437)
                      ·
                        rfl

theorem cell23_7924382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 5, 1, 1, 3].length) (baseStart_7924382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7924382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7924382 prefixEnd_7924382 := by exact prefixLift 7924382
  have htrace : WordTrace (prefixWord ++ tailWord_7924382) baseStart_7924382 baseEnd_7924382 := by
    simpa [prefixWord, tailWord_7924382, baseEnd_7924382] using wordTrace_append hprefix tailTrace_7924382
  have hstable : (prefixWord ++ tailWord_7924382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7924382).length < 2 ^ (prefixWord ++ tailWord_7924382).sum := by decide
  have hdescent : baseEnd_7924382 < baseStart_7924382 := by decide
  rcases family_descends (prefixWord ++ tailWord_7924382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7924385 : List Nat := [1, 2, 3, 3, 3, 1, 3, 1, 1, 5]
def baseStart_7924385 : Nat := 118140960795 + 7924385 * 2 ^ 59
def prefixEnd_7924385 : Nat := 4983230072969 + 3 ^ 40 * 7924385 * 2
def baseEnd_7924385 : Nat := 1356339465426361180314641

theorem tailTrace_7924385 : CollatzResearch.WordTrace tailWord_7924385 prefixEnd_7924385 1356339465426361180314641 := by
  unfold tailWord_7924385
  simp only [CollatzResearch.WordTrace]
  refine ⟨289026065396313997055246609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192684043597542664703497739 289026065396313997055246609)
  ·
    refine ⟨216769549047235497791434957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 289026065396313997055246609 216769549047235497791434957)
    ·
      refine ⟨81288580892713311671788109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 216769549047235497791434957 81288580892713311671788109)
      ·
        refine ⟨30483217834767491876920541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81288580892713311671788109 30483217834767491876920541)
        ·
          refine ⟨11431206688037809453845203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30483217834767491876920541 11431206688037809453845203)
          ·
            refine ⟨17146810032056714180767805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11431206688037809453845203 17146810032056714180767805)
            ·
              refine ⟨6430053762021267817787927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17146810032056714180767805 6430053762021267817787927)
              ·
                refine ⟨9645080643031901726681891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6430053762021267817787927 9645080643031901726681891)
                ·
                  refine ⟨14467620964547852590022837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9645080643031901726681891 14467620964547852590022837)
                  ·
                    refine ⟨1356339465426361180314641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14467620964547852590022837 1356339465426361180314641)
                    ·
                      rfl

theorem cell23_7924385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 3, 1, 1, 5].length) (baseStart_7924385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7924385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7924385 prefixEnd_7924385 := by exact prefixLift 7924385
  have htrace : WordTrace (prefixWord ++ tailWord_7924385) baseStart_7924385 baseEnd_7924385 := by
    simpa [prefixWord, tailWord_7924385, baseEnd_7924385] using wordTrace_append hprefix tailTrace_7924385
  have hstable : (prefixWord ++ tailWord_7924385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7924385).length < 2 ^ (prefixWord ++ tailWord_7924385).sum := by decide
  have hdescent : baseEnd_7924385 < baseStart_7924385 := by decide
  rcases family_descends (prefixWord ++ tailWord_7924385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7924428 : List Nat := [2, 2, 1, 5, 1, 2, 3, 7]
def baseStart_7924428 : Nat := 118140960795 + 7924428 * 2 ^ 59
def prefixEnd_7924428 : Nat := 4983230072969 + 3 ^ 40 * 7924428 * 2
def baseEnd_7924428 : Nat := 150705202812860254544675

theorem tailTrace_7924428 : CollatzResearch.WordTrace tailWord_7924428 prefixEnd_7924428 150705202812860254544675 := by
  unfold tailWord_7924428
  simp only [CollatzResearch.WordTrace]
  refine ⟨144513816867579107699530969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192685089156772143599374625 144513816867579107699530969)
  ·
    refine ⟨108385362650684330774648227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144513816867579107699530969 108385362650684330774648227)
    ·
      refine ⟨162578043976026496161972341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108385362650684330774648227 162578043976026496161972341)
      ·
        refine ⟨15241691622752484015184907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 162578043976026496161972341 15241691622752484015184907)
        ·
          refine ⟨22862537434128726022777361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15241691622752484015184907 22862537434128726022777361)
          ·
            refine ⟨17146903075596544517083021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22862537434128726022777361 17146903075596544517083021)
            ·
              refine ⟨6430088653348704193906133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17146903075596544517083021 6430088653348704193906133)
              ·
                refine ⟨150705202812860254544675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6430088653348704193906133 150705202812860254544675)
                ·
                  rfl

theorem cell23_7924428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 3, 7].length) (baseStart_7924428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7924428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7924428 prefixEnd_7924428 := by exact prefixLift 7924428
  have htrace : WordTrace (prefixWord ++ tailWord_7924428) baseStart_7924428 baseEnd_7924428 := by
    simpa [prefixWord, tailWord_7924428, baseEnd_7924428] using wordTrace_append hprefix tailTrace_7924428
  have hstable : (prefixWord ++ tailWord_7924428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7924428).length < 2 ^ (prefixWord ++ tailWord_7924428).sum := by decide
  have hdescent : baseEnd_7924428 < baseStart_7924428 := by decide
  rcases family_descends (prefixWord ++ tailWord_7924428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7924469 : List Nat := [1, 3, 6, 1, 1, 2, 1, 1, 1, 2, 4]
def baseStart_7924469 : Nat := 118140960795 + 7924469 * 2 ^ 59
def prefixEnd_7924469 : Nat := 4983230072969 + 3 ^ 40 * 7924469 * 2
def baseEnd_7924469 : Nat := 4069061528654061212293537

theorem tailTrace_7924469 : CollatzResearch.WordTrace tailWord_7924469 prefixEnd_7924469 4069061528654061212293537 := by
  unfold tailWord_7924469
  simp only [CollatzResearch.WordTrace]
  refine ⟨289029129128009679401304461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192686086085339786267536307 289029129128009679401304461)
  ·
    refine ⟨108385923423003629775489173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 289029129128009679401304461 108385923423003629775489173)
    ·
      refine ⟨5080590160453295145726055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 108385923423003629775489173 5080590160453295145726055)
      ·
        refine ⟨7620885240679942718589083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5080590160453295145726055 7620885240679942718589083)
        ·
          refine ⟨11431327861019914077883625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7620885240679942718589083 11431327861019914077883625)
          ·
            refine ⟨8573495895764935558412719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11431327861019914077883625 8573495895764935558412719)
            ·
              refine ⟨12860243843647403337619079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8573495895764935558412719 12860243843647403337619079)
              ·
                refine ⟨19290365765471105006428619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12860243843647403337619079 19290365765471105006428619)
                ·
                  refine ⟨28935548648206657509642929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19290365765471105006428619 28935548648206657509642929)
                  ·
                    refine ⟨21701661486154993132232197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28935548648206657509642929 21701661486154993132232197)
                    ·
                      refine ⟨4069061528654061212293537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21701661486154993132232197 4069061528654061212293537)
                      ·
                        rfl

theorem cell23_7924469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 2, 1, 1, 1, 2, 4].length) (baseStart_7924469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7924469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7924469 prefixEnd_7924469 := by exact prefixLift 7924469
  have htrace : WordTrace (prefixWord ++ tailWord_7924469) baseStart_7924469 baseEnd_7924469 := by
    simpa [prefixWord, tailWord_7924469, baseEnd_7924469] using wordTrace_append hprefix tailTrace_7924469
  have hstable : (prefixWord ++ tailWord_7924469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7924469).length < 2 ^ (prefixWord ++ tailWord_7924469).sum := by decide
  have hdescent : baseEnd_7924469 < baseStart_7924469 := by decide
  rcases family_descends (prefixWord ++ tailWord_7924469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7924481 : List Nat := [1, 2, 4, 1, 1, 1, 1, 4, 2, 1, 5]
def baseStart_7924481 : Nat := 118140960795 + 7924481 * 2 ^ 59
def prefixEnd_7924481 : Nat := 4983230072969 + 3 ^ 40 * 7924481 * 2
def baseEnd_7924481 : Nat := 4069067690421915165343481

theorem tailTrace_7924481 : CollatzResearch.WordTrace tailWord_7924481 prefixEnd_7924481 4069067690421915165343481 := by
  unfold tailWord_7924481
  simp only [CollatzResearch.WordTrace]
  refine ⟨289029566803966205450741297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192686377869310803633827531 289029566803966205450741297)
  ·
    refine ⟨216772175102974654088055973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 289029566803966205450741297 216772175102974654088055973)
    ·
      refine ⟨40644782831807747641510495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 216772175102974654088055973 40644782831807747641510495)
      ·
        refine ⟨60967174247711621462265743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40644782831807747641510495 60967174247711621462265743)
        ·
          refine ⟨91450761371567432193398615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60967174247711621462265743 91450761371567432193398615)
          ·
            refine ⟨137176142057351148290097923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91450761371567432193398615 137176142057351148290097923)
            ·
              refine ⟨205764213086026722435146885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137176142057351148290097923 205764213086026722435146885)
              ·
                refine ⟨38580789953630010456590041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 205764213086026722435146885 38580789953630010456590041)
                ·
                  refine ⟨28935592465222507842442531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38580789953630010456590041 28935592465222507842442531)
                  ·
                    refine ⟨43403388697833761763663797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28935592465222507842442531 43403388697833761763663797)
                    ·
                      refine ⟨4069067690421915165343481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43403388697833761763663797 4069067690421915165343481)
                      ·
                        rfl

theorem cell23_7924481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 4, 2, 1, 5].length) (baseStart_7924481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7924481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7924481 prefixEnd_7924481 := by exact prefixLift 7924481
  have htrace : WordTrace (prefixWord ++ tailWord_7924481) baseStart_7924481 baseEnd_7924481 := by
    simpa [prefixWord, tailWord_7924481, baseEnd_7924481] using wordTrace_append hprefix tailTrace_7924481
  have hstable : (prefixWord ++ tailWord_7924481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7924481).length < 2 ^ (prefixWord ++ tailWord_7924481).sum := by decide
  have hdescent : baseEnd_7924481 < baseStart_7924481 := by decide
  rcases family_descends (prefixWord ++ tailWord_7924481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7924482 : List Nat := [3, 4, 1, 1, 1, 2, 1, 4, 1, 3, 2]
def baseStart_7924482 : Nat := 118140960795 + 7924482 * 2 ^ 59
def prefixEnd_7924482 : Nat := 4983230072969 + 3 ^ 40 * 7924482 * 2
def baseEnd_7924482 : Nat := 4069068203902569661430977

theorem tailTrace_7924482 : CollatzResearch.WordTrace tailWord_7924482 prefixEnd_7924482 4069068203902569661430977 := by
  unfold tailWord_7924482
  simp only [CollatzResearch.WordTrace]
  refine ⟨72257400819240645655381925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192686402184641721747685133 72257400819240645655381925)
  ·
    refine ⟨13548262653607621060384111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72257400819240645655381925 13548262653607621060384111)
    ·
      refine ⟨20322393980411431590576167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13548262653607621060384111 20322393980411431590576167)
      ·
        refine ⟨30483590970617147385864251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20322393980411431590576167 30483590970617147385864251)
        ·
          refine ⟨45725386455925721078796377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30483590970617147385864251 45725386455925721078796377)
          ·
            refine ⟨34294039841944290809097283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45725386455925721078796377 34294039841944290809097283)
            ·
              refine ⟨51441059762916436213645925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34294039841944290809097283 51441059762916436213645925)
              ·
                refine ⟨9645198705546831790058611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51441059762916436213645925 9645198705546831790058611)
                ·
                  refine ⟨14467798058320247685087917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9645198705546831790058611 14467798058320247685087917)
                  ·
                    refine ⟨5425424271870092881907969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14467798058320247685087917 5425424271870092881907969)
                    ·
                      refine ⟨4069068203902569661430977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5425424271870092881907969 4069068203902569661430977)
                      ·
                        rfl

theorem cell23_7924482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 4, 1, 3, 2].length) (baseStart_7924482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7924482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7924482 prefixEnd_7924482 := by exact prefixLift 7924482
  have htrace : WordTrace (prefixWord ++ tailWord_7924482) baseStart_7924482 baseEnd_7924482 := by
    simpa [prefixWord, tailWord_7924482, baseEnd_7924482] using wordTrace_append hprefix tailTrace_7924482
  have hstable : (prefixWord ++ tailWord_7924482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7924482).length < 2 ^ (prefixWord ++ tailWord_7924482).sum := by decide
  have hdescent : baseEnd_7924482 < baseStart_7924482 := by decide
  rcases family_descends (prefixWord ++ tailWord_7924482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7924568 : List Nat := [2, 1, 2, 2, 1, 1, 1, 2, 3, 6, 2]
def baseStart_7924568 : Nat := 118140960795 + 7924568 * 2 ^ 59
def prefixEnd_7924568 : Nat := 4983230072969 + 3 ^ 40 * 7924568 * 2
def baseEnd_7924568 : Nat := 4069112363238856324955581

theorem tailTrace_7924568 : CollatzResearch.WordTrace tailWord_7924568 prefixEnd_7924568 4069112363238856324955581 := by
  unfold tailWord_7924568
  simp only [CollatzResearch.WordTrace]
  refine ⟨144516369977325509654579179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192688493303100679539438905 144516369977325509654579179)
  ·
    refine ⟨216774554965988264481868769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144516369977325509654579179 216774554965988264481868769)
    ·
      refine ⟨162580916224491198361401577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216774554965988264481868769 162580916224491198361401577)
      ·
        refine ⟨121935687168368398771051183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162580916224491198361401577 121935687168368398771051183)
        ·
          refine ⟨182903530752552598156576775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121935687168368398771051183 182903530752552598156576775)
          ·
            refine ⟨274355296128828897234865163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182903530752552598156576775 274355296128828897234865163)
            ·
              refine ⟨411532944193243345852297745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 274355296128828897234865163 411532944193243345852297745)
              ·
                refine ⟨308649708144932509389223309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 411532944193243345852297745 308649708144932509389223309)
                ·
                  refine ⟨115743640554349691020958741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 308649708144932509389223309 115743640554349691020958741)
                  ·
                    refine ⟨5425483150985141766607441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 115743640554349691020958741 5425483150985141766607441)
                    ·
                      refine ⟨4069112363238856324955581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5425483150985141766607441 4069112363238856324955581)
                      ·
                        rfl

theorem cell23_7924568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 2, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 2, 3, 6, 2].length) (baseStart_7924568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7924568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7924568 prefixEnd_7924568 := by exact prefixLift 7924568
  have htrace : WordTrace (prefixWord ++ tailWord_7924568) baseStart_7924568 baseEnd_7924568 := by
    simpa [prefixWord, tailWord_7924568, baseEnd_7924568] using wordTrace_append hprefix tailTrace_7924568
  have hstable : (prefixWord ++ tailWord_7924568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7924568).length < 2 ^ (prefixWord ++ tailWord_7924568).sum := by decide
  have hdescent : baseEnd_7924568 < baseStart_7924568 := by decide
  rcases family_descends (prefixWord ++ tailWord_7924568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7924588 : List Nat := [2, 2, 1, 1, 4, 1, 2, 2, 1, 4, 3]
def baseStart_7924588 : Nat := 118140960795 + 7924588 * 2 ^ 59
def prefixEnd_7924588 : Nat := 4983230072969 + 3 ^ 40 * 7924588 * 2
def baseEnd_7924588 : Nat := 4069122632851946246705489

theorem tailTrace_7924588 : CollatzResearch.WordTrace tailWord_7924588 prefixEnd_7924588 4069122632851946246705489 := by
  unfold tailWord_7924588
  simp only [CollatzResearch.WordTrace]
  refine ⟨144516734707289281362443209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192688979609719041816590945 144516734707289281362443209)
  ·
    refine ⟨108387551030466961021832407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144516734707289281362443209 108387551030466961021832407)
    ·
      refine ⟨162581326545700441532748611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108387551030466961021832407 162581326545700441532748611)
      ·
        refine ⟨243871989818550662299122917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162581326545700441532748611 243871989818550662299122917)
        ·
          refine ⟨45725998090978249181085547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 243871989818550662299122917 45725998090978249181085547)
          ·
            refine ⟨68588997136467373771628321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45725998090978249181085547 68588997136467373771628321)
            ·
              refine ⟨51441747852350530328721241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68588997136467373771628321 51441747852350530328721241)
              ·
                refine ⟨38581310889262897746540931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51441747852350530328721241 38581310889262897746540931)
                ·
                  refine ⟨57871966333894346619811397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38581310889262897746540931 57871966333894346619811397)
                  ·
                    refine ⟨10850993687605189991214637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 57871966333894346619811397 10850993687605189991214637)
                    ·
                      refine ⟨4069122632851946246705489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10850993687605189991214637 4069122632851946246705489)
                      ·
                        rfl

theorem cell23_7924588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 4, 3].length) (baseStart_7924588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7924588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7924588 prefixEnd_7924588 := by exact prefixLift 7924588
  have htrace : WordTrace (prefixWord ++ tailWord_7924588) baseStart_7924588 baseEnd_7924588 := by
    simpa [prefixWord, tailWord_7924588, baseEnd_7924588] using wordTrace_append hprefix tailTrace_7924588
  have hstable : (prefixWord ++ tailWord_7924588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7924588).length < 2 ^ (prefixWord ++ tailWord_7924588).sum := by decide
  have hdescent : baseEnd_7924588 < baseStart_7924588 := by decide
  rcases family_descends (prefixWord ++ tailWord_7924588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7924605 : List Nat := [1, 4, 1, 1, 2, 1, 5, 1, 2, 2, 3]
def baseStart_7924605 : Nat := 118140960795 + 7924605 * 2 ^ 59
def prefixEnd_7924605 : Nat := 4983230072969 + 3 ^ 40 * 7924605 * 2
def baseEnd_7924605 : Nat := 4069131362023072680192911

theorem tailTrace_7924605 : CollatzResearch.WordTrace tailWord_7924605 prefixEnd_7924605 4069131362023072680192911 := by
  unfold tailWord_7924605
  simp only [CollatzResearch.WordTrace]
  refine ⟨289034089455516974628255269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192689392970344649752170179 289034089455516974628255269)
  ·
    refine ⟨54193891772909432742797863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 289034089455516974628255269 54193891772909432742797863)
    ·
      refine ⟨81290837659364149114196795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54193891772909432742797863 81290837659364149114196795)
      ·
        refine ⟨121936256489046223671295193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81290837659364149114196795 121936256489046223671295193)
        ·
          refine ⟨91452192366784667753471395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121936256489046223671295193 91452192366784667753471395)
          ·
            refine ⟨137178288550177001630207093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91452192366784667753471395 137178288550177001630207093)
            ·
              refine ⟨12860464551579093902831915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 137178288550177001630207093 12860464551579093902831915)
              ·
                refine ⟨19290696827368640854247873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12860464551579093902831915 19290696827368640854247873)
                ·
                  refine ⟨14468022620526480640685905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19290696827368640854247873 14468022620526480640685905)
                  ·
                    refine ⟨10851016965394860480514429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14468022620526480640685905 10851016965394860480514429)
                    ·
                      refine ⟨4069131362023072680192911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10851016965394860480514429 4069131362023072680192911)
                      ·
                        rfl

theorem cell23_7924605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 5, 1, 2, 2, 3].length) (baseStart_7924605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7924605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7924605 prefixEnd_7924605 := by exact prefixLift 7924605
  have htrace : WordTrace (prefixWord ++ tailWord_7924605) baseStart_7924605 baseEnd_7924605 := by
    simpa [prefixWord, tailWord_7924605, baseEnd_7924605] using wordTrace_append hprefix tailTrace_7924605
  have hstable : (prefixWord ++ tailWord_7924605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7924605).length < 2 ^ (prefixWord ++ tailWord_7924605).sum := by decide
  have hdescent : baseEnd_7924605 < baseStart_7924605 := by decide
  rcases family_descends (prefixWord ++ tailWord_7924605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7924628 : List Nat := [2, 4, 2, 1, 1, 1, 1, 1, 1, 1, 8]
def baseStart_7924628 : Nat := 118140960795 + 7924628 * 2 ^ 59
def prefixEnd_7924628 : Nat := 4983230072969 + 3 ^ 40 * 7924628 * 2
def baseEnd_7924628 : Nat := 4069143172078126090205305

theorem tailTrace_7924628 : CollatzResearch.WordTrace tailWord_7924628 prefixEnd_7924628 4069143172078126090205305 := by
  unfold tailWord_7924628
  simp only [CollatzResearch.WordTrace]
  refine ⟨144517464167216824778171269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192689952222955766370895025 144517464167216824778171269)
  ·
    refine ⟨27097024531353154645907113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 144517464167216824778171269 27097024531353154645907113)
    ·
      refine ⟨20322768398514865984430335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27097024531353154645907113 20322768398514865984430335)
      ·
        refine ⟨30484152597772298976645503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20322768398514865984430335 30484152597772298976645503)
        ·
          refine ⟨45726228896658448464968255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30484152597772298976645503 45726228896658448464968255)
          ·
            refine ⟨68589343344987672697452383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45726228896658448464968255 68589343344987672697452383)
            ·
              refine ⟨102884015017481509046178575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68589343344987672697452383 102884015017481509046178575)
              ·
                refine ⟨154326022526222263569267863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102884015017481509046178575 154326022526222263569267863)
                ·
                  refine ⟨231489033789333395353901795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 154326022526222263569267863 231489033789333395353901795)
                  ·
                    refine ⟨347233550684000093030852693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 231489033789333395353901795 347233550684000093030852693)
                    ·
                      refine ⟨4069143172078126090205305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 347233550684000093030852693 4069143172078126090205305)
                      ·
                        rfl

theorem cell23_7924628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 1, 1, 1, 8].length) (baseStart_7924628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7924628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7924628 prefixEnd_7924628 := by exact prefixLift 7924628
  have htrace : WordTrace (prefixWord ++ tailWord_7924628) baseStart_7924628 baseEnd_7924628 := by
    simpa [prefixWord, tailWord_7924628, baseEnd_7924628] using wordTrace_append hprefix tailTrace_7924628
  have hstable : (prefixWord ++ tailWord_7924628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7924628).length < 2 ^ (prefixWord ++ tailWord_7924628).sum := by decide
  have hdescent : baseEnd_7924628 < baseStart_7924628 := by decide
  rcases family_descends (prefixWord ++ tailWord_7924628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7924642 : List Nat := [3, 3, 1, 2, 2, 2, 3, 1, 6]
def baseStart_7924642 : Nat := 118140960795 + 7924642 * 2 ^ 59
def prefixEnd_7924642 : Nat := 4983230072969 + 3 ^ 40 * 7924642 * 2
def baseEnd_7924642 : Nat := 452127817867476559492249

theorem tailTrace_7924642 : CollatzResearch.WordTrace tailWord_7924642 prefixEnd_7924642 452127817867476559492249 := by
  unfold tailWord_7924642
  simp only [CollatzResearch.WordTrace]
  refine ⟨72258859739095732486838045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192690292637588619964901453 72258859739095732486838045)
  ·
    refine ⟨27097072402160899682564267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72258859739095732486838045 27097072402160899682564267)
    ·
      refine ⟨40645608603241349523846401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27097072402160899682564267 40645608603241349523846401)
      ·
        refine ⟨30484206452431012142884801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40645608603241349523846401 30484206452431012142884801)
        ·
          refine ⟨22863154839323259107163601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30484206452431012142884801 22863154839323259107163601)
          ·
            refine ⟨17147366129492444330372701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22863154839323259107163601 17147366129492444330372701)
            ·
              refine ⟨6430262298559666623889763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17147366129492444330372701 6430262298559666623889763)
              ·
                refine ⟨9645393447839499935834645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6430262298559666623889763 9645393447839499935834645)
                ·
                  refine ⟨452127817867476559492249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9645393447839499935834645 452127817867476559492249)
                  ·
                    rfl

theorem cell23_7924642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 3, 1, 6].length) (baseStart_7924642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7924642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7924642 prefixEnd_7924642 := by exact prefixLift 7924642
  have htrace : WordTrace (prefixWord ++ tailWord_7924642) baseStart_7924642 baseEnd_7924642 := by
    simpa [prefixWord, tailWord_7924642, baseEnd_7924642] using wordTrace_append hprefix tailTrace_7924642
  have hstable : (prefixWord ++ tailWord_7924642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7924642).length < 2 ^ (prefixWord ++ tailWord_7924642).sum := by decide
  have hdescent : baseEnd_7924642 < baseStart_7924642 := by decide
  rcases family_descends (prefixWord ++ tailWord_7924642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7924686 : List Nat := [4, 1, 1, 1, 2, 4, 3, 2, 1, 1, 3]
def baseStart_7924686 : Nat := 118140960795 + 7924686 * 2 ^ 59
def prefixEnd_7924686 : Nat := 4983230072969 + 3 ^ 40 * 7924686 * 2
def baseEnd_7924686 : Nat := 4069172953956086863280039

theorem tailTrace_7924686 : CollatzResearch.WordTrace tailWord_7924686 prefixEnd_7924686 4069172953956086863280039 := by
  unfold tailWord_7924686
  simp only [CollatzResearch.WordTrace]
  refine ⟨36129630471027940682744239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 192691362512149016974635941 36129630471027940682744239)
  ·
    refine ⟨54194445706541911024116359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36129630471027940682744239 54194445706541911024116359)
    ·
      refine ⟨81291668559812866536174539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54194445706541911024116359 81291668559812866536174539)
      ·
        refine ⟨121937502839719299804261809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81291668559812866536174539 121937502839719299804261809)
        ·
          refine ⟨91453127129789474853196357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121937502839719299804261809 91453127129789474853196357)
          ·
            refine ⟨17147461336835526534974317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 91453127129789474853196357 17147461336835526534974317)
            ·
              refine ⟨6430298001313322450615369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17147461336835526534974317 6430298001313322450615369)
              ·
                refine ⟨4822723500984991837961527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6430298001313322450615369 4822723500984991837961527)
                ·
                  refine ⟨7234085251477487756942291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4822723500984991837961527 7234085251477487756942291)
                  ·
                    refine ⟨10851127877216231635413437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7234085251477487756942291 10851127877216231635413437)
                    ·
                      refine ⟨4069172953956086863280039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10851127877216231635413437 4069172953956086863280039)
                      ·
                        rfl

theorem cell23_7924686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 3, 2, 1, 1, 3].length) (baseStart_7924686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7924686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7924686 prefixEnd_7924686 := by exact prefixLift 7924686
  have htrace : WordTrace (prefixWord ++ tailWord_7924686) baseStart_7924686 baseEnd_7924686 := by
    simpa [prefixWord, tailWord_7924686, baseEnd_7924686] using wordTrace_append hprefix tailTrace_7924686
  have hstable : (prefixWord ++ tailWord_7924686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7924686).length < 2 ^ (prefixWord ++ tailWord_7924686).sum := by decide
  have hdescent : baseEnd_7924686 < baseStart_7924686 := by decide
  rcases family_descends (prefixWord ++ tailWord_7924686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7924698 : List Nat := [3, 1, 1, 2, 4, 1, 1, 10]
def baseStart_7924698 : Nat := 118140960795 + 7924698 * 2 ^ 59
def prefixEnd_7924698 : Nat := 4983230072969 + 3 ^ 40 * 7924698 * 2
def baseEnd_7924698 : Nat := 150710337619405215419629

theorem tailTrace_7924698 : CollatzResearch.WordTrace tailWord_7924698 prefixEnd_7924698 150710337619405215419629 := by
  unfold tailWord_7924698
  simp only [CollatzResearch.WordTrace]
  refine ⟨72259370361045012877847687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192691654296120034340927165 72259370361045012877847687)
  ·
    refine ⟨108389055541567519316771531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72259370361045012877847687 108389055541567519316771531)
    ·
      refine ⟨162583583312351278975157297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108389055541567519316771531 162583583312351278975157297)
      ·
        refine ⟨121937687484263459231367973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162583583312351278975157297 121937687484263459231367973)
        ·
          refine ⟨22863316403299398605881495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 121937687484263459231367973 22863316403299398605881495)
          ·
            refine ⟨34294974604949097908822243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22863316403299398605881495 34294974604949097908822243)
            ·
              refine ⟨51442461907423646863233365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34294974604949097908822243 51442461907423646863233365)
              ·
                refine ⟨150710337619405215419629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 51442461907423646863233365 150710337619405215419629)
                ·
                  rfl

theorem cell23_7924698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 10].length) (baseStart_7924698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7924698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7924698 prefixEnd_7924698 := by exact prefixLift 7924698
  have htrace : WordTrace (prefixWord ++ tailWord_7924698) baseStart_7924698 baseEnd_7924698 := by
    simpa [prefixWord, tailWord_7924698, baseEnd_7924698] using wordTrace_append hprefix tailTrace_7924698
  have hstable : (prefixWord ++ tailWord_7924698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7924698).length < 2 ^ (prefixWord ++ tailWord_7924698).sum := by decide
  have hdescent : baseEnd_7924698 < baseStart_7924698 := by decide
  rcases family_descends (prefixWord ++ tailWord_7924698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7924712 : List Nat := [2, 1, 4, 1, 1, 1, 5, 2, 1, 2, 3]
def baseStart_7924712 : Nat := 118140960795 + 7924712 * 2 ^ 59
def prefixEnd_7924712 : Nat := 4983230072969 + 3 ^ 40 * 7924712 * 2
def baseEnd_7924712 : Nat := 4069186304453103761554919

theorem tailTrace_7924712 : CollatzResearch.WordTrace tailWord_7924712 prefixEnd_7924712 4069186304453103761554919 := by
  unfold tailWord_7924712
  simp only [CollatzResearch.WordTrace]
  refine ⟨144518996033064665951200195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192691994710752887934933593 144518996033064665951200195)
  ·
    refine ⟨216778494049596998926800293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144518996033064665951200195 216778494049596998926800293)
    ·
      refine ⟨40645967634299437298775055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 216778494049596998926800293 40645967634299437298775055)
      ·
        refine ⟨60968951451449155948162583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40645967634299437298775055 60968951451449155948162583)
        ·
          refine ⟨91453427177173733922243875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60968951451449155948162583 91453427177173733922243875)
          ·
            refine ⟨137180140765760600883365813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91453427177173733922243875 137180140765760600883365813)
            ·
              refine ⟨12860638196790056332815545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 137180140765760600883365813 12860638196790056332815545)
              ·
                refine ⟨9645478647592542249611659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12860638196790056332815545 9645478647592542249611659)
                ·
                  refine ⟨14468217971388813374417489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9645478647592542249611659 14468217971388813374417489)
                  ·
                    refine ⟨10851163478541610030813117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14468217971388813374417489 10851163478541610030813117)
                    ·
                      refine ⟨4069186304453103761554919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10851163478541610030813117 4069186304453103761554919)
                      ·
                        rfl

theorem cell23_7924712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 5, 2, 1, 2, 3].length) (baseStart_7924712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7924712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7924712 prefixEnd_7924712 := by exact prefixLift 7924712
  have htrace : WordTrace (prefixWord ++ tailWord_7924712) baseStart_7924712 baseEnd_7924712 := by
    simpa [prefixWord, tailWord_7924712, baseEnd_7924712] using wordTrace_append hprefix tailTrace_7924712
  have hstable : (prefixWord ++ tailWord_7924712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7924712).length < 2 ^ (prefixWord ++ tailWord_7924712).sum := by decide
  have hdescent : baseEnd_7924712 < baseStart_7924712 := by decide
  rcases family_descends (prefixWord ++ tailWord_7924712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7924759 : List Nat := [1, 1, 3, 5, 1, 1, 2, 3, 2, 1, 3]
def baseStart_7924759 : Nat := 118140960795 + 7924759 * 2 ^ 59
def prefixEnd_7924759 : Nat := 4983230072969 + 3 ^ 40 * 7924759 * 2
def baseEnd_7924759 : Nat := 4069210438043865077667203

theorem tailTrace_7924759 : CollatzResearch.WordTrace tailWord_7924759 prefixEnd_7924759 4069210438043865077667203 := by
  unfold tailWord_7924759
  simp only [CollatzResearch.WordTrace]
  refine ⟨289039706296959058929361331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192693137531306039286240887 289039706296959058929361331)
  ·
    refine ⟨433559559445438588394041997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289039706296959058929361331 433559559445438588394041997)
    ·
      refine ⟨162584834792039470647765749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 433559559445438588394041997 162584834792039470647765749)
      ·
        refine ⟨15242328261753700373228039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 162584834792039470647765749 15242328261753700373228039)
        ·
          refine ⟨22863492392630550559842059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15242328261753700373228039 22863492392630550559842059)
          ·
            refine ⟨34295238588945825839763089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22863492392630550559842059 34295238588945825839763089)
            ·
              refine ⟨25721428941709369379822317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34295238588945825839763089 25721428941709369379822317)
              ·
                refine ⟨9645535853141013517433369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25721428941709369379822317 9645535853141013517433369)
                ·
                  refine ⟨7234151889855760138075027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9645535853141013517433369 7234151889855760138075027)
                  ·
                    refine ⟨10851227834783640207112541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7234151889855760138075027 10851227834783640207112541)
                    ·
                      refine ⟨4069210438043865077667203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10851227834783640207112541 4069210438043865077667203)
                      ·
                        rfl

theorem cell23_7924759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 2, 3, 2, 1, 3].length) (baseStart_7924759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7924759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7924759 prefixEnd_7924759 := by exact prefixLift 7924759
  have htrace : WordTrace (prefixWord ++ tailWord_7924759) baseStart_7924759 baseEnd_7924759 := by
    simpa [prefixWord, tailWord_7924759, baseEnd_7924759] using wordTrace_append hprefix tailTrace_7924759
  have hstable : (prefixWord ++ tailWord_7924759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7924759).length < 2 ^ (prefixWord ++ tailWord_7924759).sum := by decide
  have hdescent : baseEnd_7924759 < baseStart_7924759 := by decide
  rcases family_descends (prefixWord ++ tailWord_7924759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7924835 : List Nat := [1, 1, 1, 5, 1, 1, 1, 5, 2, 5]
def baseStart_7924835 : Nat := 118140960795 + 7924835 * 2 ^ 59
def prefixEnd_7924835 : Nat := 4983230072969 + 3 ^ 40 * 7924835 * 2
def baseEnd_7924835 : Nat := 1356416487524535593438951

theorem tailTrace_7924835 : CollatzResearch.WordTrace tailWord_7924835 prefixEnd_7924835 1356416487524535593438951 := by
  unfold tailWord_7924835
  simp only [CollatzResearch.WordTrace]
  refine ⟨289042478244683723909127959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192694985496455815939418639 289042478244683723909127959)
  ·
    refine ⟨433563717367025585863691939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289042478244683723909127959 433563717367025585863691939)
    ·
      refine ⟨650345576050538378795537909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 433563717367025585863691939 650345576050538378795537909)
      ·
        refine ⟨60969897754737973012081679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 650345576050538378795537909 60969897754737973012081679)
        ·
          refine ⟨91454846632106959518122519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60969897754737973012081679 91454846632106959518122519)
          ·
            refine ⟨137182269948160439277183779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91454846632106959518122519 137182269948160439277183779)
            ·
              refine ⟨205773404922240658915775669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137182269948160439277183779 205773404922240658915775669)
              ·
                refine ⟨19291256711460061773353969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 205773404922240658915775669 19291256711460061773353969)
                ·
                  refine ⟨14468442533595046330015477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19291256711460061773353969 14468442533595046330015477)
                  ·
                    refine ⟨1356416487524535593438951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14468442533595046330015477 1356416487524535593438951)
                    ·
                      rfl

theorem cell23_7924835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 5, 2, 5].length) (baseStart_7924835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7924835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7924835 prefixEnd_7924835 := by exact prefixLift 7924835
  have htrace : WordTrace (prefixWord ++ tailWord_7924835) baseStart_7924835 baseEnd_7924835 := by
    simpa [prefixWord, tailWord_7924835, baseEnd_7924835] using wordTrace_append hprefix tailTrace_7924835
  have hstable : (prefixWord ++ tailWord_7924835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7924835).length < 2 ^ (prefixWord ++ tailWord_7924835).sum := by decide
  have hdescent : baseEnd_7924835 < baseStart_7924835 := by decide
  rcases family_descends (prefixWord ++ tailWord_7924835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7924839 : List Nat := [1, 1, 5, 1, 1, 5, 1, 3, 5]
def baseStart_7924839 : Nat := 118140960795 + 7924839 * 2 ^ 59
def prefixEnd_7924839 : Nat := 4983230072969 + 3 ^ 40 * 7924839 * 2
def baseEnd_7924839 : Nat := 452139057388469418296315

theorem tailTrace_7924839 : CollatzResearch.WordTrace tailWord_7924839 prefixEnd_7924839 452139057388469418296315 := by
  unfold tailWord_7924839
  simp only [CollatzResearch.WordTrace]
  refine ⟨289042624136669232592273571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192695082757779488394849047 289042624136669232592273571)
  ·
    refine ⟨433563936205003848888410357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289042624136669232592273571 433563936205003848888410357)
    ·
      refine ⟨40646619019219110833288471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 433563936205003848888410357 40646619019219110833288471)
      ·
        refine ⟨60969928528828666249932707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40646619019219110833288471 60969928528828666249932707)
        ·
          refine ⟨91454892793242999374899061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60969928528828666249932707 91454892793242999374899061)
          ·
            refine ⟨8573896199366531191396787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 91454892793242999374899061 8573896199366531191396787)
            ·
              refine ⟨12860844299049796787095181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8573896199366531191396787 12860844299049796787095181)
              ·
                refine ⟨4822816612143673795160693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12860844299049796787095181 4822816612143673795160693)
                ·
                  refine ⟨452139057388469418296315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4822816612143673795160693 452139057388469418296315)
                  ·
                    rfl

theorem cell23_7924839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 5, 1, 3, 5].length) (baseStart_7924839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7924839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7924839 prefixEnd_7924839 := by exact prefixLift 7924839
  have htrace : WordTrace (prefixWord ++ tailWord_7924839) baseStart_7924839 baseEnd_7924839 := by
    simpa [prefixWord, tailWord_7924839, baseEnd_7924839] using wordTrace_append hprefix tailTrace_7924839
  have hstable : (prefixWord ++ tailWord_7924839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7924839).length < 2 ^ (prefixWord ++ tailWord_7924839).sum := by decide
  have hdescent : baseEnd_7924839 < baseStart_7924839 := by decide
  rcases family_descends (prefixWord ++ tailWord_7924839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7924875 : List Nat := [1, 1, 1, 1, 4, 1, 1, 3, 3, 4, 3]
def baseStart_7924875 : Nat := 118140960795 + 7924875 * 2 ^ 59
def prefixEnd_7924875 : Nat := 4983230072969 + 3 ^ 40 * 7924875 * 2
def baseEnd_7924875 : Nat := 4069270001799786623816669

theorem tailTrace_7924875 : CollatzResearch.WordTrace tailWord_7924875 prefixEnd_7924875 4069270001799786623816669 := by
  unfold tailWord_7924875
  simp only [CollatzResearch.WordTrace]
  refine ⟨289043937164538810740584079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192695958109692540493722719 289043937164538810740584079)
  ·
    refine ⟨433565905746808216110876119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289043937164538810740584079 433565905746808216110876119)
    ·
      refine ⟨650348858620212324166314179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 433565905746808216110876119 650348858620212324166314179)
      ·
        refine ⟨975523287930318486249471269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 650348858620212324166314179 975523287930318486249471269)
        ·
          refine ⟨182910616486934716171775863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 975523287930318486249471269 182910616486934716171775863)
          ·
            refine ⟨274365924730402074257663795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182910616486934716171775863 274365924730402074257663795)
            ·
              refine ⟨411548887095603111386495693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 274365924730402074257663795 411548887095603111386495693)
              ·
                refine ⟨154330832660851166769935885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 411548887095603111386495693 154330832660851166769935885)
                ·
                  refine ⟨57874062247819187538725957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 154330832660851166769935885 57874062247819187538725957)
                  ·
                    refine ⟨10851386671466097663511117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 57874062247819187538725957 10851386671466097663511117)
                    ·
                      refine ⟨4069270001799786623816669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10851386671466097663511117 4069270001799786623816669)
                      ·
                        rfl

theorem cell23_7924875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 3, 3, 4, 3].length) (baseStart_7924875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7924875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7924875 prefixEnd_7924875 := by exact prefixLift 7924875
  have htrace : WordTrace (prefixWord ++ tailWord_7924875) baseStart_7924875 baseEnd_7924875 := by
    simpa [prefixWord, tailWord_7924875, baseEnd_7924875] using wordTrace_append hprefix tailTrace_7924875
  have hstable : (prefixWord ++ tailWord_7924875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7924875).length < 2 ^ (prefixWord ++ tailWord_7924875).sum := by decide
  have hdescent : baseEnd_7924875 < baseStart_7924875 := by decide
  rcases family_descends (prefixWord ++ tailWord_7924875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7924905 : List Nat := [1, 2, 1, 1, 1, 1, 2, 1, 3, 7, 3]
def baseStart_7924905 : Nat := 118140960795 + 7924905 * 2 ^ 59
def prefixEnd_7924905 : Nat := 4983230072969 + 3 ^ 40 * 7924905 * 2
def baseEnd_7924905 : Nat := 4069285406219421506441531

theorem tailTrace_7924905 : CollatzResearch.WordTrace tailWord_7924905 prefixEnd_7924905 4069285406219421506441531 := by
  unfold tailWord_7924905
  simp only [CollatzResearch.WordTrace]
  refine ⟨289045031354430125864176169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192696687569620083909450779 289045031354430125864176169)
  ·
    refine ⟨216783773515822594398132127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 289045031354430125864176169 216783773515822594398132127)
    ·
      refine ⟨325175660273733891597198191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216783773515822594398132127 325175660273733891597198191)
      ·
        refine ⟨487763490410600837395797287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 325175660273733891597198191 487763490410600837395797287)
        ·
          refine ⟨731645235615901256093695931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 487763490410600837395797287 731645235615901256093695931)
          ·
            refine ⟨1097467853423851884140543897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 731645235615901256093695931 1097467853423851884140543897)
            ·
              refine ⟨823100890067888913105407923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1097467853423851884140543897 823100890067888913105407923)
              ·
                refine ⟨1234651335101833369658111885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 823100890067888913105407923 1234651335101833369658111885)
                ·
                  refine ⟨462994250663187513621791957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1234651335101833369658111885 462994250663187513621791957)
                  ·
                    refine ⟨10851427749918457350510749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 462994250663187513621791957 10851427749918457350510749)
                    ·
                      refine ⟨4069285406219421506441531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10851427749918457350510749 4069285406219421506441531)
                      ·
                        rfl

theorem cell23_7924905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 3, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 3, 7, 3].length) (baseStart_7924905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7924905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7924905 prefixEnd_7924905 := by exact prefixLift 7924905
  have htrace : WordTrace (prefixWord ++ tailWord_7924905) baseStart_7924905 baseEnd_7924905 := by
    simpa [prefixWord, tailWord_7924905, baseEnd_7924905] using wordTrace_append hprefix tailTrace_7924905
  have hstable : (prefixWord ++ tailWord_7924905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7924905).length < 2 ^ (prefixWord ++ tailWord_7924905).sum := by decide
  have hdescent : baseEnd_7924905 < baseStart_7924905 := by decide
  rcases family_descends (prefixWord ++ tailWord_7924905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7924929 : List Nat := [1, 2, 6, 1, 1, 1, 2, 3, 6]
def baseStart_7924929 : Nat := 118140960795 + 7924929 * 2 ^ 59
def prefixEnd_7924929 : Nat := 4983230072969 + 3 ^ 40 * 7924929 * 2
def baseEnd_7924929 : Nat := 452144192195014379171269

theorem tailTrace_7924929 : CollatzResearch.WordTrace tailWord_7924929 prefixEnd_7924929 452144192195014379171269 := by
  unfold tailWord_7924929
  simp only [CollatzResearch.WordTrace]
  refine ⟨289045906706343177963049841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192697271137562118642033227 289045906706343177963049841)
  ·
    refine ⟨216784430029757383472287381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 289045906706343177963049841 216784430029757383472287381)
    ·
      refine ⟨10161770157644877350263471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 216784430029757383472287381 10161770157644877350263471)
      ·
        refine ⟨15242655236467316025395207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10161770157644877350263471 15242655236467316025395207)
        ·
          refine ⟨22863982854700974038092811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15242655236467316025395207 22863982854700974038092811)
          ·
            refine ⟨34295974282051461057139217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22863982854700974038092811 34295974282051461057139217)
            ·
              refine ⟨25721980711538595792854413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34295974282051461057139217 25721980711538595792854413)
              ·
                refine ⟨9645742766826973422320405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25721980711538595792854413 9645742766826973422320405)
                ·
                  refine ⟨452144192195014379171269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9645742766826973422320405 452144192195014379171269)
                  ·
                    rfl

theorem cell23_7924929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 2, 3, 6].length) (baseStart_7924929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7924929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7924929 prefixEnd_7924929 := by exact prefixLift 7924929
  have htrace : WordTrace (prefixWord ++ tailWord_7924929) baseStart_7924929 baseEnd_7924929 := by
    simpa [prefixWord, tailWord_7924929, baseEnd_7924929] using wordTrace_append hprefix tailTrace_7924929
  have hstable : (prefixWord ++ tailWord_7924929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7924929).length < 2 ^ (prefixWord ++ tailWord_7924929).sum := by decide
  have hdescent : baseEnd_7924929 < baseStart_7924929 := by decide
  rcases family_descends (prefixWord ++ tailWord_7924929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7924950 : List Nat := [5, 2, 1, 2, 2, 1, 2, 3, 1, 4]
def baseStart_7924950 : Nat := 118140960795 + 7924950 * 2 ^ 59
def prefixEnd_7924950 : Nat := 4983230072969 + 3 ^ 40 * 7924950 * 2
def baseEnd_7924950 : Nat := 1356436170949624610126275

theorem tailTrace_7924950 : CollatzResearch.WordTrace tailWord_7924950 prefixEnd_7924950 1356436170949624610126275 := by
  unfold tailWord_7924950
  simp only [CollatzResearch.WordTrace]
  refine ⟨18065417039954193659347769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 192697781759511399033042869 18065417039954193659347769)
  ·
    refine ⟨13549062779965645244510827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18065417039954193659347769 13549062779965645244510827)
    ·
      refine ⟨20323594169948467866766241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13549062779965645244510827 20323594169948467866766241)
      ·
        refine ⟨15242695627461350900074681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20323594169948467866766241 15242695627461350900074681)
        ·
          refine ⟨11432021720596013175056011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15242695627461350900074681 11432021720596013175056011)
          ·
            refine ⟨17148032580894019762584017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11432021720596013175056011 17148032580894019762584017)
            ·
              refine ⟨12861024435670514821938013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17148032580894019762584017 12861024435670514821938013)
              ·
                refine ⟨4822884163376443058226755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12861024435670514821938013 4822884163376443058226755)
                ·
                  refine ⟨7234326245064664587340133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4822884163376443058226755 7234326245064664587340133)
                  ·
                    refine ⟨1356436170949624610126275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7234326245064664587340133 1356436170949624610126275)
                    ·
                      rfl

theorem cell23_7924950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 2, 3, 1, 4].length) (baseStart_7924950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7924950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7924950 prefixEnd_7924950 := by exact prefixLift 7924950
  have htrace : WordTrace (prefixWord ++ tailWord_7924950) baseStart_7924950 baseEnd_7924950 := by
    simpa [prefixWord, tailWord_7924950, baseEnd_7924950] using wordTrace_append hprefix tailTrace_7924950
  have hstable : (prefixWord ++ tailWord_7924950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7924950).length < 2 ^ (prefixWord ++ tailWord_7924950).sum := by decide
  have hdescent : baseEnd_7924950 < baseStart_7924950 := by decide
  rcases family_descends (prefixWord ++ tailWord_7924950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7924959 : List Nat := [1, 1, 2, 3, 2, 1, 6, 1, 1, 5]
def baseStart_7924959 : Nat := 118140960795 + 7924959 * 2 ^ 59
def prefixEnd_7924959 : Nat := 4983230072969 + 3 ^ 40 * 7924959 * 2
def baseEnd_7924959 : Nat := 1356437711391588098388761

theorem tailTrace_7924959 : CollatzResearch.WordTrace tailWord_7924959 prefixEnd_7924959 1356437711391588098388761 := by
  unfold tailWord_7924959
  simp only [CollatzResearch.WordTrace]
  refine ⟨289047000896234493086641931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192698000597489662057761287 289047000896234493086641931)
  ·
    refine ⟨433570501344351739629962897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289047000896234493086641931 433570501344351739629962897)
    ·
      refine ⟨325177876008263804722472173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 433570501344351739629962897 325177876008263804722472173)
      ·
        refine ⟨121941703503098926770927065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 325177876008263804722472173 121941703503098926770927065)
        ·
          refine ⟨91456277627324195078195299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121941703503098926770927065 91456277627324195078195299)
          ·
            refine ⟨137184416440986292617292949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91456277627324195078195299 137184416440986292617292949)
            ·
              refine ⟨6430519520671232466435607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 137184416440986292617292949 6430519520671232466435607)
              ·
                refine ⟨9645779281006848699653411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6430519520671232466435607 9645779281006848699653411)
                ·
                  refine ⟨14468668921510273049480117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9645779281006848699653411 14468668921510273049480117)
                  ·
                    refine ⟨1356437711391588098388761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14468668921510273049480117 1356437711391588098388761)
                    ·
                      rfl

theorem cell23_7924959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 6, 1, 1, 5].length) (baseStart_7924959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7924959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7924959 prefixEnd_7924959 := by exact prefixLift 7924959
  have htrace : WordTrace (prefixWord ++ tailWord_7924959) baseStart_7924959 baseEnd_7924959 := by
    simpa [prefixWord, tailWord_7924959, baseEnd_7924959] using wordTrace_append hprefix tailTrace_7924959
  have hstable : (prefixWord ++ tailWord_7924959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7924959).length < 2 ^ (prefixWord ++ tailWord_7924959).sum := by decide
  have hdescent : baseEnd_7924959 < baseStart_7924959 := by decide
  rcases family_descends (prefixWord ++ tailWord_7924959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7924973 : List Nat := [1, 5, 1, 2, 2, 1, 2, 4, 1, 1, 3]
def baseStart_7924973 : Nat := 118140960795 + 7924973 * 2 ^ 59
def prefixEnd_7924973 : Nat := 4983230072969 + 3 ^ 40 * 7924973 * 2
def baseEnd_7924973 : Nat := 4069320322903927240391219

theorem tailTrace_7924973 : CollatzResearch.WordTrace tailWord_7924973 prefixEnd_7924973 4069320322903927240391219 := by
  unfold tailWord_7924973
  simp only [CollatzResearch.WordTrace]
  refine ⟨289047511518183773477651573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192698341012122515651767715 289047511518183773477651573)
  ·
    refine ⟨27098204204829728763529835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 289047511518183773477651573 27098204204829728763529835)
    ·
      refine ⟨40647306307244593145294753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27098204204829728763529835 40647306307244593145294753)
      ·
        refine ⟨30485479730433444858971065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40647306307244593145294753 30485479730433444858971065)
        ·
          refine ⟨22864109797825083644228299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30485479730433444858971065 22864109797825083644228299)
          ·
            refine ⟨34296164696737625466342449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22864109797825083644228299 34296164696737625466342449)
            ·
              refine ⟨25722123522553219099756837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34296164696737625466342449 25722123522553219099756837)
              ·
                refine ⟨4822898160478728581204407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25722123522553219099756837 4822898160478728581204407)
                ·
                  refine ⟨7234347240718092871806611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4822898160478728581204407 7234347240718092871806611)
                  ·
                    refine ⟨10851520861077139307709917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7234347240718092871806611 10851520861077139307709917)
                    ·
                      refine ⟨4069320322903927240391219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10851520861077139307709917 4069320322903927240391219)
                      ·
                        rfl

theorem cell23_7924973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 2, 4, 1, 1, 3].length) (baseStart_7924973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7924973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7924973 prefixEnd_7924973 := by exact prefixLift 7924973
  have htrace : WordTrace (prefixWord ++ tailWord_7924973) baseStart_7924973 baseEnd_7924973 := by
    simpa [prefixWord, tailWord_7924973, baseEnd_7924973] using wordTrace_append hprefix tailTrace_7924973
  have hstable : (prefixWord ++ tailWord_7924973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7924973).length < 2 ^ (prefixWord ++ tailWord_7924973).sum := by decide
  have hdescent : baseEnd_7924973 < baseStart_7924973 := by decide
  rcases family_descends (prefixWord ++ tailWord_7924973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7924980 : List Nat := [2, 6, 1, 2, 1, 1, 3, 1, 6]
def baseStart_7924980 : Nat := 118140960795 + 7924980 * 2 ^ 59
def prefixEnd_7924980 : Nat := 4983230072969 + 3 ^ 40 * 7924980 * 2
def baseEnd_7924980 : Nat := 452147101918723190333743

theorem tailTrace_7924980 : CollatzResearch.WordTrace tailWord_7924980 prefixEnd_7924980 452147101918723190333743 := by
  unfold tailWord_7924980
  simp only [CollatzResearch.WordTrace]
  refine ⟨144523883414579206836578197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192698511219438942448770929 144523883414579206836578197)
  ·
    refine ⟨6774557035058400320464603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 144523883414579206836578197 6774557035058400320464603)
    ·
      refine ⟨10161835552587600480696905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6774557035058400320464603 10161835552587600480696905)
      ·
        refine ⟨7621376664440700360522679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10161835552587600480696905 7621376664440700360522679)
        ·
          refine ⟨11432064996661050540784019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7621376664440700360522679 11432064996661050540784019)
          ·
            refine ⟨17148097494991575811176029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11432064996661050540784019 17148097494991575811176029)
            ·
              refine ⟨6430536560621840929191011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17148097494991575811176029 6430536560621840929191011)
              ·
                refine ⟨9645804840932761393786517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6430536560621840929191011 9645804840932761393786517)
                ·
                  refine ⟨452147101918723190333743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9645804840932761393786517 452147101918723190333743)
                  ·
                    rfl

theorem cell23_7924980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 3, 1, 6].length) (baseStart_7924980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7924980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7924980 prefixEnd_7924980 := by exact prefixLift 7924980
  have htrace : WordTrace (prefixWord ++ tailWord_7924980) baseStart_7924980 baseEnd_7924980 := by
    simpa [prefixWord, tailWord_7924980, baseEnd_7924980] using wordTrace_append hprefix tailTrace_7924980
  have hstable : (prefixWord ++ tailWord_7924980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7924980).length < 2 ^ (prefixWord ++ tailWord_7924980).sum := by decide
  have hdescent : baseEnd_7924980 < baseStart_7924980 := by decide
  rcases family_descends (prefixWord ++ tailWord_7924980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7924985 : List Nat := [1, 2, 1, 3, 1, 1, 4, 10]
def baseStart_7924985 : Nat := 118140960795 + 7924985 * 2 ^ 59
def prefixEnd_7924985 : Nat := 4983230072969 + 3 ^ 40 * 7924985 * 2
def baseEnd_7924985 : Nat := 150715795728584488645969

theorem tailTrace_7924985 : CollatzResearch.WordTrace tailWord_7924985 prefixEnd_7924985 150715795728584488645969 := by
  unfold tailWord_7924985
  simp only [CollatzResearch.WordTrace]
  refine ⟨289047949194140299527088409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192698632796093533018058939 289047949194140299527088409)
  ·
    refine ⟨216785961895605224645316307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 289047949194140299527088409 216785961895605224645316307)
    ·
      refine ⟨325178942843407836967974461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216785961895605224645316307 325178942843407836967974461)
      ·
        refine ⟨121942103566277938862990423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 325178942843407836967974461 121942103566277938862990423)
        ·
          refine ⟨182913155349416908294485635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121942103566277938862990423 182913155349416908294485635)
          ·
            refine ⟨274369733024125362441728453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182913155349416908294485635 274369733024125362441728453)
            ·
              refine ⟨51444324942023505457824085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 274369733024125362441728453 51444324942023505457824085)
              ·
                refine ⟨150715795728584488645969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 51444324942023505457824085 150715795728584488645969)
                ·
                  rfl

theorem cell23_7924985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 10].length) (baseStart_7924985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7924985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7924985 prefixEnd_7924985 := by exact prefixLift 7924985
  have htrace : WordTrace (prefixWord ++ tailWord_7924985) baseStart_7924985 baseEnd_7924985 := by
    simpa [prefixWord, tailWord_7924985, baseEnd_7924985] using wordTrace_append hprefix tailTrace_7924985
  have hstable : (prefixWord ++ tailWord_7924985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7924985).length < 2 ^ (prefixWord ++ tailWord_7924985).sum := by decide
  have hdescent : baseEnd_7924985 < baseStart_7924985 := by decide
  rcases family_descends (prefixWord ++ tailWord_7924985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7924996 : List Nat := [2, 3, 2, 2, 2, 2, 2, 2, 1, 1, 4]
def baseStart_7924996 : Nat := 118140960795 + 7924996 * 2 ^ 59
def prefixEnd_7924996 : Nat := 4983230072969 + 3 ^ 40 * 7924996 * 2
def baseEnd_7924996 : Nat := 4069332132958980650403613

theorem tailTrace_7924996 : CollatzResearch.WordTrace tailWord_7924996 prefixEnd_7924996 4069332132958980650403613 := by
  unfold tailWord_7924996
  simp only [CollatzResearch.WordTrace]
  refine ⟨144524175198550224202869421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192698900264733632270492561 144524175198550224202869421)
  ·
    refine ⟨54196565699456334076076033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144524175198550224202869421 54196565699456334076076033)
    ·
      refine ⟨40647424274592250557057025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54196565699456334076076033 40647424274592250557057025)
      ·
        refine ⟨30485568205944187917792769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40647424274592250557057025 30485568205944187917792769)
        ·
          refine ⟨22864176154458140938344577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30485568205944187917792769 22864176154458140938344577)
          ·
            refine ⟨17148132115843605703758433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22864176154458140938344577 17148132115843605703758433)
            ·
              refine ⟨12861099086882704277818825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17148132115843605703758433 12861099086882704277818825)
              ·
                refine ⟨9645824315162028208364119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12861099086882704277818825 9645824315162028208364119)
                ·
                  refine ⟨14468736472743042312546179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9645824315162028208364119 14468736472743042312546179)
                  ·
                    refine ⟨21703104709114563468819269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14468736472743042312546179 21703104709114563468819269)
                    ·
                      refine ⟨4069332132958980650403613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21703104709114563468819269 4069332132958980650403613)
                      ·
                        rfl

theorem cell23_7924996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 2, 2, 1, 1, 4].length) (baseStart_7924996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7924996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7924996 prefixEnd_7924996 := by exact prefixLift 7924996
  have htrace : WordTrace (prefixWord ++ tailWord_7924996) baseStart_7924996 baseEnd_7924996 := by
    simpa [prefixWord, tailWord_7924996, baseEnd_7924996] using wordTrace_append hprefix tailTrace_7924996
  have hstable : (prefixWord ++ tailWord_7924996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7924996).length < 2 ^ (prefixWord ++ tailWord_7924996).sum := by decide
  have hdescent : baseEnd_7924996 < baseStart_7924996 := by decide
  rcases family_descends (prefixWord ++ tailWord_7924996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7925039 : List Nat := [1, 1, 2, 1, 2, 1, 3, 4, 3, 3, 2]
def baseStart_7925039 : Nat := 118140960795 + 7925039 * 2 ^ 59
def prefixEnd_7925039 : Nat := 4983230072969 + 3 ^ 40 * 7925039 * 2
def baseEnd_7925039 : Nat := 4069354212627123982165915

theorem tailTrace_7925039 : CollatzResearch.WordTrace tailWord_7925039 prefixEnd_7925039 4069354212627123982165915 := by
  unfold tailWord_7925039
  simp only [CollatzResearch.WordTrace]
  refine ⟨289049918735944666749554171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192699945823963111166369447 289049918735944666749554171)
  ·
    refine ⟨433574878103917000124331257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289049918735944666749554171 433574878103917000124331257)
    ·
      refine ⟨325181158577937750093248443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 433574878103917000124331257 325181158577937750093248443)
      ·
        refine ⟨487771737866906625139872665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 325181158577937750093248443 487771737866906625139872665)
        ·
          refine ⟨365828803400179968854904499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 487771737866906625139872665 365828803400179968854904499)
          ·
            refine ⟨548743205100269953282356749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 365828803400179968854904499 548743205100269953282356749)
            ·
              refine ⟨205778701912601232480883781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 548743205100269953282356749 205778701912601232480883781)
              ·
                refine ⟨38583506608612731090165709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 205778701912601232480883781 38583506608612731090165709)
                ·
                  refine ⟨14468814978229774158812141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38583506608612731090165709 14468814978229774158812141)
                  ·
                    refine ⟨5425805616836165309554553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14468814978229774158812141 5425805616836165309554553)
                    ·
                      refine ⟨4069354212627123982165915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5425805616836165309554553 4069354212627123982165915)
                      ·
                        rfl

theorem cell23_7925039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 4, 3, 3, 2].length) (baseStart_7925039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7925039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7925039 prefixEnd_7925039 := by exact prefixLift 7925039
  have htrace : WordTrace (prefixWord ++ tailWord_7925039) baseStart_7925039 baseEnd_7925039 := by
    simpa [prefixWord, tailWord_7925039, baseEnd_7925039] using wordTrace_append hprefix tailTrace_7925039
  have hstable : (prefixWord ++ tailWord_7925039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7925039).length < 2 ^ (prefixWord ++ tailWord_7925039).sum := by decide
  have hdescent : baseEnd_7925039 < baseStart_7925039 := by decide
  rcases family_descends (prefixWord ++ tailWord_7925039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7925072 : List Nat := [2, 1, 1, 1, 1, 5, 1, 3, 2, 1, 5]
def baseStart_7925072 : Nat := 118140960795 + 7925072 * 2 ^ 59
def prefixEnd_7925072 : Nat := 4983230072969 + 3 ^ 40 * 7925072 * 2
def baseEnd_7925072 : Nat := 4069371157488722353053263

theorem tailTrace_7925072 : CollatzResearch.WordTrace tailWord_7925072 prefixEnd_7925072 4069371157488722353053263 := by
  unfold tailWord_7925072
  simp only [CollatzResearch.WordTrace]
  refine ⟨144525561172412556692752735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192700748229883408923670313 144525561172412556692752735)
  ·
    refine ⟨216788341758618835039129103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144525561172412556692752735 216788341758618835039129103)
    ·
      refine ⟨325182512637928252558693655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216788341758618835039129103 325182512637928252558693655)
      ·
        refine ⟨487773768956892378838040483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 325182512637928252558693655 487773768956892378838040483)
        ·
          refine ⟨731660653435338568257060725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 487773768956892378838040483 731660653435338568257060725)
          ·
            refine ⟨68593186259562990774099443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 731660653435338568257060725 68593186259562990774099443)
            ·
              refine ⟨102889779389344486161149165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68593186259562990774099443 102889779389344486161149165)
              ·
                refine ⟨38583667271004182310430937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 102889779389344486161149165 38583667271004182310430937)
                ·
                  refine ⟨28937750453253136732823203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38583667271004182310430937 28937750453253136732823203)
                  ·
                    refine ⟨43406625679879705099234805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28937750453253136732823203 43406625679879705099234805)
                    ·
                      refine ⟨4069371157488722353053263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43406625679879705099234805 4069371157488722353053263)
                      ·
                        rfl

theorem cell23_7925072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 3, 2, 1, 5].length) (baseStart_7925072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7925072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7925072 prefixEnd_7925072 := by exact prefixLift 7925072
  have htrace : WordTrace (prefixWord ++ tailWord_7925072) baseStart_7925072 baseEnd_7925072 := by
    simpa [prefixWord, tailWord_7925072, baseEnd_7925072] using wordTrace_append hprefix tailTrace_7925072
  have hstable : (prefixWord ++ tailWord_7925072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7925072).length < 2 ^ (prefixWord ++ tailWord_7925072).sum := by decide
  have hdescent : baseEnd_7925072 < baseStart_7925072 := by decide
  rcases family_descends (prefixWord ++ tailWord_7925072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7925073 : List Nat := [1, 2, 2, 1, 4, 1, 5, 1, 1, 3, 2]
def baseStart_7925073 : Nat := 118140960795 + 7925073 * 2 ^ 59
def prefixEnd_7925073 : Nat := 4983230072969 + 3 ^ 40 * 7925073 * 2
def baseEnd_7925073 : Nat := 4069371670969376849140759

theorem tailTrace_7925073 : CollatzResearch.WordTrace tailWord_7925073 prefixEnd_7925073 4069371670969376849140759 := by
  unfold tailWord_7925073
  simp only [CollatzResearch.WordTrace]
  refine ⟨289051158817821490556291873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192700772545214327037527915 289051158817821490556291873)
  ·
    refine ⟨216788369113366117917218905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 289051158817821490556291873 216788369113366117917218905)
    ·
      refine ⟨162591276835024588437914179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216788369113366117917218905 162591276835024588437914179)
      ·
        refine ⟨243886915252536882656871269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162591276835024588437914179 243886915252536882656871269)
        ·
          refine ⟨45728796609850665498163363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 243886915252536882656871269 45728796609850665498163363)
          ·
            refine ⟨68593194914775998247245045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45728796609850665498163363 68593194914775998247245045)
            ·
              refine ⟨6430612023260249835679223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 68593194914775998247245045 6430612023260249835679223)
              ·
                refine ⟨9645918034890374753518835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6430612023260249835679223 9645918034890374753518835)
                ·
                  refine ⟨14468877052335562130278253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9645918034890374753518835 14468877052335562130278253)
                  ·
                    refine ⟨5425828894625835798854345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14468877052335562130278253 5425828894625835798854345)
                    ·
                      refine ⟨4069371670969376849140759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5425828894625835798854345 4069371670969376849140759)
                      ·
                        rfl

theorem cell23_7925073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 5, 1, 1, 3, 2].length) (baseStart_7925073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7925073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7925073 prefixEnd_7925073 := by exact prefixLift 7925073
  have htrace : WordTrace (prefixWord ++ tailWord_7925073) baseStart_7925073 baseEnd_7925073 := by
    simpa [prefixWord, tailWord_7925073, baseEnd_7925073] using wordTrace_append hprefix tailTrace_7925073
  have hstable : (prefixWord ++ tailWord_7925073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7925073).length < 2 ^ (prefixWord ++ tailWord_7925073).sum := by decide
  have hdescent : baseEnd_7925073 < baseStart_7925073 := by decide
  rcases family_descends (prefixWord ++ tailWord_7925073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7925159 : List Nat := [1, 1, 6, 1, 1, 1, 1, 1, 3, 3, 4]
def baseStart_7925159 : Nat := 118140960795 + 7925159 * 2 ^ 59
def prefixEnd_7925159 : Nat := 4983230072969 + 3 ^ 40 * 7925159 * 2
def baseEnd_7925159 : Nat := 4069415830305663512665363

theorem tailTrace_7925159 : CollatzResearch.WordTrace tailWord_7925159 prefixEnd_7925159 4069415830305663512665363 := by
  unfold tailWord_7925159
  simp only [CollatzResearch.WordTrace]
  refine ⟨289054295495509927243922531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192702863663673284829281687 289054295495509927243922531)
  ·
    refine ⟨433581443243264890865883797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289054295495509927243922531 433581443243264890865883797)
    ·
      refine ⟨20324130152028041759338303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 433581443243264890865883797 20324130152028041759338303)
      ·
        refine ⟨30486195228042062639007455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20324130152028041759338303 30486195228042062639007455)
        ·
          refine ⟨45729292842063093958511183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30486195228042062639007455 45729292842063093958511183)
          ·
            refine ⟨68593939263094640937766775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45729292842063093958511183 68593939263094640937766775)
            ·
              refine ⟨102890908894641961406650163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68593939263094640937766775 102890908894641961406650163)
              ·
                refine ⟨154336363341962942109975245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102890908894641961406650163 154336363341962942109975245)
                ·
                  refine ⟨57876136253236103291240717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 154336363341962942109975245 57876136253236103291240717)
                  ·
                    refine ⟨21703551094963538734215269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 57876136253236103291240717 21703551094963538734215269)
                    ·
                      refine ⟨4069415830305663512665363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21703551094963538734215269 4069415830305663512665363)
                      ·
                        rfl

theorem cell23_7925159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 1, 3, 3, 4].length) (baseStart_7925159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7925159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7925159 prefixEnd_7925159 := by exact prefixLift 7925159
  have htrace : WordTrace (prefixWord ++ tailWord_7925159) baseStart_7925159 baseEnd_7925159 := by
    simpa [prefixWord, tailWord_7925159, baseEnd_7925159] using wordTrace_append hprefix tailTrace_7925159
  have hstable : (prefixWord ++ tailWord_7925159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7925159).length < 2 ^ (prefixWord ++ tailWord_7925159).sum := by decide
  have hdescent : baseEnd_7925159 < baseStart_7925159 := by decide
  rcases family_descends (prefixWord ++ tailWord_7925159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7925196 : List Nat := [2, 2, 1, 4, 2, 1, 1, 1, 4, 2, 3]
def baseStart_7925196 : Nat := 118140960795 + 7925196 * 2 ^ 59
def prefixEnd_7925196 : Nat := 4983230072969 + 3 ^ 40 * 7925196 * 2
def baseEnd_7925196 : Nat := 4069434829089879867902693

theorem tailTrace_7925196 : CollatzResearch.WordTrace tailWord_7925196 prefixEnd_7925196 4069434829089879867902693 := by
  unfold tailWord_7925196
  simp only [CollatzResearch.WordTrace]
  refine ⟨144527822498187941281509721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192703763330917255042012961 144527822498187941281509721)
  ·
    refine ⟨108395866873640955961132291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144527822498187941281509721 108395866873640955961132291)
    ·
      refine ⟨162593800310461433941698437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108395866873640955961132291 162593800310461433941698437)
      ·
        refine ⟨30486337558211518864068457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 162593800310461433941698437 30486337558211518864068457)
        ·
          refine ⟨22864753168658639148051343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30486337558211518864068457 22864753168658639148051343)
          ·
            refine ⟨34297129752987958722077015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22864753168658639148051343 34297129752987958722077015)
            ·
              refine ⟨51445694629481938083115523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34297129752987958722077015 51445694629481938083115523)
              ·
                refine ⟨77168541944222907124673285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51445694629481938083115523 77168541944222907124673285)
                ·
                  refine ⟨14469101614541795085876241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 77168541944222907124673285 14469101614541795085876241)
                  ·
                    refine ⟨10851826210906346314407181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14469101614541795085876241 10851826210906346314407181)
                    ·
                      refine ⟨4069434829089879867902693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10851826210906346314407181 4069434829089879867902693)
                      ·
                        rfl

theorem cell23_7925196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 1, 4, 2, 3].length) (baseStart_7925196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7925196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7925196 prefixEnd_7925196 := by exact prefixLift 7925196
  have htrace : WordTrace (prefixWord ++ tailWord_7925196) baseStart_7925196 baseEnd_7925196 := by
    simpa [prefixWord, tailWord_7925196, baseEnd_7925196] using wordTrace_append hprefix tailTrace_7925196
  have hstable : (prefixWord ++ tailWord_7925196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7925196).length < 2 ^ (prefixWord ++ tailWord_7925196).sum := by decide
  have hdescent : baseEnd_7925196 < baseStart_7925196 := by decide
  rcases family_descends (prefixWord ++ tailWord_7925196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7925276 : List Nat := [2, 2, 3, 1, 2, 1, 4, 1, 1, 6]
def baseStart_7925276 : Nat := 118140960795 + 7925276 * 2 ^ 59
def prefixEnd_7925276 : Nat := 4983230072969 + 3 ^ 40 * 7925276 * 2
def baseEnd_7925276 : Nat := 1356491969180746518300775

theorem tailTrace_7925276 : CollatzResearch.WordTrace tailWord_7925276 prefixEnd_7925276 1356491969180746518300775 := by
  unfold tailWord_7925276
  simp only [CollatzResearch.WordTrace]
  refine ⟨144529281418043028112965841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192705708557390704150621121 144529281418043028112965841)
  ·
    refine ⟨108396961063532271084724381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144529281418043028112965841 108396961063532271084724381)
    ·
      refine ⟨40648860398824601656771643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108396961063532271084724381 40648860398824601656771643)
      ·
        refine ⟨60973290598236902485157465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40648860398824601656771643 60973290598236902485157465)
        ·
          refine ⟨45729967948677676863868099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60973290598236902485157465 45729967948677676863868099)
          ·
            refine ⟨68594951923016515295802149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45729967948677676863868099 68594951923016515295802149)
            ·
              refine ⟨12861553485565596617962903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68594951923016515295802149 12861553485565596617962903)
              ·
                refine ⟨19292330228348394926944355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12861553485565596617962903 19292330228348394926944355)
                ·
                  refine ⟨28938495342522592390416533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19292330228348394926944355 28938495342522592390416533)
                  ·
                    refine ⟨1356491969180746518300775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28938495342522592390416533 1356491969180746518300775)
                    ·
                      rfl

theorem cell23_7925276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 4, 1, 1, 6].length) (baseStart_7925276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7925276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7925276 prefixEnd_7925276 := by exact prefixLift 7925276
  have htrace : WordTrace (prefixWord ++ tailWord_7925276) baseStart_7925276 baseEnd_7925276 := by
    simpa [prefixWord, tailWord_7925276, baseEnd_7925276] using wordTrace_append hprefix tailTrace_7925276
  have hstable : (prefixWord ++ tailWord_7925276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7925276).length < 2 ^ (prefixWord ++ tailWord_7925276).sum := by decide
  have hdescent : baseEnd_7925276 < baseStart_7925276 := by decide
  rcases family_descends (prefixWord ++ tailWord_7925276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7925279 : List Nat := [1, 1, 2, 4, 1, 1, 2, 3, 1, 1, 6]
def baseStart_7925279 : Nat := 118140960795 + 7925279 * 2 ^ 59
def prefixEnd_7925279 : Nat := 4983230072969 + 3 ^ 40 * 7925279 * 2
def baseEnd_7925279 : Nat := 4069477447984203043164811

theorem tailTrace_7925279 : CollatzResearch.WordTrace tailWord_7925279 prefixEnd_7925279 4069477447984203043164811 := by
  unfold tailWord_7925279
  simp only [CollatzResearch.WordTrace]
  refine ⟨289058672255075187738290891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192705781503383458492193927 289058672255075187738290891)
  ·
    refine ⟨433588008382612781607436337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289058672255075187738290891 433588008382612781607436337)
    ·
      refine ⟨325191006286959586205577253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 433588008382612781607436337 325191006286959586205577253)
      ·
        refine ⟨60973313678804922413545735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 325191006286959586205577253 60973313678804922413545735)
        ·
          refine ⟨91459970518207383620318603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60973313678804922413545735 91459970518207383620318603)
          ·
            refine ⟨137189955777311075430477905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91459970518207383620318603 137189955777311075430477905)
            ·
              refine ⟨102892466832983306572858429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137189955777311075430477905 102892466832983306572858429)
              ·
                refine ⟨38584675062368739964821911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 102892466832983306572858429 38584675062368739964821911)
                ·
                  refine ⟨57877012593553109947232867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38584675062368739964821911 57877012593553109947232867)
                  ·
                    refine ⟨86815518890329664920849301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 57877012593553109947232867 86815518890329664920849301)
                    ·
                      refine ⟨4069477447984203043164811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 86815518890329664920849301 4069477447984203043164811)
                      ·
                        rfl

theorem cell23_7925279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 3, 1, 1, 6].length) (baseStart_7925279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7925279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7925279 prefixEnd_7925279 := by exact prefixLift 7925279
  have htrace : WordTrace (prefixWord ++ tailWord_7925279) baseStart_7925279 baseEnd_7925279 := by
    simpa [prefixWord, tailWord_7925279, baseEnd_7925279] using wordTrace_append hprefix tailTrace_7925279
  have hstable : (prefixWord ++ tailWord_7925279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7925279).length < 2 ^ (prefixWord ++ tailWord_7925279).sum := by decide
  have hdescent : baseEnd_7925279 < baseStart_7925279 := by decide
  rcases family_descends (prefixWord ++ tailWord_7925279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7925303 : List Nat := [1, 1, 3, 1, 2, 5, 1, 3, 1, 2, 3]
def baseStart_7925303 : Nat := 118140960795 + 7925303 * 2 ^ 59
def prefixEnd_7925303 : Nat := 4983230072969 + 3 ^ 40 * 7925303 * 2
def baseEnd_7925303 : Nat := 4069489771519910949264701

theorem tailTrace_7925303 : CollatzResearch.WordTrace tailWord_7925303 prefixEnd_7925303 4069489771519910949264701 := by
  unfold tailWord_7925303
  simp only [CollatzResearch.WordTrace]
  refine ⟨289059547606988239837164563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192706365071325493224776375 289059547606988239837164563)
  ·
    refine ⟨433589321410482359755746845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289059547606988239837164563 433589321410482359755746845)
    ·
      refine ⟨162595995528930884908405067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 433589321410482359755746845 162595995528930884908405067)
      ·
        refine ⟨243893993293396327362607601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162595995528930884908405067 243893993293396327362607601)
        ·
          refine ⟨182920494970047245521955701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 243893993293396327362607601 182920494970047245521955701)
          ·
            refine ⟨17148796403441929267683347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 182920494970047245521955701 17148796403441929267683347)
            ·
              refine ⟨25723194605162893901525021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17148796403441929267683347 25723194605162893901525021)
              ·
                refine ⟨9646197976936085213071883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25723194605162893901525021 9646197976936085213071883)
                ·
                  refine ⟨14469296965404127819607825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9646197976936085213071883 14469296965404127819607825)
                  ·
                    refine ⟨10851972724053095864705869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14469296965404127819607825 10851972724053095864705869)
                    ·
                      refine ⟨4069489771519910949264701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10851972724053095864705869 4069489771519910949264701)
                      ·
                        rfl

theorem cell23_7925303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 1, 3, 1, 2, 3].length) (baseStart_7925303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7925303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7925303 prefixEnd_7925303 := by exact prefixLift 7925303
  have htrace : WordTrace (prefixWord ++ tailWord_7925303) baseStart_7925303 baseEnd_7925303 := by
    simpa [prefixWord, tailWord_7925303, baseEnd_7925303] using wordTrace_append hprefix tailTrace_7925303
  have hstable : (prefixWord ++ tailWord_7925303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7925303).length < 2 ^ (prefixWord ++ tailWord_7925303).sum := by decide
  have hdescent : baseEnd_7925303 < baseStart_7925303 := by decide
  rcases family_descends (prefixWord ++ tailWord_7925303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7925334 : List Nat := [5, 2, 2, 2, 1, 1, 2, 2, 1, 1, 4]
def baseStart_7925334 : Nat := 118140960795 + 7925334 * 2 ^ 59
def prefixEnd_7925334 : Nat := 4983230072969 + 3 ^ 40 * 7925334 * 2
def baseEnd_7925334 : Nat := 4069505689420200327977059

theorem tailTrace_7925334 : CollatzResearch.WordTrace tailWord_7925334 prefixEnd_7925334 4069505689420200327977059 := by
  unfold tailWord_7925334
  simp only [CollatzResearch.WordTrace]
  refine ⟨18066292391867245758221441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 192707118846583954754362037 18066292391867245758221441)
  ·
    refine ⟨13549719293900434318666081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18066292391867245758221441 13549719293900434318666081)
    ·
      refine ⟨10162289470425325738999561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13549719293900434318666081 10162289470425325738999561)
      ·
        refine ⟨7621717102818994304249671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10162289470425325738999561 7621717102818994304249671)
        ·
          refine ⟨11432575654228491456374507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7621717102818994304249671 11432575654228491456374507)
          ·
            refine ⟨17148863481342737184561761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11432575654228491456374507 17148863481342737184561761)
            ·
              refine ⟨12861647611007052888421321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17148863481342737184561761 12861647611007052888421321)
              ·
                refine ⟨9646235708255289666315991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12861647611007052888421321 9646235708255289666315991)
                ·
                  refine ⟨14469353562382934499473987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9646235708255289666315991 14469353562382934499473987)
                  ·
                    refine ⟨21704030343574401749210981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14469353562382934499473987 21704030343574401749210981)
                    ·
                      refine ⟨4069505689420200327977059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21704030343574401749210981 4069505689420200327977059)
                      ·
                        rfl

theorem cell23_7925334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 2, 2, 1, 1, 4].length) (baseStart_7925334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7925334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7925334 prefixEnd_7925334 := by exact prefixLift 7925334
  have htrace : WordTrace (prefixWord ++ tailWord_7925334) baseStart_7925334 baseEnd_7925334 := by
    simpa [prefixWord, tailWord_7925334, baseEnd_7925334] using wordTrace_append hprefix tailTrace_7925334
  have hstable : (prefixWord ++ tailWord_7925334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7925334).length < 2 ^ (prefixWord ++ tailWord_7925334).sum := by decide
  have hdescent : baseEnd_7925334 < baseStart_7925334 := by decide
  rcases family_descends (prefixWord ++ tailWord_7925334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7925360 : List Nat := [2, 1, 1, 1, 6, 1, 2, 3, 1, 3, 2]
def baseStart_7925360 : Nat := 118140960795 + 7925360 * 2 ^ 59
def prefixEnd_7925360 : Nat := 4983230072969 + 3 ^ 40 * 7925360 * 2
def baseEnd_7925360 : Nat := 4069519039917217226251939

theorem tailTrace_7925360 : CollatzResearch.WordTrace tailWord_7925360 prefixEnd_7925360 4069519039917217226251939 := by
  unfold tailWord_7925360
  simp only [CollatzResearch.WordTrace]
  refine ⟨144530813283890869285994767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192707751045187825714659689 144530813283890869285994767)
  ·
    refine ⟨216796219925836303928992151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144530813283890869285994767 216796219925836303928992151)
    ·
      refine ⟨325194329888754455893488227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216796219925836303928992151 325194329888754455893488227)
      ·
        refine ⟨487791494833131683840232341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 325194329888754455893488227 487791494833131683840232341)
        ·
          refine ⟨22865226320303047680010891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 487791494833131683840232341 22865226320303047680010891)
          ·
            refine ⟨34297839480454571520016337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22865226320303047680010891 34297839480454571520016337)
            ·
              refine ⟨25723379610340928640012253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34297839480454571520016337 25723379610340928640012253)
              ·
                refine ⟨9646267353877848240004595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25723379610340928640012253 9646267353877848240004595)
                ·
                  refine ⟨14469401030816772360006893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9646267353877848240004595 14469401030816772360006893)
                  ·
                    refine ⟨5426025386556289635002585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14469401030816772360006893 5426025386556289635002585)
                    ·
                      refine ⟨4069519039917217226251939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5426025386556289635002585 4069519039917217226251939)
                      ·
                        rfl

theorem cell23_7925360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 2, 3, 1, 3, 2].length) (baseStart_7925360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7925360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7925360 prefixEnd_7925360 := by exact prefixLift 7925360
  have htrace : WordTrace (prefixWord ++ tailWord_7925360) baseStart_7925360 baseEnd_7925360 := by
    simpa [prefixWord, tailWord_7925360, baseEnd_7925360] using wordTrace_append hprefix tailTrace_7925360
  have hstable : (prefixWord ++ tailWord_7925360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7925360).length < 2 ^ (prefixWord ++ tailWord_7925360).sum := by decide
  have hdescent : baseEnd_7925360 < baseStart_7925360 := by decide
  rcases family_descends (prefixWord ++ tailWord_7925360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7925376 : List Nat := [2, 1, 1, 2, 1, 4, 2, 1, 2, 4, 3]
def baseStart_7925376 : Nat := 118140960795 + 7925376 * 2 ^ 59
def prefixEnd_7925376 : Nat := 4983230072969 + 3 ^ 40 * 7925376 * 2
def baseEnd_7925376 : Nat := 4069527255607689163651865

theorem tailTrace_7925376 : CollatzResearch.WordTrace tailWord_7925376 prefixEnd_7925376 4069527255607689163651865 := by
  unfold tailWord_7925376
  simp only [CollatzResearch.WordTrace]
  refine ⟨144531105067861886652285991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192708140090482515536381321 144531105067861886652285991)
  ·
    refine ⟨216796657601792829978428987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144531105067861886652285991 216796657601792829978428987)
    ·
      refine ⟨325194986402689244967643481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216796657601792829978428987 325194986402689244967643481)
      ·
        refine ⟨243896239802016933725732611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 325194986402689244967643481 243896239802016933725732611)
        ·
          refine ⟨365844359703025400588598917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 243896239802016933725732611 365844359703025400588598917)
          ·
            refine ⟨68595817444317262610362297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 365844359703025400588598917 68595817444317262610362297)
            ·
              refine ⟨51446863083237946957771723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68595817444317262610362297 51446863083237946957771723)
              ·
                refine ⟨77170294624856920436657585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51446863083237946957771723 77170294624856920436657585)
                ·
                  refine ⟨57877720968642690327493189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77170294624856920436657585 57877720968642690327493189)
                  ·
                    refine ⟨10852072681620504436404973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 57877720968642690327493189 10852072681620504436404973)
                    ·
                      refine ⟨4069527255607689163651865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10852072681620504436404973 4069527255607689163651865)
                      ·
                        rfl

theorem cell23_7925376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 1, 2, 4, 3].length) (baseStart_7925376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7925376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7925376 prefixEnd_7925376 := by exact prefixLift 7925376
  have htrace : WordTrace (prefixWord ++ tailWord_7925376) baseStart_7925376 baseEnd_7925376 := by
    simpa [prefixWord, tailWord_7925376, baseEnd_7925376] using wordTrace_append hprefix tailTrace_7925376
  have hstable : (prefixWord ++ tailWord_7925376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7925376).length < 2 ^ (prefixWord ++ tailWord_7925376).sum := by decide
  have hdescent : baseEnd_7925376 < baseStart_7925376 := by decide
  rcases family_descends (prefixWord ++ tailWord_7925376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7925394 : List Nat := [3, 2, 3, 1, 3, 2, 1, 2, 1, 3, 2]
def baseStart_7925394 : Nat := 118140960795 + 7925394 * 2 ^ 59
def prefixEnd_7925394 : Nat := 4983230072969 + 3 ^ 40 * 7925394 * 2
def baseEnd_7925394 : Nat := 4069536498259470093226783

theorem tailTrace_7925394 : CollatzResearch.WordTrace tailWord_7925394 prefixEnd_7925394 4069536498259470093226783 := by
  unfold tailWord_7925394
  simp only [CollatzResearch.WordTrace]
  refine ⟨72265716662414640594681809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192708577766439041585818157 72265716662414640594681809)
  ·
    refine ⟨54199287496810980446011357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72265716662414640594681809 54199287496810980446011357)
    ·
      refine ⟨20324732811304117667254259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54199287496810980446011357 20324732811304117667254259)
      ·
        refine ⟨30487099216956176500881389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20324732811304117667254259 30487099216956176500881389)
        ·
          refine ⟨11432662206358566187830521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30487099216956176500881389 11432662206358566187830521)
          ·
            refine ⟨8574496654768924640872891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11432662206358566187830521 8574496654768924640872891)
            ·
              refine ⟨12861744982153386961309337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8574496654768924640872891 12861744982153386961309337)
              ·
                refine ⟨9646308736615040220982003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12861744982153386961309337 9646308736615040220982003)
                ·
                  refine ⟨14469463104922560331473005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9646308736615040220982003 14469463104922560331473005)
                  ·
                    refine ⟨5426048664345960124302377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14469463104922560331473005 5426048664345960124302377)
                    ·
                      refine ⟨4069536498259470093226783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5426048664345960124302377 4069536498259470093226783)
                      ·
                        rfl

theorem cell23_7925394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 2, 1, 2, 1, 3, 2].length) (baseStart_7925394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7925394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7925394 prefixEnd_7925394 := by exact prefixLift 7925394
  have htrace : WordTrace (prefixWord ++ tailWord_7925394) baseStart_7925394 baseEnd_7925394 := by
    simpa [prefixWord, tailWord_7925394, baseEnd_7925394] using wordTrace_append hprefix tailTrace_7925394
  have hstable : (prefixWord ++ tailWord_7925394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7925394).length < 2 ^ (prefixWord ++ tailWord_7925394).sum := by decide
  have hdescent : baseEnd_7925394 < baseStart_7925394 := by decide
  rcases family_descends (prefixWord ++ tailWord_7925394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7925407 : List Nat := [1, 1, 2, 7, 1, 1, 1, 2, 1, 4, 2]
def baseStart_7925407 : Nat := 118140960795 + 7925407 * 2 ^ 59
def prefixEnd_7925407 : Nat := 4983230072969 + 3 ^ 40 * 7925407 * 2
def baseEnd_7925407 : Nat := 4069543173507978542364223

theorem tailTrace_7925407 : CollatzResearch.WordTrace tailWord_7925407 prefixEnd_7925407 4069543173507978542364223 := by
  unfold tailWord_7925407
  simp only [CollatzResearch.WordTrace]
  refine ⟨289063340798611465598950475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192708893865740977065966983 289063340798611465598950475)
  ·
    refine ⟨433595011197917198398425713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289063340798611465598950475 433595011197917198398425713)
    ·
      refine ⟨325196258398437898798819285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 433595011197917198398425713 325196258398437898798819285)
      ·
        refine ⟨7621787306213388253097327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 325196258398437898798819285 7621787306213388253097327)
        ·
          refine ⟨11432680959320082379645991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7621787306213388253097327 11432680959320082379645991)
          ·
            refine ⟨17149021438980123569468987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11432680959320082379645991 17149021438980123569468987)
            ·
              refine ⟨25723532158470185354203481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17149021438980123569468987 25723532158470185354203481)
              ·
                refine ⟨19292649118852639015652611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25723532158470185354203481 19292649118852639015652611)
                ·
                  refine ⟨28938973678278958523478917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19292649118852639015652611 28938973678278958523478917)
                  ·
                    refine ⟨5426057564677304723152297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28938973678278958523478917 5426057564677304723152297)
                    ·
                      refine ⟨4069543173507978542364223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5426057564677304723152297 4069543173507978542364223)
                      ·
                        rfl

theorem cell23_7925407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 1, 2, 1, 4, 2].length) (baseStart_7925407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7925407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7925407 prefixEnd_7925407 := by exact prefixLift 7925407
  have htrace : WordTrace (prefixWord ++ tailWord_7925407) baseStart_7925407 baseEnd_7925407 := by
    simpa [prefixWord, tailWord_7925407, baseEnd_7925407] using wordTrace_append hprefix tailTrace_7925407
  have hstable : (prefixWord ++ tailWord_7925407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7925407).length < 2 ^ (prefixWord ++ tailWord_7925407).sum := by decide
  have hdescent : baseEnd_7925407 < baseStart_7925407 := by decide
  rcases family_descends (prefixWord ++ tailWord_7925407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7925433 : List Nat := [1, 2, 1, 4, 1, 1, 3, 1, 2, 5, 2]
def baseStart_7925433 : Nat := 118140960795 + 7925433 * 2 ^ 59
def prefixEnd_7925433 : Nat := 4983230072969 + 3 ^ 40 * 7925433 * 2
def baseEnd_7925433 : Nat := 4069556524004995440639103

theorem tailTrace_7925433 : CollatzResearch.WordTrace tailWord_7925433 prefixEnd_7925433 4069556524004995440639103 := by
  unfold tailWord_7925433
  simp only [CollatzResearch.WordTrace]
  refine ⟨289064289096517272039396953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192709526064344848026264635 289064289096517272039396953)
  ·
    refine ⟨216798216822387954029547715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 289064289096517272039396953 216798216822387954029547715)
    ·
      refine ⟨325197325233581931044321573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216798216822387954029547715 325197325233581931044321573)
      ·
        refine ⟨60974498481296612070810295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 325197325233581931044321573 60974498481296612070810295)
        ·
          refine ⟨91461747721944918106215443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60974498481296612070810295 91461747721944918106215443)
          ·
            refine ⟨137192621582917377159323165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91461747721944918106215443 137192621582917377159323165)
            ·
              refine ⟨51447233093594016434746187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 137192621582917377159323165 51447233093594016434746187)
              ·
                refine ⟨77170849640391024652119281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51447233093594016434746187 77170849640391024652119281)
                ·
                  refine ⟨57878137230293268489089461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77170849640391024652119281 57878137230293268489089461)
                  ·
                    refine ⟨5426075365339993920852137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 57878137230293268489089461 5426075365339993920852137)
                    ·
                      refine ⟨4069556524004995440639103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5426075365339993920852137 4069556524004995440639103)
                      ·
                        rfl

theorem cell23_7925433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 1, 2, 5, 2].length) (baseStart_7925433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7925433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7925433 prefixEnd_7925433 := by exact prefixLift 7925433
  have htrace : WordTrace (prefixWord ++ tailWord_7925433) baseStart_7925433 baseEnd_7925433 := by
    simpa [prefixWord, tailWord_7925433, baseEnd_7925433] using wordTrace_append hprefix tailTrace_7925433
  have hstable : (prefixWord ++ tailWord_7925433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7925433).length < 2 ^ (prefixWord ++ tailWord_7925433).sum := by decide
  have hdescent : baseEnd_7925433 < baseStart_7925433 := by decide
  rcases family_descends (prefixWord ++ tailWord_7925433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7925460 : List Nat := [2, 4, 1, 3, 1, 1, 3, 1, 2, 5]
def baseStart_7925460 : Nat := 118140960795 + 7925460 * 2 ^ 59
def prefixEnd_7925460 : Nat := 4983230072969 + 3 ^ 40 * 7925460 * 2
def baseEnd_7925460 : Nat := 1356523462660888945000493

theorem tailTrace_7925460 : CollatzResearch.WordTrace tailWord_7925460 prefixEnd_7925460 1356523462660888945000493 := by
  unfold tailWord_7925460
  simp only [CollatzResearch.WordTrace]
  refine ⟨144532636933709727825314917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192710182578279637100419889 144532636933709727825314917)
  ·
    refine ⟨27099869425070573967246547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 144532636933709727825314917 27099869425070573967246547)
    ·
      refine ⟨40649804137605860950869821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27099869425070573967246547 40649804137605860950869821)
      ·
        refine ⟨15243676551602197856576183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40649804137605860950869821 15243676551602197856576183)
        ·
          refine ⟨22865514827403296784864275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15243676551602197856576183 22865514827403296784864275)
          ·
            refine ⟨34298272241104945177296413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22865514827403296784864275 34298272241104945177296413)
            ·
              refine ⟨12861852090414354441486155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34298272241104945177296413 12861852090414354441486155)
              ·
                refine ⟨19292778135621531662229233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12861852090414354441486155 19292778135621531662229233)
                ·
                  refine ⟨14469583601716148746671925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19292778135621531662229233 14469583601716148746671925)
                  ·
                    refine ⟨1356523462660888945000493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14469583601716148746671925 1356523462660888945000493)
                    ·
                      rfl

theorem cell23_7925460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 3, 1, 2, 5].length) (baseStart_7925460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7925460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7925460 prefixEnd_7925460 := by exact prefixLift 7925460
  have htrace : WordTrace (prefixWord ++ tailWord_7925460) baseStart_7925460 baseEnd_7925460 := by
    simpa [prefixWord, tailWord_7925460, baseEnd_7925460] using wordTrace_append hprefix tailTrace_7925460
  have hstable : (prefixWord ++ tailWord_7925460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7925460).length < 2 ^ (prefixWord ++ tailWord_7925460).sum := by decide
  have hdescent : baseEnd_7925460 < baseStart_7925460 := by decide
  rcases family_descends (prefixWord ++ tailWord_7925460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7925463 : List Nat := [1, 1, 3, 2, 1, 3, 1, 2, 1, 6, 2]
def baseStart_7925463 : Nat := 118140960795 + 7925463 * 2 ^ 59
def prefixEnd_7925463 : Nat := 4983230072969 + 3 ^ 40 * 7925463 * 2
def baseEnd_7925463 : Nat := 4069571928424630323263965

theorem tailTrace_7925463 : CollatzResearch.WordTrace tailWord_7925463 prefixEnd_7925463 4069571928424630323263965 := by
  unfold tailWord_7925463
  simp only [CollatzResearch.WordTrace]
  refine ⟨289065383286408587162989043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192710255524272391441992695 289065383286408587162989043)
  ·
    refine ⟨433598074929612880744483565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289065383286408587162989043 433598074929612880744483565)
    ·
      refine ⟨162599278098604830279181337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 433598074929612880744483565 162599278098604830279181337)
      ·
        refine ⟨121949458573953622709386003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162599278098604830279181337 121949458573953622709386003)
        ·
          refine ⟨182924187860930434064079005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121949458573953622709386003 182924187860930434064079005)
          ·
            refine ⟨68596570447848912774029627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 182924187860930434064079005 68596570447848912774029627)
            ·
              refine ⟨102894855671773369161044441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68596570447848912774029627 102894855671773369161044441)
              ·
                refine ⟨77171141753830026870783331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102894855671773369161044441 77171141753830026870783331)
                ·
                  refine ⟨115756712630745040306174997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77171141753830026870783331 115756712630745040306174997)
                  ·
                    refine ⟨5426095904566173764351953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 115756712630745040306174997 5426095904566173764351953)
                    ·
                      refine ⟨4069571928424630323263965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5426095904566173764351953 4069571928424630323263965)
                      ·
                        rfl

theorem cell23_7925463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 2, 1, 6, 2].length) (baseStart_7925463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7925463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7925463 prefixEnd_7925463 := by exact prefixLift 7925463
  have htrace : WordTrace (prefixWord ++ tailWord_7925463) baseStart_7925463 baseEnd_7925463 := by
    simpa [prefixWord, tailWord_7925463, baseEnd_7925463] using wordTrace_append hprefix tailTrace_7925463
  have hstable : (prefixWord ++ tailWord_7925463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7925463).length < 2 ^ (prefixWord ++ tailWord_7925463).sum := by decide
  have hdescent : baseEnd_7925463 < baseStart_7925463 := by decide
  rcases family_descends (prefixWord ++ tailWord_7925463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7925476 : List Nat := [2, 3, 1, 1, 1, 3, 1, 1, 1, 3, 6]
def baseStart_7925476 : Nat := 118140960795 + 7925476 * 2 ^ 59
def prefixEnd_7925476 : Nat := 4983230072969 + 3 ^ 40 * 7925476 * 2
def baseEnd_7925476 : Nat := 4069578603673138772401405

theorem tailTrace_7925476 : CollatzResearch.WordTrace tailWord_7925476 prefixEnd_7925476 4069578603673138772401405 := by
  unfold tailWord_7925476
  simp only [CollatzResearch.WordTrace]
  refine ⟨144532928717680745191606141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192710571623574326922141521 144532928717680745191606141)
  ·
    refine ⟨54199848269130279446852303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144532928717680745191606141 54199848269130279446852303)
    ·
      refine ⟨81299772403695419170278455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54199848269130279446852303 81299772403695419170278455)
      ·
        refine ⟨121949658605543128755417683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81299772403695419170278455 121949658605543128755417683)
        ·
          refine ⟨182924487908314693133126525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121949658605543128755417683 182924487908314693133126525)
          ·
            refine ⟨68596682965618009924922447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 182924487908314693133126525 68596682965618009924922447)
            ·
              refine ⟨102895024448427014887383671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68596682965618009924922447 102895024448427014887383671)
              ·
                refine ⟨154342536672640522331075507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102895024448427014887383671 154342536672640522331075507)
                ·
                  refine ⟨231513805008960783496613261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 154342536672640522331075507 231513805008960783496613261)
                  ·
                    refine ⟨86817676878360293811229973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 231513805008960783496613261 86817676878360293811229973)
                    ·
                      refine ⟨4069578603673138772401405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 86817676878360293811229973 4069578603673138772401405)
                      ·
                        rfl

theorem cell23_7925476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 1, 1, 3, 6].length) (baseStart_7925476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7925476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7925476 prefixEnd_7925476 := by exact prefixLift 7925476
  have htrace : WordTrace (prefixWord ++ tailWord_7925476) baseStart_7925476 baseEnd_7925476 := by
    simpa [prefixWord, tailWord_7925476, baseEnd_7925476] using wordTrace_append hprefix tailTrace_7925476
  have hstable : (prefixWord ++ tailWord_7925476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7925476).length < 2 ^ (prefixWord ++ tailWord_7925476).sum := by decide
  have hdescent : baseEnd_7925476 < baseStart_7925476 := by decide
  rcases family_descends (prefixWord ++ tailWord_7925476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7925480 : List Nat := [2, 1, 4, 1, 3, 1, 1, 2, 2, 4, 2]
def baseStart_7925480 : Nat := 118140960795 + 7925480 * 2 ^ 59
def prefixEnd_7925480 : Nat := 4983230072969 + 3 ^ 40 * 7925480 * 2
def baseEnd_7925480 : Nat := 4069580657595756756751387

theorem tailTrace_7925480 : CollatzResearch.WordTrace tailWord_7925480 prefixEnd_7925480 4069580657595756756751387 := by
  unfold tailWord_7925480
  simp only [CollatzResearch.WordTrace]
  refine ⟨144533001663673499533178947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192710668884897999377571929 144533001663673499533178947)
  ·
    refine ⟨216799502495510249299768421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144533001663673499533178947 216799502495510249299768421)
    ·
      refine ⟨40649906717908171743706579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 216799502495510249299768421 40649906717908171743706579)
      ·
        refine ⟨60974860076862257615559869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40649906717908171743706579 60974860076862257615559869)
        ·
          refine ⟨22865572528823346605834951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60974860076862257615559869 22865572528823346605834951)
          ·
            refine ⟨34298358793235019908752427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22865572528823346605834951 34298358793235019908752427)
            ·
              refine ⟨51447538189852529863128641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34298358793235019908752427 51447538189852529863128641)
              ·
                refine ⟨38585653642389397397346481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51447538189852529863128641 38585653642389397397346481)
                ·
                  refine ⟨28939240231792048048009861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38585653642389397397346481 28939240231792048048009861)
                  ·
                    refine ⟨5426107543461009009001849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28939240231792048048009861 5426107543461009009001849)
                    ·
                      refine ⟨4069580657595756756751387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5426107543461009009001849 4069580657595756756751387)
                      ·
                        rfl

theorem cell23_7925480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 2, 2, 4, 2].length) (baseStart_7925480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7925480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7925480 prefixEnd_7925480 := by exact prefixLift 7925480
  have htrace : WordTrace (prefixWord ++ tailWord_7925480) baseStart_7925480 baseEnd_7925480 := by
    simpa [prefixWord, tailWord_7925480, baseEnd_7925480] using wordTrace_append hprefix tailTrace_7925480
  have hstable : (prefixWord ++ tailWord_7925480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7925480).length < 2 ^ (prefixWord ++ tailWord_7925480).sum := by decide
  have hdescent : baseEnd_7925480 < baseStart_7925480 := by decide
  rcases family_descends (prefixWord ++ tailWord_7925480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7925483 : List Nat := [1, 1, 1, 1, 2, 4, 2, 4, 2, 2, 3]
def baseStart_7925483 : Nat := 118140960795 + 7925483 * 2 ^ 59
def prefixEnd_7925483 : Nat := 4983230072969 + 3 ^ 40 * 7925483 * 2
def baseEnd_7925483 : Nat := 4069582198037720245013873

theorem tailTrace_7925483 : CollatzResearch.WordTrace tailWord_7925483 prefixEnd_7925483 4069582198037720245013873 := by
  unfold tailWord_7925483
  simp only [CollatzResearch.WordTrace]
  refine ⟨289066112746336130578717103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192710741830890753719144735 289066112746336130578717103)
  ·
    refine ⟨433599169119504195868075655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289066112746336130578717103 433599169119504195868075655)
    ·
      refine ⟨650398753679256293802113483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 433599169119504195868075655 650398753679256293802113483)
      ·
        refine ⟨975598130518884440703170225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 650398753679256293802113483 975598130518884440703170225)
        ·
          refine ⟨731698597889163330527377669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 975598130518884440703170225 731698597889163330527377669)
          ·
            refine ⟨137193487104218124473883313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 731698597889163330527377669 137193487104218124473883313)
            ·
              refine ⟨102895115328163593355412485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137193487104218124473883313 102895115328163593355412485)
              ·
                refine ⟨19292834124030673754139841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 102895115328163593355412485 19292834124030673754139841)
                ·
                  refine ⟨14469625593023005315604881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19292834124030673754139841 14469625593023005315604881)
                  ·
                    refine ⟨10852219194767253986703661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14469625593023005315604881 10852219194767253986703661)
                    ·
                      refine ⟨4069582198037720245013873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10852219194767253986703661 4069582198037720245013873)
                      ·
                        rfl

theorem cell23_7925483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 4, 2, 2, 3].length) (baseStart_7925483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7925483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7925483 prefixEnd_7925483 := by exact prefixLift 7925483
  have htrace : WordTrace (prefixWord ++ tailWord_7925483) baseStart_7925483 baseEnd_7925483 := by
    simpa [prefixWord, tailWord_7925483, baseEnd_7925483] using wordTrace_append hprefix tailTrace_7925483
  have hstable : (prefixWord ++ tailWord_7925483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7925483).length < 2 ^ (prefixWord ++ tailWord_7925483).sum := by decide
  have hdescent : baseEnd_7925483 < baseStart_7925483 := by decide
  rcases family_descends (prefixWord ++ tailWord_7925483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7925490 : List Nat := [3, 2, 1, 3, 1, 1, 4, 1, 3, 4]
def baseStart_7925490 : Nat := 118140960795 + 7925490 * 2 ^ 59
def prefixEnd_7925490 : Nat := 4983230072969 + 3 ^ 40 * 7925490 * 2
def baseEnd_7925490 : Nat := 1356528597467433905875447

theorem tailTrace_7925490 : CollatzResearch.WordTrace tailWord_7925490 prefixEnd_7925490 1356528597467433905875447 := by
  unfold tailWord_7925490
  simp only [CollatzResearch.WordTrace]
  refine ⟨72266592014327692693555481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192710912038207180516147949 72266592014327692693555481)
  ·
    refine ⟨54199944010745769520166611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72266592014327692693555481 54199944010745769520166611)
    ·
      refine ⟨81299916016118654280249917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54199944010745769520166611 81299916016118654280249917)
      ·
        refine ⟨30487468506044495355093719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81299916016118654280249917 30487468506044495355093719)
        ·
          refine ⟨45731202759066743032640579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30487468506044495355093719 45731202759066743032640579)
          ·
            refine ⟨68596804138600114548960869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45731202759066743032640579 68596804138600114548960869)
            ·
              refine ⟨12861900775987521477930163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68596804138600114548960869 12861900775987521477930163)
              ·
                refine ⟨19292851163981282216895245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12861900775987521477930163 19292851163981282216895245)
                ·
                  refine ⟨7234819186492980831335717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19292851163981282216895245 7234819186492980831335717)
                  ·
                    refine ⟨1356528597467433905875447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7234819186492980831335717 1356528597467433905875447)
                    ·
                      rfl

theorem cell23_7925490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 4, 1, 3, 4].length) (baseStart_7925490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7925490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7925490 prefixEnd_7925490 := by exact prefixLift 7925490
  have htrace : WordTrace (prefixWord ++ tailWord_7925490) baseStart_7925490 baseEnd_7925490 := by
    simpa [prefixWord, tailWord_7925490, baseEnd_7925490] using wordTrace_append hprefix tailTrace_7925490
  have hstable : (prefixWord ++ tailWord_7925490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7925490).length < 2 ^ (prefixWord ++ tailWord_7925490).sum := by decide
  have hdescent : baseEnd_7925490 < baseStart_7925490 := by decide
  rcases family_descends (prefixWord ++ tailWord_7925490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7925567 : List Nat := [1, 1, 2, 2, 6, 2, 1, 2, 1, 5]
def baseStart_7925567 : Nat := 118140960795 + 7925567 * 2 ^ 59
def prefixEnd_7925567 : Nat := 4983230072969 + 3 ^ 40 * 7925567 * 2
def baseEnd_7925567 : Nat := 1356541776804232638787829

theorem tailTrace_7925567 : CollatzResearch.WordTrace tailWord_7925567 prefixEnd_7925567 1356541776804232638787829 := by
  unfold tailWord_7925567
  simp only [CollatzResearch.WordTrace]
  refine ⟨289069176478031812924774955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192712784318687875283183303 289069176478031812924774955)
  ·
    refine ⟨433603764717047719387162433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289069176478031812924774955 433603764717047719387162433)
    ·
      refine ⟨325202823537785789540371825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 433603764717047719387162433 325202823537785789540371825)
      ·
        refine ⟨243902117653339342155278869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 325202823537785789540371825 243902117653339342155278869)
        ·
          refine ⟨11432911765000281663528697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 243902117653339342155278869 11432911765000281663528697)
          ·
            refine ⟨8574683823750211247646523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11432911765000281663528697 8574683823750211247646523)
            ·
              refine ⟨12862025735625316871469785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8574683823750211247646523 12862025735625316871469785)
              ·
                refine ⟨9646519301718987653602339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12862025735625316871469785 9646519301718987653602339)
                ·
                  refine ⟨14469778952578481480403509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9646519301718987653602339 14469778952578481480403509)
                  ·
                    refine ⟨1356541776804232638787829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14469778952578481480403509 1356541776804232638787829)
                    ·
                      rfl

theorem cell23_7925567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 2, 1, 2, 1, 5].length) (baseStart_7925567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7925567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7925567 prefixEnd_7925567 := by exact prefixLift 7925567
  have htrace : WordTrace (prefixWord ++ tailWord_7925567) baseStart_7925567 baseEnd_7925567 := by
    simpa [prefixWord, tailWord_7925567, baseEnd_7925567] using wordTrace_append hprefix tailTrace_7925567
  have hstable : (prefixWord ++ tailWord_7925567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7925567).length < 2 ^ (prefixWord ++ tailWord_7925567).sum := by decide
  have hdescent : baseEnd_7925567 < baseStart_7925567 := by decide
  rcases family_descends (prefixWord ++ tailWord_7925567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7925580 : List Nat := [2, 2, 1, 3, 4, 1, 1, 2, 1, 6]
def baseStart_7925580 : Nat := 118140960795 + 7925580 * 2 ^ 59
def prefixEnd_7925580 : Nat := 4983230072969 + 3 ^ 40 * 7925580 * 2
def baseEnd_7925580 : Nat := 1356544001887068788500309

theorem tailTrace_7925580 : CollatzResearch.WordTrace tailWord_7925580 prefixEnd_7925580 1356544001887068788500309 := by
  unfold tailWord_7925580
  simp only [CollatzResearch.WordTrace]
  refine ⟨144534825313492358072499097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192713100417989810763332129 144534825313492358072499097)
  ·
    refine ⟨108401118985119268554374323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144534825313492358072499097 108401118985119268554374323)
    ·
      refine ⟨162601678477678902831561485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108401118985119268554374323 162601678477678902831561485)
      ·
        refine ⟨60975629429129588561835557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 162601678477678902831561485 60975629429129588561835557)
        ·
          refine ⟨11432930517961797855344167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60975629429129588561835557 11432930517961797855344167)
          ·
            refine ⟨17149395776942696783016251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11432930517961797855344167 17149395776942696783016251)
            ·
              refine ⟨25724093665414045174524377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17149395776942696783016251 25724093665414045174524377)
              ·
                refine ⟨19293070249060533880893283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25724093665414045174524377 19293070249060533880893283)
                ·
                  refine ⟨28939605373590800821339925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19293070249060533880893283 28939605373590800821339925)
                  ·
                    refine ⟨1356544001887068788500309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28939605373590800821339925 1356544001887068788500309)
                    ·
                      rfl

theorem cell23_7925580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 1, 2, 1, 6].length) (baseStart_7925580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7925580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7925580 prefixEnd_7925580 := by exact prefixLift 7925580
  have htrace : WordTrace (prefixWord ++ tailWord_7925580) baseStart_7925580 baseEnd_7925580 := by
    simpa [prefixWord, tailWord_7925580, baseEnd_7925580] using wordTrace_append hprefix tailTrace_7925580
  have hstable : (prefixWord ++ tailWord_7925580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7925580).length < 2 ^ (prefixWord ++ tailWord_7925580).sum := by decide
  have hdescent : baseEnd_7925580 < baseStart_7925580 := by decide
  rcases family_descends (prefixWord ++ tailWord_7925580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7925613 : List Nat := [1, 5, 1, 1, 1, 1, 2, 1, 2, 2, 6]
def baseStart_7925613 : Nat := 118140960795 + 7925613 * 2 ^ 59
def prefixEnd_7925613 : Nat := 4983230072969 + 3 ^ 40 * 7925613 * 2
def baseEnd_7925613 : Nat := 4069648950522804736388275

theorem tailTrace_7925613 : CollatzResearch.WordTrace tailWord_7925613 prefixEnd_7925613 4069648950522804736388275 := by
  unfold tailWord_7925613
  simp only [CollatzResearch.WordTrace]
  refine ⟨289070854235865162780949493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192713902823910108520632995 289070854235865162780949493)
  ·
    refine ⟨27100392584612359010714015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 289070854235865162780949493 27100392584612359010714015)
    ·
      refine ⟨40650588876918538516071023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27100392584612359010714015 40650588876918538516071023)
      ·
        refine ⟨60975883315377807774106535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40650588876918538516071023 60975883315377807774106535)
        ·
          refine ⟨91463824973066711661159803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60975883315377807774106535 91463824973066711661159803)
          ·
            refine ⟨137195737459600067491739705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91463824973066711661159803 137195737459600067491739705)
            ·
              refine ⟨102896803094700050618804779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137195737459600067491739705 102896803094700050618804779)
              ·
                refine ⟨154345204642050075928207169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102896803094700050618804779 154345204642050075928207169)
                ·
                  refine ⟨115758903481537556946155377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 154345204642050075928207169 115758903481537556946155377)
                  ·
                    refine ⟨86819177611153167709616533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 115758903481537556946155377 86819177611153167709616533)
                    ·
                      refine ⟨4069648950522804736388275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 86819177611153167709616533 4069648950522804736388275)
                      ·
                        rfl

theorem cell23_7925613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 1, 2, 2, 6].length) (baseStart_7925613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7925613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7925613 prefixEnd_7925613 := by exact prefixLift 7925613
  have htrace : WordTrace (prefixWord ++ tailWord_7925613) baseStart_7925613 baseEnd_7925613 := by
    simpa [prefixWord, tailWord_7925613, baseEnd_7925613] using wordTrace_append hprefix tailTrace_7925613
  have hstable : (prefixWord ++ tailWord_7925613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7925613).length < 2 ^ (prefixWord ++ tailWord_7925613).sum := by decide
  have hdescent : baseEnd_7925613 < baseStart_7925613 := by decide
  rcases family_descends (prefixWord ++ tailWord_7925613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7925653 : List Nat := [1, 3, 2, 1, 1, 3, 1, 1, 4, 6]
def baseStart_7925653 : Nat := 118140960795 + 7925653 * 2 ^ 59
def prefixEnd_7925653 : Nat := 4983230072969 + 3 ^ 40 * 7925653 * 2
def baseEnd_7925653 : Nat := 1356556496582994859962697

theorem tailTrace_7925653 : CollatzResearch.WordTrace tailWord_7925653 prefixEnd_7925653 1356556496582994859962697 := by
  unfold tailWord_7925653
  simp only [CollatzResearch.WordTrace]
  refine ⟨289072313155720249612405613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192714875437146833074937075 289072313155720249612405613)
  ·
    refine ⟨108402117433395093604652105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 289072313155720249612405613 108402117433395093604652105)
    ·
      refine ⟨81301588075046320203489079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108402117433395093604652105 81301588075046320203489079)
      ·
        refine ⟨121952382112569480305233619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81301588075046320203489079 121952382112569480305233619)
        ·
          refine ⟨182928573168854220457850429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121952382112569480305233619 182928573168854220457850429)
          ·
            refine ⟨68598214938320332671693911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 182928573168854220457850429 68598214938320332671693911)
            ·
              refine ⟨102897322407480499007540867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68598214938320332671693911 102897322407480499007540867)
              ·
                refine ⟨154345983611220748511311301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102897322407480499007540867 154345983611220748511311301)
                ·
                  refine ⟨28939871927103890345870869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 154345983611220748511311301 28939871927103890345870869)
                  ·
                    refine ⟨1356556496582994859962697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28939871927103890345870869 1356556496582994859962697)
                    ·
                      rfl

theorem cell23_7925653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 1, 4, 6].length) (baseStart_7925653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7925653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7925653 prefixEnd_7925653 := by exact prefixLift 7925653
  have htrace : WordTrace (prefixWord ++ tailWord_7925653) baseStart_7925653 baseEnd_7925653 := by
    simpa [prefixWord, tailWord_7925653, baseEnd_7925653] using wordTrace_append hprefix tailTrace_7925653
  have hstable : (prefixWord ++ tailWord_7925653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7925653).length < 2 ^ (prefixWord ++ tailWord_7925653).sum := by decide
  have hdescent : baseEnd_7925653 < baseStart_7925653 := by decide
  rcases family_descends (prefixWord ++ tailWord_7925653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7925671 : List Nat := [1, 1, 6, 1, 2, 2, 3, 1, 2, 1, 3]
def baseStart_7925671 : Nat := 118140960795 + 7925671 * 2 ^ 59
def prefixEnd_7925671 : Nat := 4983230072969 + 3 ^ 40 * 7925671 * 2
def baseEnd_7925671 : Nat := 4069678732400765509463009

theorem tailTrace_7925671 : CollatzResearch.WordTrace tailWord_7925671 prefixEnd_7925671 4069678732400765509463009 := by
  unfold tailWord_7925671
  simp only [CollatzResearch.WordTrace]
  refine ⟨289072969669655038686560867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192715313113103359124373911 289072969669655038686560867)
  ·
    refine ⟨433609454504482558029841301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289072969669655038686560867 433609454504482558029841301)
    ·
      refine ⟨20325443179897619907648811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 433609454504482558029841301 20325443179897619907648811)
      ·
        refine ⟨30488164769846429861473217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20325443179897619907648811 30488164769846429861473217)
        ·
          refine ⟨22866123577384822396104913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30488164769846429861473217 22866123577384822396104913)
          ·
            refine ⟨17149592683038616797078685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22866123577384822396104913 17149592683038616797078685)
            ·
              refine ⟨6431097256139481298904507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17149592683038616797078685 6431097256139481298904507)
              ·
                refine ⟨9646645884209221948356761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6431097256139481298904507 9646645884209221948356761)
                ·
                  refine ⟨7234984413156916461267571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9646645884209221948356761 7234984413156916461267571)
                  ·
                    refine ⟨10852476619735374691901357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7234984413156916461267571 10852476619735374691901357)
                    ·
                      refine ⟨4069678732400765509463009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10852476619735374691901357 4069678732400765509463009)
                      ·
                        rfl

theorem cell23_7925671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 3, 1, 2, 1, 3].length) (baseStart_7925671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7925671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7925671 prefixEnd_7925671 := by exact prefixLift 7925671
  have htrace : WordTrace (prefixWord ++ tailWord_7925671) baseStart_7925671 baseEnd_7925671 := by
    simpa [prefixWord, tailWord_7925671, baseEnd_7925671] using wordTrace_append hprefix tailTrace_7925671
  have hstable : (prefixWord ++ tailWord_7925671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7925671).length < 2 ^ (prefixWord ++ tailWord_7925671).sum := by decide
  have hdescent : baseEnd_7925671 < baseStart_7925671 := by decide
  rcases family_descends (prefixWord ++ tailWord_7925671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7925673 : List Nat := [1, 2, 1, 1, 1, 1, 4, 3, 1, 4, 4]
def baseStart_7925673 : Nat := 118140960795 + 7925673 * 2 ^ 59
def prefixEnd_7925673 : Nat := 4983230072969 + 3 ^ 40 * 7925673 * 2
def baseEnd_7925673 : Nat := 4069679759362074501637999

theorem tailTrace_7925673 : CollatzResearch.WordTrace tailWord_7925673 prefixEnd_7925673 4069679759362074501637999 := by
  unfold tailWord_7925673
  simp only [CollatzResearch.WordTrace]
  refine ⟨289073042615647793028133673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192715361743765195352089115 289073042615647793028133673)
  ·
    refine ⟨216804781961735844771100255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 289073042615647793028133673 216804781961735844771100255)
    ·
      refine ⟨325207172942603767156650383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216804781961735844771100255 325207172942603767156650383)
      ·
        refine ⟨487810759413905650734975575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 325207172942603767156650383 487810759413905650734975575)
        ·
          refine ⟨731716139120858476102463363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 487810759413905650734975575 731716139120858476102463363)
          ·
            refine ⟨1097574208681287714153695045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 731716139120858476102463363 1097574208681287714153695045)
            ·
              refine ⟨205795164127741446403817821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1097574208681287714153695045 205795164127741446403817821)
              ·
                refine ⟨77173186547903042401431683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 205795164127741446403817821 77173186547903042401431683)
                ·
                  refine ⟨115759779821854563602147525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77173186547903042401431683 115759779821854563602147525)
                  ·
                    refine ⟨21704958716597730675402661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 115759779821854563602147525 21704958716597730675402661)
                    ·
                      refine ⟨4069679759362074501637999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21704958716597730675402661 4069679759362074501637999)
                      ·
                        rfl

theorem cell23_7925673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 3, 1, 4, 4].length) (baseStart_7925673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7925673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7925673 prefixEnd_7925673 := by exact prefixLift 7925673
  have htrace : WordTrace (prefixWord ++ tailWord_7925673) baseStart_7925673 baseEnd_7925673 := by
    simpa [prefixWord, tailWord_7925673, baseEnd_7925673] using wordTrace_append hprefix tailTrace_7925673
  have hstable : (prefixWord ++ tailWord_7925673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7925673).length < 2 ^ (prefixWord ++ tailWord_7925673).sum := by decide
  have hdescent : baseEnd_7925673 < baseStart_7925673 := by decide
  rcases family_descends (prefixWord ++ tailWord_7925673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7925678 : List Nat := [4, 1, 5, 1, 2, 1, 2, 7]
def baseStart_7925678 : Nat := 118140960795 + 7925678 * 2 ^ 59
def prefixEnd_7925678 : Nat := 4983230072969 + 3 ^ 40 * 7925678 * 2
def baseEnd_7925678 : Nat := 150728975065383221558351

theorem tailTrace_7925678 : CollatzResearch.WordTrace tailWord_7925678 prefixEnd_7925678 150728975065383221558351 := by
  unfold tailWord_7925678
  simp only [CollatzResearch.WordTrace]
  refine ⟨36134153122578709860258211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 192715483320419785921377125 36134153122578709860258211)
  ·
    refine ⟨54201229683868064790387317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36134153122578709860258211 54201229683868064790387317)
    ·
      refine ⟨5081365282862631074098811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 54201229683868064790387317 5081365282862631074098811)
      ·
        refine ⟨7622047924293946611148217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5081365282862631074098811 7622047924293946611148217)
        ·
          refine ⟨5716535943220459958361163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7622047924293946611148217 5716535943220459958361163)
          ·
            refine ⟨8574803914830689937541745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5716535943220459958361163 8574803914830689937541745)
            ·
              refine ⟨6431102936123017453156309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8574803914830689937541745 6431102936123017453156309)
              ·
                refine ⟨150728975065383221558351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6431102936123017453156309 150728975065383221558351)
                ·
                  rfl

theorem cell23_7925678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 1, 2, 7].length) (baseStart_7925678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7925678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7925678 prefixEnd_7925678 := by exact prefixLift 7925678
  have htrace : WordTrace (prefixWord ++ tailWord_7925678) baseStart_7925678 baseEnd_7925678 := by
    simpa [prefixWord, tailWord_7925678, baseEnd_7925678] using wordTrace_append hprefix tailTrace_7925678
  have hstable : (prefixWord ++ tailWord_7925678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7925678).length < 2 ^ (prefixWord ++ tailWord_7925678).sum := by decide
  have hdescent : baseEnd_7925678 < baseStart_7925678 := by decide
  rcases family_descends (prefixWord ++ tailWord_7925678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7925683 : List Nat := [1, 1, 1, 2, 3, 1, 3, 4, 7]
def baseStart_7925683 : Nat := 118140960795 + 7925683 * 2 ^ 59
def prefixEnd_7925683 : Nat := 4983230072969 + 3 ^ 40 * 7925683 * 2
def baseEnd_7925683 : Nat := 452187210463179940279217

theorem tailTrace_7925683 : CollatzResearch.WordTrace tailWord_7925683 prefixEnd_7925683 452187210463179940279217 := by
  unfold tailWord_7925683
  simp only [CollatzResearch.WordTrace]
  refine ⟨289073407345611564735997703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192715604897074376490665135 289073407345611564735997703)
  ·
    refine ⟨433610111018417347103996555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289073407345611564735997703 433610111018417347103996555)
    ·
      refine ⟨650415166527626020655994833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 433610111018417347103996555 650415166527626020655994833)
      ·
        refine ⟨487811374895719515491996125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 650415166527626020655994833 487811374895719515491996125)
        ·
          refine ⟨182929265585894818309498547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 487811374895719515491996125 182929265585894818309498547)
          ·
            refine ⟨274393898378842227464247821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182929265585894818309498547 274393898378842227464247821)
            ·
              refine ⟨102897711892065835299092933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 274393898378842227464247821 102897711892065835299092933)
              ·
                refine ⟨19293320979762344118579925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 102897711892065835299092933 19293320979762344118579925)
                ·
                  refine ⟨452187210463179940279217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19293320979762344118579925 452187210463179940279217)
                  ·
                    rfl

theorem cell23_7925683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 4, 7].length) (baseStart_7925683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7925683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7925683 prefixEnd_7925683 := by exact prefixLift 7925683
  have htrace : WordTrace (prefixWord ++ tailWord_7925683) baseStart_7925683 baseEnd_7925683 := by
    simpa [prefixWord, tailWord_7925683, baseEnd_7925683] using wordTrace_append hprefix tailTrace_7925683
  have hstable : (prefixWord ++ tailWord_7925683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7925683).length < 2 ^ (prefixWord ++ tailWord_7925683).sum := by decide
  have hdescent : baseEnd_7925683 < baseStart_7925683 := by decide
  rcases family_descends (prefixWord ++ tailWord_7925683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7925694 : List Nat := [4, 2, 1, 1, 1, 3, 1, 2, 4, 2, 2]
def baseStart_7925694 : Nat := 118140960795 + 7925694 * 2 ^ 59
def prefixEnd_7925694 : Nat := 4983230072969 + 3 ^ 40 * 7925694 * 2
def baseEnd_7925694 : Nat := 4069690542455818919475403

theorem tailTrace_7925694 : CollatzResearch.WordTrace tailWord_7925694 prefixEnd_7925694 4069690542455818919475403 := by
  unfold tailWord_7925694
  simp only [CollatzResearch.WordTrace]
  refine ⟨36134226068571464201831017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 192715872365714475743098757 36134226068571464201831017)
  ·
    refine ⟨27100669551428598151373263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36134226068571464201831017 27100669551428598151373263)
    ·
      refine ⟨40651004327142897227059895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27100669551428598151373263 40651004327142897227059895)
      ·
        refine ⟨60976506490714345840589843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40651004327142897227059895 60976506490714345840589843)
        ·
          refine ⟨91464759736071518760884765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60976506490714345840589843 91464759736071518760884765)
          ·
            refine ⟨34299284901026819535331787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91464759736071518760884765 34299284901026819535331787)
            ·
              refine ⟨51448927351540229302997681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34299284901026819535331787 51448927351540229302997681)
              ·
                refine ⟨38586695513655171977248261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51448927351540229302997681 38586695513655171977248261)
                ·
                  refine ⟨7235005408810344745734049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38586695513655171977248261 7235005408810344745734049)
                  ·
                    refine ⟨5426254056607758559300537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7235005408810344745734049 5426254056607758559300537)
                    ·
                      refine ⟨4069690542455818919475403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5426254056607758559300537 4069690542455818919475403)
                      ·
                        rfl

theorem cell23_7925694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 2, 4, 2, 2].length) (baseStart_7925694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7925694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7925694 prefixEnd_7925694 := by exact prefixLift 7925694
  have htrace : WordTrace (prefixWord ++ tailWord_7925694) baseStart_7925694 baseEnd_7925694 := by
    simpa [prefixWord, tailWord_7925694, baseEnd_7925694] using wordTrace_append hprefix tailTrace_7925694
  have hstable : (prefixWord ++ tailWord_7925694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7925694).length < 2 ^ (prefixWord ++ tailWord_7925694).sum := by decide
  have hdescent : baseEnd_7925694 < baseStart_7925694 := by decide
  rcases family_descends (prefixWord ++ tailWord_7925694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7925713 : List Nat := [1, 2, 2, 1, 2, 1, 2, 2, 3, 7]
def baseStart_7925713 : Nat := 118140960795 + 7925713 * 2 ^ 59
def prefixEnd_7925713 : Nat := 4983230072969 + 3 ^ 40 * 7925713 * 2
def baseEnd_7925713 : Nat := 1356566766196084781712605

theorem tailTrace_7925713 : CollatzResearch.WordTrace tailWord_7925713 prefixEnd_7925713 1356566766196084781712605 := by
  unfold tailWord_7925713
  simp only [CollatzResearch.WordTrace]
  refine ⟨289074501535502879859589793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192716334357001919906393195 289074501535502879859589793)
  ·
    refine ⟨216805876151627159894692345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 289074501535502879859589793 216805876151627159894692345)
    ·
      refine ⟨162604407113720369921019259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216805876151627159894692345 162604407113720369921019259)
      ·
        refine ⟨243906610670580554881528889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162604407113720369921019259 243906610670580554881528889)
        ·
          refine ⟨182929958002935416161146667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 243906610670580554881528889 182929958002935416161146667)
          ·
            refine ⟨274394937004403124241720001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182929958002935416161146667 274394937004403124241720001)
            ·
              refine ⟨205796202753302343181290001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 274394937004403124241720001 205796202753302343181290001)
              ·
                refine ⟨154347152064976757385967501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 205796202753302343181290001 154347152064976757385967501)
                ·
                  refine ⟨57880182024366284019737813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 154347152064976757385967501 57880182024366284019737813)
                  ·
                    refine ⟨1356566766196084781712605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 57880182024366284019737813 1356566766196084781712605)
                    ·
                      rfl

theorem cell23_7925713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 2, 3, 7].length) (baseStart_7925713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7925713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7925713 prefixEnd_7925713 := by exact prefixLift 7925713
  have htrace : WordTrace (prefixWord ++ tailWord_7925713) baseStart_7925713 baseEnd_7925713 := by
    simpa [prefixWord, tailWord_7925713, baseEnd_7925713] using wordTrace_append hprefix tailTrace_7925713
  have hstable : (prefixWord ++ tailWord_7925713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7925713).length < 2 ^ (prefixWord ++ tailWord_7925713).sum := by decide
  have hdescent : baseEnd_7925713 < baseStart_7925713 := by decide
  rcases family_descends (prefixWord ++ tailWord_7925713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7925717 : List Nat := [1, 3, 2, 3, 2, 3, 1, 1, 7]
def baseStart_7925717 : Nat := 118140960795 + 7925717 * 2 ^ 59
def prefixEnd_7925717 : Nat := 4983230072969 + 3 ^ 40 * 7925717 * 2
def baseEnd_7925717 : Nat := 452189150278985814387533

theorem tailTrace_7925717 : CollatzResearch.WordTrace tailWord_7925717 prefixEnd_7925717 452189150278985814387533 := by
  unfold tailWord_7925717
  simp only [CollatzResearch.WordTrace]
  refine ⟨289074647427488388542735405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192716431618325592361823603 289074647427488388542735405)
  ·
    refine ⟨108402992785308145703525777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 289074647427488388542735405 108402992785308145703525777)
    ·
      refine ⟨81302244588981109277644333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108402992785308145703525777 81302244588981109277644333)
      ·
        refine ⟨30488341720867915979116625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81302244588981109277644333 30488341720867915979116625)
        ·
          refine ⟨22866256290650936984337469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30488341720867915979116625 22866256290650936984337469)
          ·
            refine ⟨8574846108994101369126551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22866256290650936984337469 8574846108994101369126551)
            ·
              refine ⟨12862269163491152053689827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8574846108994101369126551 12862269163491152053689827)
              ·
                refine ⟨19293403745236728080534741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12862269163491152053689827 19293403745236728080534741)
                ·
                  refine ⟨452189150278985814387533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19293403745236728080534741 452189150278985814387533)
                  ·
                    rfl

theorem cell23_7925717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 3, 1, 1, 7].length) (baseStart_7925717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7925717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7925717 prefixEnd_7925717 := by exact prefixLift 7925717
  have htrace : WordTrace (prefixWord ++ tailWord_7925717) baseStart_7925717 baseEnd_7925717 := by
    simpa [prefixWord, tailWord_7925717, baseEnd_7925717] using wordTrace_append hprefix tailTrace_7925717
  have hstable : (prefixWord ++ tailWord_7925717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7925717).length < 2 ^ (prefixWord ++ tailWord_7925717).sum := by decide
  have hdescent : baseEnd_7925717 < baseStart_7925717 := by decide
  rcases family_descends (prefixWord ++ tailWord_7925717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7925760 : List Nat := [2, 1, 1, 2, 1, 1, 1, 3, 7, 4]
def baseStart_7925760 : Nat := 118140960795 + 7925760 * 2 ^ 59
def prefixEnd_7925760 : Nat := 4983230072969 + 3 ^ 40 * 7925760 * 2
def baseEnd_7925760 : Nat := 1356574810726338553750033

theorem tailTrace_7925760 : CollatzResearch.WordTrace tailWord_7925760 prefixEnd_7925760 1356574810726338553750033 := by
  unfold tailWord_7925760
  simp only [CollatzResearch.WordTrace]
  refine ⟨144538107883166303443275367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192717477177555071257700489 144538107883166303443275367)
  ·
    refine ⟨216807161824749455164913051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144538107883166303443275367 216807161824749455164913051)
    ·
      refine ⟨325210742737124182747369577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216807161824749455164913051 325210742737124182747369577)
      ·
        refine ⟨243908057052843137060527183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 325210742737124182747369577 243908057052843137060527183)
        ·
          refine ⟨365862085579264705590790775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 243908057052843137060527183 365862085579264705590790775)
          ·
            refine ⟨548793128368897058386186163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 365862085579264705590790775 548793128368897058386186163)
            ·
              refine ⟨823189692553345587579279245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 548793128368897058386186163 823189692553345587579279245)
              ·
                refine ⟨308696134707504595342229717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 823189692553345587579279245 308696134707504595342229717)
                ·
                  refine ⟨7235065657207138953333509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 308696134707504595342229717 7235065657207138953333509)
                  ·
                    refine ⟨1356574810726338553750033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7235065657207138953333509 1356574810726338553750033)
                    ·
                      rfl

theorem cell23_7925760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 3, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 3, 7, 4].length) (baseStart_7925760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7925760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7925760 prefixEnd_7925760 := by exact prefixLift 7925760
  have htrace : WordTrace (prefixWord ++ tailWord_7925760) baseStart_7925760 baseEnd_7925760 := by
    simpa [prefixWord, tailWord_7925760, baseEnd_7925760] using wordTrace_append hprefix tailTrace_7925760
  have hstable : (prefixWord ++ tailWord_7925760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7925760).length < 2 ^ (prefixWord ++ tailWord_7925760).sum := by decide
  have hdescent : baseEnd_7925760 < baseStart_7925760 := by decide
  rcases family_descends (prefixWord ++ tailWord_7925760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7925767 : List Nat := [1, 1, 4, 3, 1, 2, 2, 2, 2, 1, 4]
def baseStart_7925767 : Nat := 118140960795 + 7925767 * 2 ^ 59
def prefixEnd_7925767 : Nat := 4983230072969 + 3 ^ 40 * 7925767 * 2
def baseEnd_7925767 : Nat := 4069728026543597133862567

theorem tailTrace_7925767 : CollatzResearch.WordTrace tailWord_7925767 prefixEnd_7925767 4069728026543597133862567 := by
  unfold tailWord_7925767
  simp only [CollatzResearch.WordTrace]
  refine ⟨289076471077307247082055555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192717647384871498054703703 289076471077307247082055555)
  ·
    refine ⟨433614706615960870623083333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289076471077307247082055555 433614706615960870623083333)
    ·
      refine ⟨81302757490492663241828125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 433614706615960870623083333 81302757490492663241828125)
      ·
        refine ⟨30488534058934748715685547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81302757490492663241828125 30488534058934748715685547)
        ·
          refine ⟨45732801088402123073528321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30488534058934748715685547 45732801088402123073528321)
          ·
            refine ⟨34299600816301592305146241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45732801088402123073528321 34299600816301592305146241)
            ·
              refine ⟨25724700612226194228859681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34299600816301592305146241 25724700612226194228859681)
              ·
                refine ⟨19293525459169645671644761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25724700612226194228859681 19293525459169645671644761)
                ·
                  refine ⟨14470144094377234253733571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19293525459169645671644761 14470144094377234253733571)
                  ·
                    refine ⟨21705216141565851380600357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14470144094377234253733571 21705216141565851380600357)
                    ·
                      refine ⟨4069728026543597133862567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21705216141565851380600357 4069728026543597133862567)
                      ·
                        rfl

theorem cell23_7925767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 2, 2, 2, 1, 4].length) (baseStart_7925767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7925767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7925767 prefixEnd_7925767 := by exact prefixLift 7925767
  have htrace : WordTrace (prefixWord ++ tailWord_7925767) baseStart_7925767 baseEnd_7925767 := by
    simpa [prefixWord, tailWord_7925767, baseEnd_7925767] using wordTrace_append hprefix tailTrace_7925767
  have hstable : (prefixWord ++ tailWord_7925767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7925767).length < 2 ^ (prefixWord ++ tailWord_7925767).sum := by decide
  have hdescent : baseEnd_7925767 < baseStart_7925767 := by decide
  rcases family_descends (prefixWord ++ tailWord_7925767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7925857 : List Nat := [1, 2, 3, 1, 1, 2, 1, 1, 1, 8, 2]
def baseStart_7925857 : Nat := 118140960795 + 7925857 * 2 ^ 59
def prefixEnd_7925857 : Nat := 4983230072969 + 3 ^ 40 * 7925857 * 2
def baseEnd_7925857 : Nat := 4069774239802501781737153

theorem tailTrace_7925857 : CollatzResearch.WordTrace tailWord_7925857 prefixEnd_7925857 4069774239802501781737153 := by
  unfold tailWord_7925857
  simp only [CollatzResearch.WordTrace]
  refine ⟨289079753646981192452831825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192719835764654128301887883 289079753646981192452831825)
  ·
    refine ⟨216809815235235894339623869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 289079753646981192452831825 216809815235235894339623869)
    ·
      refine ⟨81303680713213460377358951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 216809815235235894339623869 81303680713213460377358951)
      ·
        refine ⟨121955521069820190566038427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81303680713213460377358951 121955521069820190566038427)
        ·
          refine ⟨182933281604730285849057641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121955521069820190566038427 182933281604730285849057641)
          ·
            refine ⟨137199961203547714386793231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 182933281604730285849057641 137199961203547714386793231)
            ·
              refine ⟨205799941805321571580189847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137199961203547714386793231 205799941805321571580189847)
              ·
                refine ⟨308699912707982357370284771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 205799941805321571580189847 308699912707982357370284771)
                ·
                  refine ⟨463049869061973536055427157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 308699912707982357370284771 463049869061973536055427157)
                  ·
                    refine ⟨5426365653070002375649537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 463049869061973536055427157 5426365653070002375649537)
                    ·
                      refine ⟨4069774239802501781737153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5426365653070002375649537 4069774239802501781737153)
                      ·
                        rfl

theorem cell23_7925857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 1, 1, 8, 2].length) (baseStart_7925857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7925857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7925857 prefixEnd_7925857 := by exact prefixLift 7925857
  have htrace : WordTrace (prefixWord ++ tailWord_7925857) baseStart_7925857 baseEnd_7925857 := by
    simpa [prefixWord, tailWord_7925857, baseEnd_7925857] using wordTrace_append hprefix tailTrace_7925857
  have hstable : (prefixWord ++ tailWord_7925857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7925857).length < 2 ^ (prefixWord ++ tailWord_7925857).sum := by decide
  have hdescent : baseEnd_7925857 < baseStart_7925857 := by decide
  rcases family_descends (prefixWord ++ tailWord_7925857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7925868 : List Nat := [2, 2, 1, 1, 3, 5, 1, 3, 1, 1, 3]
def baseStart_7925868 : Nat := 118140960795 + 7925868 * 2 ^ 59
def prefixEnd_7925868 : Nat := 4983230072969 + 3 ^ 40 * 7925868 * 2
def baseEnd_7925868 : Nat := 4069779888089701238699603

theorem tailTrace_7925868 : CollatzResearch.WordTrace tailWord_7925868 prefixEnd_7925868 4069779888089701238699603 := by
  unfold tailWord_7925868
  simp only [CollatzResearch.WordTrace]
  refine ⟨144540077424970670665741129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192720103233294227554321505 144540077424970670665741129)
  ·
    refine ⟨108405058068728002999305847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144540077424970670665741129 108405058068728002999305847)
    ·
      refine ⟨162607587103092004498958771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108405058068728002999305847 162607587103092004498958771)
      ·
        refine ⟨243911380654638006748438157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162607587103092004498958771 243911380654638006748438157)
        ·
          refine ⟨91466767745489252530664309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 243911380654638006748438157 91466767745489252530664309)
          ·
            refine ⟨8575009476139617424749779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 91466767745489252530664309 8575009476139617424749779)
            ·
              refine ⟨12862514214209426137124669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8575009476139617424749779 12862514214209426137124669)
              ·
                refine ⟨4823442830328534801421751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12862514214209426137124669 4823442830328534801421751)
                ·
                  refine ⟨7235164245492802202132627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4823442830328534801421751 7235164245492802202132627)
                  ·
                    refine ⟨10852746368239203303198941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7235164245492802202132627 10852746368239203303198941)
                    ·
                      refine ⟨4069779888089701238699603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10852746368239203303198941 4069779888089701238699603)
                      ·
                        rfl

theorem cell23_7925868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 5, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 5, 1, 3, 1, 1, 3].length) (baseStart_7925868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7925868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7925868 prefixEnd_7925868 := by exact prefixLift 7925868
  have htrace : WordTrace (prefixWord ++ tailWord_7925868) baseStart_7925868 baseEnd_7925868 := by
    simpa [prefixWord, tailWord_7925868, baseEnd_7925868] using wordTrace_append hprefix tailTrace_7925868
  have hstable : (prefixWord ++ tailWord_7925868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7925868).length < 2 ^ (prefixWord ++ tailWord_7925868).sum := by decide
  have hdescent : baseEnd_7925868 < baseStart_7925868 := by decide
  rcases family_descends (prefixWord ++ tailWord_7925868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7925874 : List Nat := [3, 2, 1, 2, 2, 2, 2, 3, 1, 1, 4]
def baseStart_7925874 : Nat := 118140960795 + 7925874 * 2 ^ 59
def prefixEnd_7925874 : Nat := 4983230072969 + 3 ^ 40 * 7925874 * 2
def baseEnd_7925874 : Nat := 4069782968973628215224575

theorem tailTrace_7925874 : CollatzResearch.WordTrace tailWord_7925874 prefixEnd_7925874 4069782968973628215224575 := by
  unfold tailWord_7925874
  simp only [CollatzResearch.WordTrace]
  refine ⟨72270093421979901089050169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192720249125279736237467117 72270093421979901089050169)
  ·
    refine ⟨54202570066484925816787627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72270093421979901089050169 54202570066484925816787627)
    ·
      refine ⟨81303855099727388725181441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54202570066484925816787627 81303855099727388725181441)
      ·
        refine ⟨60977891324795541543886081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81303855099727388725181441 60977891324795541543886081)
        ·
          refine ⟨45733418493596656157914561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60977891324795541543886081 45733418493596656157914561)
          ·
            refine ⟨34300063870197492118435921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45733418493596656157914561 34300063870197492118435921)
            ·
              refine ⟨25725047902648119088826941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34300063870197492118435921 25725047902648119088826941)
              ·
                refine ⟨9646892963493044658310103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25725047902648119088826941 9646892963493044658310103)
                ·
                  refine ⟨14470339445239566987465155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9646892963493044658310103 14470339445239566987465155)
                  ·
                    refine ⟨21705509167859350481197733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14470339445239566987465155 21705509167859350481197733)
                    ·
                      refine ⟨4069782968973628215224575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21705509167859350481197733 4069782968973628215224575)
                      ·
                        rfl

theorem cell23_7925874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 2, 3, 1, 1, 4].length) (baseStart_7925874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7925874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7925874 prefixEnd_7925874 := by exact prefixLift 7925874
  have htrace : WordTrace (prefixWord ++ tailWord_7925874) baseStart_7925874 baseEnd_7925874 := by
    simpa [prefixWord, tailWord_7925874, baseEnd_7925874] using wordTrace_append hprefix tailTrace_7925874
  have hstable : (prefixWord ++ tailWord_7925874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7925874).length < 2 ^ (prefixWord ++ tailWord_7925874).sum := by decide
  have hdescent : baseEnd_7925874 < baseStart_7925874 := by decide
  rcases family_descends (prefixWord ++ tailWord_7925874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7925891 : List Nat := [1, 1, 1, 3, 3, 3, 3, 1, 3, 2, 2]
def baseStart_7925891 : Nat := 118140960795 + 7925891 * 2 ^ 59
def prefixEnd_7925891 : Nat := 4983230072969 + 3 ^ 40 * 7925891 * 2
def baseEnd_7925891 : Nat := 4069791698144754648711997

theorem tailTrace_7925891 : CollatzResearch.WordTrace tailWord_7925891 prefixEnd_7925891 4069791698144754648711997 := by
  unfold tailWord_7925891
  simp only [CollatzResearch.WordTrace]
  refine ⟨289080993728858016259569527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192720662485905344173046351 289080993728858016259569527)
  ·
    refine ⟨433621490593287024389354291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289080993728858016259569527 433621490593287024389354291)
    ·
      refine ⟨650432235889930536584031437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 433621490593287024389354291 650432235889930536584031437)
      ·
        refine ⟨243912088458723951219011789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 650432235889930536584031437 243912088458723951219011789)
        ·
          refine ⟨91467033172021481707129421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 243912088458723951219011789 91467033172021481707129421)
          ·
            refine ⟨34300137439508055640173533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91467033172021481707129421 34300137439508055640173533)
            ·
              refine ⟨12862551539815520865065075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34300137439508055640173533 12862551539815520865065075)
              ·
                refine ⟨19293827309723281297597613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12862551539815520865065075 19293827309723281297597613)
                ·
                  refine ⟨7235185241146230486599105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19293827309723281297597613 7235185241146230486599105)
                  ·
                    refine ⟨5426388930859672864949329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7235185241146230486599105 5426388930859672864949329)
                    ·
                      refine ⟨4069791698144754648711997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5426388930859672864949329 4069791698144754648711997)
                      ·
                        rfl

theorem cell23_7925891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 3, 1, 3, 2, 2].length) (baseStart_7925891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7925891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7925891 prefixEnd_7925891 := by exact prefixLift 7925891
  have htrace : WordTrace (prefixWord ++ tailWord_7925891) baseStart_7925891 baseEnd_7925891 := by
    simpa [prefixWord, tailWord_7925891, baseEnd_7925891] using wordTrace_append hprefix tailTrace_7925891
  have hstable : (prefixWord ++ tailWord_7925891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7925891).length < 2 ^ (prefixWord ++ tailWord_7925891).sum := by decide
  have hdescent : baseEnd_7925891 < baseStart_7925891 := by decide
  rcases family_descends (prefixWord ++ tailWord_7925891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7925907 : List Nat := [1, 1, 1, 2, 1, 2, 3, 5, 1, 3, 3]
def baseStart_7925907 : Nat := 118140960795 + 7925907 * 2 ^ 59
def prefixEnd_7925907 : Nat := 4983230072969 + 3 ^ 40 * 7925907 * 2
def baseEnd_7925907 : Nat := 4069799913835226586111923

theorem tailTrace_7925907 : CollatzResearch.WordTrace tailWord_7925907 prefixEnd_7925907 4069799913835226586111923 := by
  unfold tailWord_7925907
  simp only [CollatzResearch.WordTrace]
  refine ⟨289081577296800050992151975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192721051531200033994767983 289081577296800050992151975)
  ·
    refine ⟨433622365945200076488227963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289081577296800050992151975 433622365945200076488227963)
    ·
      refine ⟨650433548917800114732341945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 433622365945200076488227963 650433548917800114732341945)
      ·
        refine ⟨487825161688350086049256459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 650433548917800114732341945 487825161688350086049256459)
        ·
          refine ⟨731737742532525129073884689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 487825161688350086049256459 731737742532525129073884689)
          ·
            refine ⟨548803306899393846805413517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 731737742532525129073884689 548803306899393846805413517)
            ·
              refine ⟨205801240087272692552030069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 548803306899393846805413517 205801240087272692552030069)
              ·
                refine ⟨19293866258181814926752819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 205801240087272692552030069 19293866258181814926752819)
                ·
                  refine ⟨28940799387272722390129229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19293866258181814926752819 28940799387272722390129229)
                  ·
                    refine ⟨10852799770227270896298461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28940799387272722390129229 10852799770227270896298461)
                    ·
                      refine ⟨4069799913835226586111923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10852799770227270896298461 4069799913835226586111923)
                      ·
                        rfl

theorem cell23_7925907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 5, 1, 3, 3].length) (baseStart_7925907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7925907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7925907 prefixEnd_7925907 := by exact prefixLift 7925907
  have htrace : WordTrace (prefixWord ++ tailWord_7925907) baseStart_7925907 baseEnd_7925907 := by
    simpa [prefixWord, tailWord_7925907, baseEnd_7925907] using wordTrace_append hprefix tailTrace_7925907
  have hstable : (prefixWord ++ tailWord_7925907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7925907).length < 2 ^ (prefixWord ++ tailWord_7925907).sum := by decide
  have hdescent : baseEnd_7925907 < baseStart_7925907 := by decide
  rcases family_descends (prefixWord ++ tailWord_7925907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7925967 : List Nat := [1, 1, 2, 1, 1, 3, 3, 2, 2, 4, 3]
def baseStart_7925967 : Nat := 118140960795 + 7925967 * 2 ^ 59
def prefixEnd_7925967 : Nat := 4983230072969 + 3 ^ 40 * 7925967 * 2
def baseEnd_7925967 : Nat := 4069830722674496351361647

theorem tailTrace_7925967 : CollatzResearch.WordTrace tailWord_7925967 prefixEnd_7925967 4069830722674496351361647 := by
  unfold tailWord_7925967
  simp only [CollatzResearch.WordTrace]
  refine ⟨289083765676582681239336155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192722510451055120826224103 289083765676582681239336155)
  ·
    refine ⟨433625648514874021859004233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289083765676582681239336155 433625648514874021859004233)
    ·
      refine ⟨325219236386155516394253175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 433625648514874021859004233 325219236386155516394253175)
      ·
        refine ⟨487828854579233274591379763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 325219236386155516394253175 487828854579233274591379763)
        ·
          refine ⟨731743281868849911887069645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 487828854579233274591379763 731743281868849911887069645)
          ·
            refine ⟨274403730700818716957651117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 731743281868849911887069645 274403730700818716957651117)
            ·
              refine ⟨102901399012807018859119169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 274403730700818716957651117 102901399012807018859119169)
              ·
                refine ⟨77176049259605264144339377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102901399012807018859119169 77176049259605264144339377)
                ·
                  refine ⟨57882036944703948108254533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77176049259605264144339377 57882036944703948108254533)
                  ·
                    refine ⟨10852881927131990270297725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 57882036944703948108254533 10852881927131990270297725)
                    ·
                      refine ⟨4069830722674496351361647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10852881927131990270297725 4069830722674496351361647)
                      ·
                        rfl

theorem cell23_7925967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 2, 2, 4, 3].length) (baseStart_7925967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7925967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7925967 prefixEnd_7925967 := by exact prefixLift 7925967
  have htrace : WordTrace (prefixWord ++ tailWord_7925967) baseStart_7925967 baseEnd_7925967 := by
    simpa [prefixWord, tailWord_7925967, baseEnd_7925967] using wordTrace_append hprefix tailTrace_7925967
  have hstable : (prefixWord ++ tailWord_7925967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7925967).length < 2 ^ (prefixWord ++ tailWord_7925967).sum := by decide
  have hdescent : baseEnd_7925967 < baseStart_7925967 := by decide
  rcases family_descends (prefixWord ++ tailWord_7925967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7926017 : List Nat := [1, 2, 4, 1, 1, 2, 1, 1, 3, 7]
def baseStart_7926017 : Nat := 118140960795 + 7926017 * 2 ^ 59
def prefixEnd_7926017 : Nat := 4983230072969 + 3 ^ 40 * 7926017 * 2
def baseEnd_7926017 : Nat := 1356618798902407051912139

theorem tailTrace_7926017 : CollatzResearch.WordTrace tailWord_7926017 prefixEnd_7926017 1356618798902407051912139 := by
  unfold tailWord_7926017
  simp only [CollatzResearch.WordTrace]
  refine ⟨289085589326401539778656305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192723726217601026519104203 289085589326401539778656305)
  ·
    refine ⟨216814191994801154833992229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 289085589326401539778656305 216814191994801154833992229)
    ·
      refine ⟨40652660999025216531373543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 216814191994801154833992229 40652660999025216531373543)
      ·
        refine ⟨60978991498537824797060315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40652660999025216531373543 60978991498537824797060315)
        ·
          refine ⟨91468487247806737195590473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60978991498537824797060315 91468487247806737195590473)
          ·
            refine ⟨68601365435855052896692855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91468487247806737195590473 68601365435855052896692855)
            ·
              refine ⟨102902048153782579345039283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68601365435855052896692855 102902048153782579345039283)
              ·
                refine ⟨154353072230673869017558925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102902048153782579345039283 154353072230673869017558925)
                ·
                  refine ⟨57882402086502700881584597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 154353072230673869017558925 57882402086502700881584597)
                  ·
                    refine ⟨1356618798902407051912139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 57882402086502700881584597 1356618798902407051912139)
                    ·
                      rfl

theorem cell23_7926017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 1, 3, 7].length) (baseStart_7926017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7926017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7926017 prefixEnd_7926017 := by exact prefixLift 7926017
  have htrace : WordTrace (prefixWord ++ tailWord_7926017) baseStart_7926017 baseEnd_7926017 := by
    simpa [prefixWord, tailWord_7926017, baseEnd_7926017] using wordTrace_append hprefix tailTrace_7926017
  have hstable : (prefixWord ++ tailWord_7926017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7926017).length < 2 ^ (prefixWord ++ tailWord_7926017).sum := by decide
  have hdescent : baseEnd_7926017 < baseStart_7926017 := by decide
  rcases family_descends (prefixWord ++ tailWord_7926017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7926055 : List Nat := [1, 1, 8, 1, 1, 2, 1, 1, 7]
def baseStart_7926055 : Nat := 118140960795 + 7926055 * 2 ^ 59
def prefixEnd_7926055 : Nat := 4983230072969 + 3 ^ 40 * 7926055 * 2
def baseEnd_7926055 : Nat := 452208434330232445229027

theorem tailTrace_7926055 : CollatzResearch.WordTrace tailWord_7926055 prefixEnd_7926055 452208434330232445229027 := by
  unfold tailWord_7926055
  simp only [CollatzResearch.WordTrace]
  refine ⟨289086975300263872268539619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192724650200175914845693079 289086975300263872268539619)
  ·
    refine ⟨433630462950395808402809429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289086975300263872268539619 433630462950395808402809429)
    ·
      refine ⟨5081606987699950879720423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 433630462950395808402809429 5081606987699950879720423)
      ·
        refine ⟨7622410481549926319580635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5081606987699950879720423 7622410481549926319580635)
        ·
          refine ⟨11433615722324889479370953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7622410481549926319580635 11433615722324889479370953)
          ·
            refine ⟨8575211791743667109528215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11433615722324889479370953 8575211791743667109528215)
            ·
              refine ⟨12862817687615500664292323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8575211791743667109528215 12862817687615500664292323)
              ·
                refine ⟨19294226531423250996438485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12862817687615500664292323 19294226531423250996438485)
                ·
                  refine ⟨452208434330232445229027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19294226531423250996438485 452208434330232445229027)
                  ·
                    rfl

theorem cell23_7926055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 2, 1, 1, 7].length) (baseStart_7926055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7926055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7926055 prefixEnd_7926055 := by exact prefixLift 7926055
  have htrace : WordTrace (prefixWord ++ tailWord_7926055) baseStart_7926055 baseEnd_7926055 := by
    simpa [prefixWord, tailWord_7926055, baseEnd_7926055] using wordTrace_append hprefix tailTrace_7926055
  have hstable : (prefixWord ++ tailWord_7926055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7926055).length < 2 ^ (prefixWord ++ tailWord_7926055).sum := by decide
  have hdescent : baseEnd_7926055 < baseStart_7926055 := by decide
  rcases family_descends (prefixWord ++ tailWord_7926055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7926064 : List Nat := [2, 1, 1, 1, 2, 2, 2, 5, 3, 4]
def baseStart_7926064 : Nat := 118140960795 + 7926064 * 2 ^ 59
def prefixEnd_7926064 : Nat := 4983230072969 + 3 ^ 40 * 7926064 * 2
def baseEnd_7926064 : Nat := 1356626843432660823949567

theorem tailTrace_7926064 : CollatzResearch.WordTrace tailWord_7926064 prefixEnd_7926064 1356626843432660823949567 := by
  unfold tailWord_7926064
  simp only [CollatzResearch.WordTrace]
  refine ⟨144543651778615633402808623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192724869038154177870411497 144543651778615633402808623)
  ·
    refine ⟨216815477667923450104212935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144543651778615633402808623 216815477667923450104212935)
    ·
      refine ⟨325223216501885175156319403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216815477667923450104212935 325223216501885175156319403)
      ·
        refine ⟨487834824752827762734479105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 325223216501885175156319403 487834824752827762734479105)
        ·
          refine ⟨365876118564620822050859329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 487834824752827762734479105 365876118564620822050859329)
          ·
            refine ⟨274407088923465616538144497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 365876118564620822050859329 274407088923465616538144497)
            ·
              refine ⟨205805316692599212403608373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 274407088923465616538144497 205805316692599212403608373)
              ·
                refine ⟨19294248439931176162838285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 205805316692599212403608373 19294248439931176162838285)
                ·
                  refine ⟨7235343164974191061064357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19294248439931176162838285 7235343164974191061064357)
                  ·
                    refine ⟨1356626843432660823949567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7235343164974191061064357 1356626843432660823949567)
                    ·
                      rfl

theorem cell23_7926064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 5, 3, 4].length) (baseStart_7926064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7926064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7926064 prefixEnd_7926064 := by exact prefixLift 7926064
  have htrace : WordTrace (prefixWord ++ tailWord_7926064) baseStart_7926064 baseEnd_7926064 := by
    simpa [prefixWord, tailWord_7926064, baseEnd_7926064] using wordTrace_append hprefix tailTrace_7926064
  have hstable : (prefixWord ++ tailWord_7926064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7926064).length < 2 ^ (prefixWord ++ tailWord_7926064).sum := by decide
  have hdescent : baseEnd_7926064 < baseStart_7926064 := by decide
  rcases family_descends (prefixWord ++ tailWord_7926064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7926121 : List Nat := [1, 2, 1, 1, 1, 3, 4, 3, 3, 1, 3]
def baseStart_7926121 : Nat := 118140960795 + 7926121 * 2 ^ 59
def prefixEnd_7926121 : Nat := 4983230072969 + 3 ^ 40 * 7926121 * 2
def baseEnd_7926121 : Nat := 4069909798695288748835939

theorem tailTrace_7926121 : CollatzResearch.WordTrace tailWord_7926121 prefixEnd_7926121 4069909798695288748835939 := by
  unfold tailWord_7926121
  simp only [CollatzResearch.WordTrace]
  refine ⟨289089382518024765540442217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192726255012016510360294811 289089382518024765540442217)
  ·
    refine ⟨216817036888518574155331663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 289089382518024765540442217 216817036888518574155331663)
    ·
      refine ⟨325225555332777861232997495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216817036888518574155331663 325225555332777861232997495)
      ·
        refine ⟨487838332999166791849496243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 325225555332777861232997495 487838332999166791849496243)
        ·
          refine ⟨731757499498750187774244365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 487838332999166791849496243 731757499498750187774244365)
          ·
            refine ⟨274409062312031320415341637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 731757499498750187774244365 274409062312031320415341637)
            ·
              refine ⟨51451699183505872577876557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 274409062312031320415341637 51451699183505872577876557)
              ·
                refine ⟨19294387193814702216703709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51451699183505872577876557 19294387193814702216703709)
                ·
                  refine ⟨7235395197680513331263891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19294387193814702216703709 7235395197680513331263891)
                  ·
                    refine ⟨10853092796520769996895837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7235395197680513331263891 10853092796520769996895837)
                    ·
                      refine ⟨4069909798695288748835939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10853092796520769996895837 4069909798695288748835939)
                      ·
                        rfl

theorem cell23_7926121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 3, 3, 1, 3].length) (baseStart_7926121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7926121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7926121 prefixEnd_7926121 := by exact prefixLift 7926121
  have htrace : WordTrace (prefixWord ++ tailWord_7926121) baseStart_7926121 baseEnd_7926121 := by
    simpa [prefixWord, tailWord_7926121, baseEnd_7926121] using wordTrace_append hprefix tailTrace_7926121
  have hstable : (prefixWord ++ tailWord_7926121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7926121).length < 2 ^ (prefixWord ++ tailWord_7926121).sum := by decide
  have hdescent : baseEnd_7926121 < baseStart_7926121 := by decide
  rcases family_descends (prefixWord ++ tailWord_7926121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7926155 : List Nat := [1, 1, 1, 1, 4, 5, 2, 3, 1, 1, 3]
def baseStart_7926155 : Nat := 118140960795 + 7926155 * 2 ^ 59
def prefixEnd_7926155 : Nat := 4983230072969 + 3 ^ 40 * 7926155 * 2
def baseEnd_7926155 : Nat := 4069927257037541615810783

theorem tailTrace_7926155 : CollatzResearch.WordTrace tailWord_7926155 prefixEnd_7926155 4069927257037541615810783 := by
  unfold tailWord_7926155
  simp only [CollatzResearch.WordTrace]
  refine ⟨289090622599901589347179919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192727081733267726231453279 289090622599901589347179919)
  ·
    refine ⟨433635933899852384020769879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289090622599901589347179919 433635933899852384020769879)
    ·
      refine ⟨650453900849778576031154819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 433635933899852384020769879 650453900849778576031154819)
      ·
        refine ⟨975680851274667864046732229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 650453900849778576031154819 975680851274667864046732229)
        ·
          refine ⟨182940159614000224508762293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 975680851274667864046732229 182940159614000224508762293)
          ·
            refine ⟨17150639963812521047696465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 182940159614000224508762293 17150639963812521047696465)
            ·
              refine ⟨12862979972859390785772349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17150639963812521047696465 12862979972859390785772349)
              ·
                refine ⟨4823617489822271544664631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12862979972859390785772349 4823617489822271544664631)
                ·
                  refine ⟨7235426234733407316996947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4823617489822271544664631 7235426234733407316996947)
                  ·
                    refine ⟨10853139352100110975495421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7235426234733407316996947 10853139352100110975495421)
                    ·
                      refine ⟨4069927257037541615810783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10853139352100110975495421 4069927257037541615810783)
                      ·
                        rfl

theorem cell23_7926155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 2, 3, 1, 1, 3].length) (baseStart_7926155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7926155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7926155 prefixEnd_7926155 := by exact prefixLift 7926155
  have htrace : WordTrace (prefixWord ++ tailWord_7926155) baseStart_7926155 baseEnd_7926155 := by
    simpa [prefixWord, tailWord_7926155, baseEnd_7926155] using wordTrace_append hprefix tailTrace_7926155
  have hstable : (prefixWord ++ tailWord_7926155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7926155).length < 2 ^ (prefixWord ++ tailWord_7926155).sum := by decide
  have hdescent : baseEnd_7926155 < baseStart_7926155 := by decide
  rcases family_descends (prefixWord ++ tailWord_7926155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7926158 : List Nat := [4, 1, 1, 4, 1, 2, 1, 3, 1, 5]
def baseStart_7926158 : Nat := 118140960795 + 7926158 * 2 ^ 59
def prefixEnd_7926158 : Nat := 4983230072969 + 3 ^ 40 * 7926158 * 2
def baseEnd_7926158 : Nat := 1356642932493168368024423

theorem tailTrace_7926158 : CollatzResearch.WordTrace tailWord_7926158 prefixEnd_7926158 1356642932493168368024423 := by
  unfold tailWord_7926158
  simp only [CollatzResearch.WordTrace]
  refine ⟨36136341502361340107442391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 192727154679260480573026085 36136341502361340107442391)
  ·
    refine ⟨54204512253542010161163587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36136341502361340107442391 54204512253542010161163587)
    ·
      refine ⟨81306768380313015241745381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54204512253542010161163587 81306768380313015241745381)
      ·
        refine ⟨15245019071308690357827259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81306768380313015241745381 15245019071308690357827259)
        ·
          refine ⟨22867528606963035536740889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15245019071308690357827259 22867528606963035536740889)
          ·
            refine ⟨17150646455222276652555667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22867528606963035536740889 17150646455222276652555667)
            ·
              refine ⟨25725969682833414978833501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17150646455222276652555667 25725969682833414978833501)
              ·
                refine ⟨9647238631062530617062563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25725969682833414978833501 9647238631062530617062563)
                ·
                  refine ⟨14470857946593795925593845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9647238631062530617062563 14470857946593795925593845)
                  ·
                    refine ⟨1356642932493168368024423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14470857946593795925593845 1356642932493168368024423)
                    ·
                      rfl

theorem cell23_7926158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 1, 3, 1, 5].length) (baseStart_7926158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7926158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7926158 prefixEnd_7926158 := by exact prefixLift 7926158
  have htrace : WordTrace (prefixWord ++ tailWord_7926158) baseStart_7926158 baseEnd_7926158 := by
    simpa [prefixWord, tailWord_7926158, baseEnd_7926158] using wordTrace_append hprefix tailTrace_7926158
  have hstable : (prefixWord ++ tailWord_7926158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7926158).length < 2 ^ (prefixWord ++ tailWord_7926158).sum := by decide
  have hdescent : baseEnd_7926158 < baseStart_7926158 := by decide
  rcases family_descends (prefixWord ++ tailWord_7926158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7926201 : List Nat := [1, 2, 1, 4, 3, 1, 4, 7]
def baseStart_7926201 : Nat := 118140960795 + 7926201 * 2 ^ 59
def prefixEnd_7926201 : Nat := 4983230072969 + 3 ^ 40 * 7926201 * 2
def baseEnd_7926201 : Nat := 150738921375838830956873

theorem tailTrace_7926201 : CollatzResearch.WordTrace tailWord_7926201 prefixEnd_7926201 150738921375838830956873 := by
  unfold tailWord_7926201
  simp only [CollatzResearch.WordTrace]
  refine ⟨289092300357734939203354457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192728200238489959468902971 289092300357734939203354457)
  ·
    refine ⟨216819225268301204402515843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 289092300357734939203354457 216819225268301204402515843)
    ·
      refine ⟨325228837902451806603773765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216819225268301204402515843 325228837902451806603773765)
      ·
        refine ⟨60980407106709713738207581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 325228837902451806603773765 60980407106709713738207581)
        ·
          refine ⟨22867652665016142651827843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60980407106709713738207581 22867652665016142651827843)
          ·
            refine ⟨34301478997524213977741765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22867652665016142651827843 34301478997524213977741765)
            ·
              refine ⟨6431527312035790120826581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34301478997524213977741765 6431527312035790120826581)
              ·
                refine ⟨150738921375838830956873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6431527312035790120826581 150738921375838830956873)
                ·
                  rfl

theorem cell23_7926201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 4, 7].length) (baseStart_7926201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7926201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7926201 prefixEnd_7926201 := by exact prefixLift 7926201
  have htrace : WordTrace (prefixWord ++ tailWord_7926201) baseStart_7926201 baseEnd_7926201 := by
    simpa [prefixWord, tailWord_7926201, baseEnd_7926201] using wordTrace_append hprefix tailTrace_7926201
  have hstable : (prefixWord ++ tailWord_7926201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7926201).length < 2 ^ (prefixWord ++ tailWord_7926201).sum := by decide
  have hdescent : baseEnd_7926201 < baseStart_7926201 := by decide
  rcases family_descends (prefixWord ++ tailWord_7926201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7926229 : List Nat := [1, 3, 2, 3, 1, 3, 3, 2, 1, 2, 2]
def baseStart_7926229 : Nat := 118140960795 + 7926229 * 2 ^ 59
def prefixEnd_7926229 : Nat := 4983230072969 + 3 ^ 40 * 7926229 * 2
def baseEnd_7926229 : Nat := 4069965254605974326285443

theorem tailTrace_7926229 : CollatzResearch.WordTrace tailWord_7926229 prefixEnd_7926229 4069965254605974326285443 := by
  unfold tailWord_7926229
  simp only [CollatzResearch.WordTrace]
  refine ⟨289093321601633499985373741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192728881067755666656915827 289093321601633499985373741)
  ·
    refine ⟨108409995600612562494515153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 289093321601633499985373741 108409995600612562494515153)
    ·
      refine ⟨81307496700459421870886365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108409995600612562494515153 81307496700459421870886365)
      ·
        refine ⟨30490311262672283201582387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81307496700459421870886365 30490311262672283201582387)
        ·
          refine ⟨45735466894008424802373581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30490311262672283201582387 45735466894008424802373581)
          ·
            refine ⟨17150800085253159300890093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45735466894008424802373581 17150800085253159300890093)
            ·
              refine ⟨6431550031969934737833785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17150800085253159300890093 6431550031969934737833785)
              ·
                refine ⟨4823662523977451053375339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6431550031969934737833785 4823662523977451053375339)
                ·
                  refine ⟨7235493785966176580063009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4823662523977451053375339 7235493785966176580063009)
                  ·
                    refine ⟨5426620339474632435047257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7235493785966176580063009 5426620339474632435047257)
                    ·
                      refine ⟨4069965254605974326285443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5426620339474632435047257 4069965254605974326285443)
                      ·
                        rfl

theorem cell23_7926229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 3, 2, 1, 2, 2].length) (baseStart_7926229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7926229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7926229 prefixEnd_7926229 := by exact prefixLift 7926229
  have htrace : WordTrace (prefixWord ++ tailWord_7926229) baseStart_7926229 baseEnd_7926229 := by
    simpa [prefixWord, tailWord_7926229, baseEnd_7926229] using wordTrace_append hprefix tailTrace_7926229
  have hstable : (prefixWord ++ tailWord_7926229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7926229).length < 2 ^ (prefixWord ++ tailWord_7926229).sum := by decide
  have hdescent : baseEnd_7926229 < baseStart_7926229 := by decide
  rcases family_descends (prefixWord ++ tailWord_7926229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7926285 : List Nat := [1, 7, 1, 1, 1, 1, 1, 1, 2, 3, 4]
def baseStart_7926285 : Nat := 118140960795 + 7926285 * 2 ^ 59
def prefixEnd_7926285 : Nat := 4983230072969 + 3 ^ 40 * 7926285 * 2
def baseEnd_7926285 : Nat := 4069994009522626107185185

theorem tailTrace_7926285 : CollatzResearch.WordTrace tailWord_7926285 prefixEnd_7926285 4069994009522626107185185 := by
  unfold tailWord_7926285
  simp only [CollatzResearch.WordTrace]
  refine ⟨289095364089430621549412309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192730242726287081032941539 289095364089430621549412309)
  ·
    refine ⟨6775672595846030192564351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 289095364089430621549412309 6775672595846030192564351)
    ·
      refine ⟨10163508893769045288846527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6775672595846030192564351 10163508893769045288846527)
      ·
        refine ⟨15245263340653567933269791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10163508893769045288846527 15245263340653567933269791)
        ·
          refine ⟨22867895010980351899904687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15245263340653567933269791 22867895010980351899904687)
          ·
            refine ⟨34301842516470527849857031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22867895010980351899904687 34301842516470527849857031)
            ·
              refine ⟨51452763774705791774785547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34301842516470527849857031 51452763774705791774785547)
              ·
                refine ⟨77179145662058687662178321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51452763774705791774785547 77179145662058687662178321)
                ·
                  refine ⟨57884359246544015746633741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77179145662058687662178321 57884359246544015746633741)
                  ·
                    refine ⟨21706634717454005904987653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 57884359246544015746633741 21706634717454005904987653)
                    ·
                      refine ⟨4069994009522626107185185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21706634717454005904987653 4069994009522626107185185)
                      ·
                        rfl

theorem cell23_7926285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 1, 2, 3, 4].length) (baseStart_7926285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7926285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7926285 prefixEnd_7926285 := by exact prefixLift 7926285
  have htrace : WordTrace (prefixWord ++ tailWord_7926285) baseStart_7926285 baseEnd_7926285 := by
    simpa [prefixWord, tailWord_7926285, baseEnd_7926285] using wordTrace_append hprefix tailTrace_7926285
  have hstable : (prefixWord ++ tailWord_7926285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7926285).length < 2 ^ (prefixWord ++ tailWord_7926285).sum := by decide
  have hdescent : baseEnd_7926285 < baseStart_7926285 := by decide
  rcases family_descends (prefixWord ++ tailWord_7926285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7926342 : List Nat := [6, 1, 1, 1, 2, 1, 2, 4, 5]
def baseStart_7926342 : Nat := 118140960795 + 7926342 * 2 ^ 59
def prefixEnd_7926342 : Nat := 4983230072969 + 3 ^ 40 * 7926342 * 2
def baseEnd_7926342 : Nat := 452224808657770264908047

theorem tailTrace_7926342 : CollatzResearch.WordTrace tailWord_7926342 prefixEnd_7926342 452224808657770264908047 := by
  unfold tailWord_7926342
  simp only [CollatzResearch.WordTrace]
  refine ⟨9034295095319503758882415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 192731628700149413522824853 9034295095319503758882415)
  ·
    refine ⟨13551442642979255638323623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9034295095319503758882415 13551442642979255638323623)
    ·
      refine ⟨20327163964468883457485435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13551442642979255638323623 20327163964468883457485435)
      ·
        refine ⟨30490745946703325186228153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20327163964468883457485435 30490745946703325186228153)
        ·
          refine ⟨22868059460027493889671115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30490745946703325186228153 22868059460027493889671115)
          ·
            refine ⟨34302089190041240834506673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22868059460027493889671115 34302089190041240834506673)
            ·
              refine ⟨25726566892530930625880005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34302089190041240834506673 25726566892530930625880005)
              ·
                refine ⟨4823731292349549492352501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25726566892530930625880005 4823731292349549492352501)
                ·
                  refine ⟨452224808657770264908047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4823731292349549492352501 452224808657770264908047)
                  ·
                    rfl

theorem cell23_7926342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 2, 4, 5].length) (baseStart_7926342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7926342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7926342 prefixEnd_7926342 := by exact prefixLift 7926342
  have htrace : WordTrace (prefixWord ++ tailWord_7926342) baseStart_7926342 baseEnd_7926342 := by
    simpa [prefixWord, tailWord_7926342, baseEnd_7926342] using wordTrace_append hprefix tailTrace_7926342
  have hstable : (prefixWord ++ tailWord_7926342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7926342).length < 2 ^ (prefixWord ++ tailWord_7926342).sum := by decide
  have hdescent : baseEnd_7926342 < baseStart_7926342 := by decide
  rcases family_descends (prefixWord ++ tailWord_7926342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7926368 : List Nat := [2, 1, 1, 3, 2, 1, 4, 2, 3, 4]
def baseStart_7926368 : Nat := 118140960795 + 7926368 * 2 ^ 59
def prefixEnd_7926368 : Nat := 4983230072969 + 3 ^ 40 * 7926368 * 2
def baseEnd_7926368 : Nat := 1356678876138983094149101

theorem tailTrace_7926368 : CollatzResearch.WordTrace tailWord_7926368 prefixEnd_7926368 1356678876138983094149101 := by
  unfold tailWord_7926368
  simp only [CollatzResearch.WordTrace]
  refine ⟨144549195674064963362341879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192732260898753284483122505 144549195674064963362341879)
  ·
    refine ⟨216823793511097445043512819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144549195674064963362341879 216823793511097445043512819)
    ·
      refine ⟨325235690266646167565269229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216823793511097445043512819 325235690266646167565269229)
      ·
        refine ⟨121963383849992312836975961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 325235690266646167565269229 121963383849992312836975961)
        ·
          refine ⟨91472537887494234627731971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121963383849992312836975961 91472537887494234627731971)
          ·
            refine ⟨137208806831241351941597957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91472537887494234627731971 137208806831241351941597957)
            ·
              refine ⟨25726651280857753489049617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 137208806831241351941597957 25726651280857753489049617)
              ·
                refine ⟨19294988460643315116787213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25726651280857753489049617 19294988460643315116787213)
                ·
                  refine ⟨7235620672741243168795205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19294988460643315116787213 7235620672741243168795205)
                  ·
                    refine ⟨1356678876138983094149101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7235620672741243168795205 1356678876138983094149101)
                    ·
                      rfl

theorem cell23_7926368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 4, 2, 3, 4].length) (baseStart_7926368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7926368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7926368 prefixEnd_7926368 := by exact prefixLift 7926368
  have htrace : WordTrace (prefixWord ++ tailWord_7926368) baseStart_7926368 baseEnd_7926368 := by
    simpa [prefixWord, tailWord_7926368, baseEnd_7926368] using wordTrace_append hprefix tailTrace_7926368
  have hstable : (prefixWord ++ tailWord_7926368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7926368).length < 2 ^ (prefixWord ++ tailWord_7926368).sum := by decide
  have hdescent : baseEnd_7926368 < baseStart_7926368 := by decide
  rcases family_descends (prefixWord ++ tailWord_7926368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7926371 : List Nat := [1, 1, 1, 5, 1, 2, 1, 1, 2, 4, 4]
def baseStart_7926371 : Nat := 118140960795 + 7926371 * 2 ^ 59
def prefixEnd_7926371 : Nat := 4983230072969 + 3 ^ 40 * 7926371 * 2
def baseEnd_7926371 : Nat := 4070038168858912770709789

theorem tailTrace_7926371 : CollatzResearch.WordTrace tailWord_7926371 prefixEnd_7926371 4070038168858912770709789 := by
  unfold tailWord_7926371
  simp only [CollatzResearch.WordTrace]
  refine ⟨289098500767119058237042967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192732333844746038824695311 289098500767119058237042967)
  ·
    refine ⟨433647751150678587355564451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289098500767119058237042967 433647751150678587355564451)
    ·
      refine ⟨650471626726017881033346677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 433647751150678587355564451 650471626726017881033346677)
      ·
        refine ⟨60981715005564176346876251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 650471626726017881033346677 60981715005564176346876251)
        ·
          refine ⟨91472572508346264520314377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60981715005564176346876251 91472572508346264520314377)
          ·
            refine ⟨68604429381259698390235783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91472572508346264520314377 68604429381259698390235783)
            ·
              refine ⟨102906644071889547585353675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68604429381259698390235783 102906644071889547585353675)
              ·
                refine ⟨154359966107834321378030513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102906644071889547585353675 154359966107834321378030513)
                ·
                  refine ⟨115769974580875741033522885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 154359966107834321378030513 115769974580875741033522885)
                  ·
                    refine ⟨21706870233914201443785541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 115769974580875741033522885 21706870233914201443785541)
                    ·
                      refine ⟨4070038168858912770709789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21706870233914201443785541 4070038168858912770709789)
                      ·
                        rfl

theorem cell23_7926371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 1, 2, 4, 4].length) (baseStart_7926371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7926371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7926371 prefixEnd_7926371 := by exact prefixLift 7926371
  have htrace : WordTrace (prefixWord ++ tailWord_7926371) baseStart_7926371 baseEnd_7926371 := by
    simpa [prefixWord, tailWord_7926371, baseEnd_7926371] using wordTrace_append hprefix tailTrace_7926371
  have hstable : (prefixWord ++ tailWord_7926371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7926371).length < 2 ^ (prefixWord ++ tailWord_7926371).sum := by decide
  have hdescent : baseEnd_7926371 < baseStart_7926371 := by decide
  rcases family_descends (prefixWord ++ tailWord_7926371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7926378 : List Nat := [3, 1, 3, 2, 1, 1, 1, 3, 1, 4, 3]
def baseStart_7926378 : Nat := 118140960795 + 7926378 * 2 ^ 59
def prefixEnd_7926378 : Nat := 4983230072969 + 3 ^ 40 * 7926378 * 2
def baseEnd_7926378 : Nat := 4070041763223494243322257

theorem tailTrace_7926378 : CollatzResearch.WordTrace tailWord_7926378 prefixEnd_7926378 4070041763223494243322257 := by
  unfold tailWord_7926378
  simp only [CollatzResearch.WordTrace]
  refine ⟨72274689019523424608136947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192732504052062465621698525 72274689019523424608136947)
  ·
    refine ⟨108412033529285136912205421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72274689019523424608136947 108412033529285136912205421)
    ·
      refine ⟨40654512573481926342077033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108412033529285136912205421 40654512573481926342077033)
      ·
        refine ⟨30490884430111444756557775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40654512573481926342077033 30490884430111444756557775)
        ·
          refine ⟨45736326645167167134836663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30490884430111444756557775 45736326645167167134836663)
          ·
            refine ⟨68604489967750750702254995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45736326645167167134836663 68604489967750750702254995)
            ·
              refine ⟨102906734951626126053382493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68604489967750750702254995 102906734951626126053382493)
              ·
                refine ⟨38590025606859797270018435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 102906734951626126053382493 38590025606859797270018435)
                ·
                  refine ⟨57885038410289695905027653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38590025606859797270018435 57885038410289695905027653)
                  ·
                    refine ⟨10853444701929317982192685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 57885038410289695905027653 10853444701929317982192685)
                    ·
                      refine ⟨4070041763223494243322257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10853444701929317982192685 4070041763223494243322257)
                      ·
                        rfl

theorem cell23_7926378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 3, 1, 4, 3].length) (baseStart_7926378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7926378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7926378 prefixEnd_7926378 := by exact prefixLift 7926378
  have htrace : WordTrace (prefixWord ++ tailWord_7926378) baseStart_7926378 baseEnd_7926378 := by
    simpa [prefixWord, tailWord_7926378, baseEnd_7926378] using wordTrace_append hprefix tailTrace_7926378
  have hstable : (prefixWord ++ tailWord_7926378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7926378).length < 2 ^ (prefixWord ++ tailWord_7926378).sum := by decide
  have hdescent : baseEnd_7926378 < baseStart_7926378 := by decide
  rcases family_descends (prefixWord ++ tailWord_7926378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7926441 : List Nat := [1, 2, 1, 1, 1, 1, 2, 5, 3, 6]
def baseStart_7926441 : Nat := 118140960795 + 7926441 * 2 ^ 59
def prefixEnd_7926441 : Nat := 4983230072969 + 3 ^ 40 * 7926441 * 2
def baseEnd_7926441 : Nat := 1356691370834909165611489

theorem tailTrace_7926441 : CollatzResearch.WordTrace tailWord_7926441 prefixEnd_7926441 1356691370834909165611489 := by
  unfold tailWord_7926441
  simp only [CollatzResearch.WordTrace]
  refine ⟨289101053876865460192091177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192734035917910306794727451 289101053876865460192091177)
  ·
    refine ⟨216825790407649095144068383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 289101053876865460192091177 216825790407649095144068383)
    ·
      refine ⟨325238685611473642716102575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216825790407649095144068383 325238685611473642716102575)
      ·
        refine ⟨487858028417210464074153863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 325238685611473642716102575 487858028417210464074153863)
        ·
          refine ⟨731787042625815696111230795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 487858028417210464074153863 731787042625815696111230795)
          ·
            refine ⟨1097680563938723544166846193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 731787042625815696111230795 1097680563938723544166846193)
            ·
              refine ⟨823260422954042658125134645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1097680563938723544166846193 823260422954042658125134645)
              ·
                refine ⟨77180664651941499199231373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 823260422954042658125134645 77180664651941499199231373)
                ·
                  refine ⟨28942749244478062199711765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77180664651941499199231373 28942749244478062199711765)
                  ·
                    refine ⟨1356691370834909165611489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28942749244478062199711765 1356691370834909165611489)
                    ·
                      rfl

theorem cell23_7926441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 5, 3, 6].length) (baseStart_7926441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7926441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7926441 prefixEnd_7926441 := by exact prefixLift 7926441
  have htrace : WordTrace (prefixWord ++ tailWord_7926441) baseStart_7926441 baseEnd_7926441 := by
    simpa [prefixWord, tailWord_7926441, baseEnd_7926441] using wordTrace_append hprefix tailTrace_7926441
  have hstable : (prefixWord ++ tailWord_7926441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7926441).length < 2 ^ (prefixWord ++ tailWord_7926441).sum := by decide
  have hdescent : baseEnd_7926441 < baseStart_7926441 := by decide
  rcases family_descends (prefixWord ++ tailWord_7926441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7926471 : List Nat := [1, 1, 4, 1, 1, 1, 2, 12]
def baseStart_7926471 : Nat := 118140960795 + 7926471 * 2 ^ 59
def prefixEnd_7926471 : Nat := 4983230072969 + 3 ^ 40 * 7926471 * 2
def baseEnd_7926471 : Nat := 150744056182383791831827

theorem tailTrace_7926471 : CollatzResearch.WordTrace tailWord_7926471 prefixEnd_7926471 150744056182383791831827 := by
  unfold tailWord_7926471
  simp only [CollatzResearch.WordTrace]
  refine ⟨289102148066756775315683267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192734765377837850210455511 289102148066756775315683267)
  ·
    refine ⟨433653222100135162973524901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289102148066756775315683267 433653222100135162973524901)
    ·
      refine ⟨81309979143775343057535919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 433653222100135162973524901 81309979143775343057535919)
      ·
        refine ⟨121964968715663014586303879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81309979143775343057535919 121964968715663014586303879)
        ·
          refine ⟨182947453073494521879455819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121964968715663014586303879 182947453073494521879455819)
          ·
            refine ⟨274421179610241782819183729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182947453073494521879455819 274421179610241782819183729)
            ·
              refine ⟨205815884707681337114387797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 274421179610241782819183729 205815884707681337114387797)
              ·
                refine ⟨150744056182383791831827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 205815884707681337114387797 150744056182383791831827)
                ·
                  rfl

theorem cell23_7926471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 12].length) (baseStart_7926471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7926471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7926471 prefixEnd_7926471 := by exact prefixLift 7926471
  have htrace : WordTrace (prefixWord ++ tailWord_7926471) baseStart_7926471 baseEnd_7926471 := by
    simpa [prefixWord, tailWord_7926471, baseEnd_7926471] using wordTrace_append hprefix tailTrace_7926471
  have hstable : (prefixWord ++ tailWord_7926471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7926471).length < 2 ^ (prefixWord ++ tailWord_7926471).sum := by decide
  have hdescent : baseEnd_7926471 < baseStart_7926471 := by decide
  rcases family_descends (prefixWord ++ tailWord_7926471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7926491 : List Nat := [1, 1, 1, 1, 1, 1, 1, 3, 3, 4, 6]
def baseStart_7926491 : Nat := 118140960795 + 7926491 * 2 ^ 59
def prefixEnd_7926491 : Nat := 4983230072969 + 3 ^ 40 * 7926491 * 2
def baseEnd_7926491 : Nat := 4070099786537452301209237

theorem tailTrace_7926491 : CollatzResearch.WordTrace tailWord_7926491 prefixEnd_7926491 4070099786537452301209237 := by
  unfold tailWord_7926491
  simp only [CollatzResearch.WordTrace]
  refine ⟨289102877526684318731411327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192735251684456212487607551 289102877526684318731411327)
  ·
    refine ⟨433654316290026478097116991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289102877526684318731411327 433654316290026478097116991)
    ·
      refine ⟨650481474435039717145675487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 433654316290026478097116991 650481474435039717145675487)
      ·
        refine ⟨975722211652559575718513231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 650481474435039717145675487 975722211652559575718513231)
        ·
          refine ⟨1463583317478839363577769847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 975722211652559575718513231 1463583317478839363577769847)
          ·
            refine ⟨2195374976218259045366654771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1463583317478839363577769847 2195374976218259045366654771)
            ·
              refine ⟨3293062464327388568049982157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2195374976218259045366654771 3293062464327388568049982157)
              ·
                refine ⟨1234898424122770713018743309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3293062464327388568049982157 1234898424122770713018743309)
                ·
                  refine ⟨463086909046039017382028741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1234898424122770713018743309 463086909046039017382028741)
                  ·
                    refine ⟨86828795446132315759130389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 463086909046039017382028741 86828795446132315759130389)
                    ·
                      refine ⟨4070099786537452301209237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 86828795446132315759130389 4070099786537452301209237)
                      ·
                        rfl

theorem cell23_7926491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 4, 6].length) (baseStart_7926491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7926491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7926491 prefixEnd_7926491 := by exact prefixLift 7926491
  have htrace : WordTrace (prefixWord ++ tailWord_7926491) baseStart_7926491 baseEnd_7926491 := by
    simpa [prefixWord, tailWord_7926491, baseEnd_7926491] using wordTrace_append hprefix tailTrace_7926491
  have hstable : (prefixWord ++ tailWord_7926491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7926491).length < 2 ^ (prefixWord ++ tailWord_7926491).sum := by decide
  have hdescent : baseEnd_7926491 < baseStart_7926491 := by decide
  rcases family_descends (prefixWord ++ tailWord_7926491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7926499 : List Nat := [1, 1, 1, 7, 1, 3, 2, 1, 1, 1, 4]
def baseStart_7926499 : Nat := 118140960795 + 7926499 * 2 ^ 59
def prefixEnd_7926499 : Nat := 4983230072969 + 3 ^ 40 * 7926499 * 2
def baseEnd_7926499 : Nat := 4070103894382688269909201

theorem tailTrace_7926499 : CollatzResearch.WordTrace tailWord_7926499 prefixEnd_7926499 4070103894382688269909201 := by
  unfold tailWord_7926499
  simp only [CollatzResearch.WordTrace]
  refine ⟨289103169310655336097702551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192735446207103557398468367 289103169310655336097702551)
  ·
    refine ⟨433654753965983004146553827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289103169310655336097702551 433654753965983004146553827)
    ·
      refine ⟨650482130948974506219830741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 433654753965983004146553827 650482130948974506219830741)
      ·
        refine ⟨15245674944116589989527283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 650482130948974506219830741 15245674944116589989527283)
        ·
          refine ⟨22868512416174884984290925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15245674944116589989527283 22868512416174884984290925)
          ·
            refine ⟨8575692156065581869109097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22868512416174884984290925 8575692156065581869109097)
            ·
              refine ⟨6431769117049186401831823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8575692156065581869109097 6431769117049186401831823)
              ·
                refine ⟨9647653675573779602747735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6431769117049186401831823 9647653675573779602747735)
                ·
                  refine ⟨14471480513360669404121603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9647653675573779602747735 14471480513360669404121603)
                  ·
                    refine ⟨21707220770041004106182405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14471480513360669404121603 21707220770041004106182405)
                    ·
                      refine ⟨4070103894382688269909201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21707220770041004106182405 4070103894382688269909201)
                      ·
                        rfl

theorem cell23_7926499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 3, 2, 1, 1, 1, 4].length) (baseStart_7926499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7926499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7926499 prefixEnd_7926499 := by exact prefixLift 7926499
  have htrace : WordTrace (prefixWord ++ tailWord_7926499) baseStart_7926499 baseEnd_7926499 := by
    simpa [prefixWord, tailWord_7926499, baseEnd_7926499] using wordTrace_append hprefix tailTrace_7926499
  have hstable : (prefixWord ++ tailWord_7926499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7926499).length < 2 ^ (prefixWord ++ tailWord_7926499).sum := by decide
  have hdescent : baseEnd_7926499 < baseStart_7926499 := by decide
  rcases family_descends (prefixWord ++ tailWord_7926499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7926572 : List Nat := [2, 2, 1, 1, 1, 4, 1, 3, 4, 2, 2]
def baseStart_7926572 : Nat := 118140960795 + 7926572 * 2 ^ 59
def prefixEnd_7926572 : Nat := 4983230072969 + 3 ^ 40 * 7926572 * 2
def baseEnd_7926572 : Nat := 4070141378470466484296365

theorem tailTrace_7926572 : CollatzResearch.WordTrace tailWord_7926572 prefixEnd_7926572 4070141378470466484296365 := by
  unfold tailWord_7926572
  simp only [CollatzResearch.WordTrace]
  refine ⟨144552915919695434782554985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192737221226260579710073313 144552915919695434782554985)
  ·
    refine ⟨108414686939771576086916239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144552915919695434782554985 108414686939771576086916239)
    ·
      refine ⟨162622030409657364130374359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108414686939771576086916239 162622030409657364130374359)
      ·
        refine ⟨243933045614486046195561539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162622030409657364130374359 243933045614486046195561539)
        ·
          refine ⟨365899568421729069293342309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 243933045614486046195561539 365899568421729069293342309)
          ·
            refine ⟨68606169079074200492501683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 365899568421729069293342309 68606169079074200492501683)
            ·
              refine ⟨102909253618611300738752525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68606169079074200492501683 102909253618611300738752525)
              ·
                refine ⟨38590970106979237777032197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 102909253618611300738752525 38590970106979237777032197)
                ·
                  refine ⟨7235806895058607083193537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38590970106979237777032197 7235806895058607083193537)
                  ·
                    refine ⟨5426855171293955312395153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7235806895058607083193537 5426855171293955312395153)
                    ·
                      refine ⟨4070141378470466484296365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5426855171293955312395153 4070141378470466484296365)
                      ·
                        rfl

theorem cell23_7926572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 2, 2].length) (baseStart_7926572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7926572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7926572 prefixEnd_7926572 := by exact prefixLift 7926572
  have htrace : WordTrace (prefixWord ++ tailWord_7926572) baseStart_7926572 baseEnd_7926572 := by
    simpa [prefixWord, tailWord_7926572, baseEnd_7926572] using wordTrace_append hprefix tailTrace_7926572
  have hstable : (prefixWord ++ tailWord_7926572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7926572).length < 2 ^ (prefixWord ++ tailWord_7926572).sum := by decide
  have hdescent : baseEnd_7926572 < baseStart_7926572 := by decide
  rcases family_descends (prefixWord ++ tailWord_7926572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7926593 : List Nat := [1, 2, 5, 3, 1, 2, 1, 2, 1, 3, 2]
def baseStart_7926593 : Nat := 118140960795 + 7926593 * 2 ^ 59
def prefixEnd_7926593 : Nat := 4983230072969 + 3 ^ 40 * 7926593 * 2
def baseEnd_7926593 : Nat := 4070152161564210902133769

theorem tailTrace_7926593 : CollatzResearch.WordTrace tailWord_7926593 prefixEnd_7926593 4070152161564210902133769 := by
  unfold tailWord_7926593
  simp only [CollatzResearch.WordTrace]
  refine ⟨289106597772314790151624433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192737731848209860101082955 289106597772314790151624433)
  ·
    refine ⟨216829948329236092613718325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 289106597772314790151624433 216829948329236092613718325)
    ·
      refine ⟨20327807655865883682536093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 216829948329236092613718325 20327807655865883682536093)
      ·
        refine ⟨7622927870949706380951035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20327807655865883682536093 7622927870949706380951035)
        ·
          refine ⟨11434391806424559571426553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7622927870949706380951035 11434391806424559571426553)
          ·
            refine ⟨8575793854818419678569915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11434391806424559571426553 8575793854818419678569915)
            ·
              refine ⟨12863690782227629517854873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8575793854818419678569915 12863690782227629517854873)
              ·
                refine ⟨9647768086670722138391155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12863690782227629517854873 9647768086670722138391155)
                ·
                  refine ⟨14471652130006083207586733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9647768086670722138391155 14471652130006083207586733)
                  ·
                    refine ⟨5426869548752281202845025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14471652130006083207586733 5426869548752281202845025)
                    ·
                      refine ⟨4070152161564210902133769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5426869548752281202845025 4070152161564210902133769)
                      ·
                        rfl

theorem cell23_7926593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 2, 1, 2, 1, 3, 2].length) (baseStart_7926593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7926593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7926593 prefixEnd_7926593 := by exact prefixLift 7926593
  have htrace : WordTrace (prefixWord ++ tailWord_7926593) baseStart_7926593 baseEnd_7926593 := by
    simpa [prefixWord, tailWord_7926593, baseEnd_7926593] using wordTrace_append hprefix tailTrace_7926593
  have hstable : (prefixWord ++ tailWord_7926593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7926593).length < 2 ^ (prefixWord ++ tailWord_7926593).sum := by decide
  have hdescent : baseEnd_7926593 < baseStart_7926593 := by decide
  rcases family_descends (prefixWord ++ tailWord_7926593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7926608 : List Nat := [2, 1, 1, 1, 1, 4, 2, 3, 1, 7]
def baseStart_7926608 : Nat := 118140960795 + 7926608 * 2 ^ 59
def prefixEnd_7926608 : Nat := 4983230072969 + 3 ^ 40 * 7926608 * 2
def baseEnd_7926608 : Nat := 1356719954591342781148733

theorem tailTrace_7926608 : CollatzResearch.WordTrace tailWord_7926608 prefixEnd_7926608 1356719954591342781148733 := by
  unfold tailWord_7926608
  simp only [CollatzResearch.WordTrace]
  refine ⟨144553572433630223856710239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192738096578173631808946985 144553572433630223856710239)
  ·
    refine ⟨216830358650445335785065359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144553572433630223856710239 216830358650445335785065359)
    ·
      refine ⟨325245537975668003677598039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216830358650445335785065359 325245537975668003677598039)
      ·
        refine ⟨487868306963502005516397059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 325245537975668003677598039 487868306963502005516397059)
        ·
          refine ⟨731802460445253008274595589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 487868306963502005516397059 731802460445253008274595589)
          ·
            refine ⟨137212961333484939051486673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 731802460445253008274595589 137212961333484939051486673)
            ·
              refine ⟨102909721000113704288615005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137212961333484939051486673 102909721000113704288615005)
              ·
                refine ⟨38591145375042639108230627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 102909721000113704288615005 38591145375042639108230627)
                ·
                  refine ⟨57886718062563958662345941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38591145375042639108230627 57886718062563958662345941)
                  ·
                    refine ⟨1356719954591342781148733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 57886718062563958662345941 1356719954591342781148733)
                    ·
                      rfl

theorem cell23_7926608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 3, 1, 7].length) (baseStart_7926608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7926608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7926608 prefixEnd_7926608 := by exact prefixLift 7926608
  have htrace : WordTrace (prefixWord ++ tailWord_7926608) baseStart_7926608 baseEnd_7926608 := by
    simpa [prefixWord, tailWord_7926608, baseEnd_7926608] using wordTrace_append hprefix tailTrace_7926608
  have hstable : (prefixWord ++ tailWord_7926608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7926608).length < 2 ^ (prefixWord ++ tailWord_7926608).sum := by decide
  have hdescent : baseEnd_7926608 < baseStart_7926608 := by decide
  rcases family_descends (prefixWord ++ tailWord_7926608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7926632 : List Nat := [2, 1, 4, 2, 1, 2, 1, 1, 2, 5, 2]
def baseStart_7926632 : Nat := 118140960795 + 7926632 * 2 ^ 59
def prefixEnd_7926632 : Nat := 4983230072969 + 3 ^ 40 * 7926632 * 2
def baseEnd_7926632 : Nat := 4070172187309736249546089

theorem tailTrace_7926632 : CollatzResearch.WordTrace tailWord_7926632 prefixEnd_7926632 4070172187309736249546089 := by
  unfold tailWord_7926632
  simp only [CollatzResearch.WordTrace]
  refine ⟨144554010109586749906147075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192738680146115666541529433 144554010109586749906147075)
  ·
    refine ⟨216831015164380124859220613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144554010109586749906147075 216831015164380124859220613)
    ·
      refine ⟨40655815343321273411103865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 216831015164380124859220613 40655815343321273411103865)
      ·
        refine ⟨30491861507490955058327899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40655815343321273411103865 30491861507490955058327899)
        ·
          refine ⟨45737792261236432587491849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30491861507490955058327899 45737792261236432587491849)
          ·
            refine ⟨34303344195927324440618887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45737792261236432587491849 34303344195927324440618887)
            ·
              refine ⟨51455016293890986660928331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34303344195927324440618887 51455016293890986660928331)
              ·
                refine ⟨77182524440836479991392497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51455016293890986660928331 77182524440836479991392497)
                ·
                  refine ⟨57886893330627359993544373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77182524440836479991392497 57886893330627359993544373)
                  ·
                    refine ⟨5426896249746314999394785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 57886893330627359993544373 5426896249746314999394785)
                    ·
                      refine ⟨4070172187309736249546089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5426896249746314999394785 4070172187309736249546089)
                      ·
                        rfl

theorem cell23_7926632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 1, 2, 5, 2].length) (baseStart_7926632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7926632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7926632 prefixEnd_7926632 := by exact prefixLift 7926632
  have htrace : WordTrace (prefixWord ++ tailWord_7926632) baseStart_7926632 baseEnd_7926632 := by
    simpa [prefixWord, tailWord_7926632, baseEnd_7926632] using wordTrace_append hprefix tailTrace_7926632
  have hstable : (prefixWord ++ tailWord_7926632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7926632).length < 2 ^ (prefixWord ++ tailWord_7926632).sum := by decide
  have hdescent : baseEnd_7926632 < baseStart_7926632 := by decide
  rcases family_descends (prefixWord ++ tailWord_7926632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7926655 : List Nat := [1, 1, 2, 2, 1, 1, 5, 1, 5, 4]
def baseStart_7926655 : Nat := 118140960795 + 7926655 * 2 ^ 59
def prefixEnd_7926655 : Nat := 4983230072969 + 3 ^ 40 * 7926655 * 2
def baseEnd_7926655 : Nat := 1356727999121596553186161

theorem tailTrace_7926655 : CollatzResearch.WordTrace tailWord_7926655 prefixEnd_7926655 1356727999121596553186161 := by
  unfold tailWord_7926655
  simp only [CollatzResearch.WordTrace]
  refine ⟨289108859098090174740381419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192739239398726783160254279 289108859098090174740381419)
  ·
    refine ⟨433663288647135262110572129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289108859098090174740381419 433663288647135262110572129)
    ·
      refine ⟨325247466485351446582929097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 433663288647135262110572129 325247466485351446582929097)
      ·
        refine ⟨243935599864013584937196823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 325247466485351446582929097 243935599864013584937196823)
        ·
          refine ⟨365903399796020377405795235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 243935599864013584937196823 365903399796020377405795235)
          ·
            refine ⟨548855099694030566108692853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 365903399796020377405795235 548855099694030566108692853)
            ·
              refine ⟨51455165596315365572689955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 548855099694030566108692853 51455165596315365572689955)
              ·
                refine ⟨77182748394473048359034933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51455165596315365572689955 77182748394473048359034933)
                ·
                  refine ⟨7235882661981848283659525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 77182748394473048359034933 7235882661981848283659525)
                  ·
                    refine ⟨1356727999121596553186161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7235882661981848283659525 1356727999121596553186161)
                    ·
                      rfl

theorem cell23_7926655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 1, 5, 4].length) (baseStart_7926655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7926655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7926655 prefixEnd_7926655 := by exact prefixLift 7926655
  have htrace : WordTrace (prefixWord ++ tailWord_7926655) baseStart_7926655 baseEnd_7926655 := by
    simpa [prefixWord, tailWord_7926655, baseEnd_7926655] using wordTrace_append hprefix tailTrace_7926655
  have hstable : (prefixWord ++ tailWord_7926655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7926655).length < 2 ^ (prefixWord ++ tailWord_7926655).sum := by decide
  have hdescent : baseEnd_7926655 < baseStart_7926655 := by decide
  rcases family_descends (prefixWord ++ tailWord_7926655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7926685 : List Nat := [1, 4, 2, 1, 2, 1, 3, 1, 8]
def baseStart_7926685 : Nat := 118140960795 + 7926685 * 2 ^ 59
def prefixEnd_7926685 : Nat := 4983230072969 + 3 ^ 40 * 7926685 * 2
def baseEnd_7926685 : Nat := 452244377976047171353705

theorem tailTrace_7926685 : CollatzResearch.WordTrace tailWord_7926685 prefixEnd_7926685 452244377976047171353705 := by
  unfold tailWord_7926685
  simp only [CollatzResearch.WordTrace]
  refine ⟨289109953287981489863973509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192739968858654326575982339 289109953287981489863973509)
  ·
    refine ⟨54208116241496529349495033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 289109953287981489863973509 54208116241496529349495033)
    ·
      refine ⟨40656087181122397012121275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54208116241496529349495033 40656087181122397012121275)
      ·
        refine ⟨60984130771683595518181913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40656087181122397012121275 60984130771683595518181913)
        ·
          refine ⟨45738098078762696638636435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60984130771683595518181913 45738098078762696638636435)
          ·
            refine ⟨68607147118144044957954653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45738098078762696638636435 68607147118144044957954653)
            ·
              refine ⟨25727680169304016859232995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68607147118144044957954653 25727680169304016859232995)
              ·
                refine ⟨38591520253956025288849493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25727680169304016859232995 38591520253956025288849493)
                ·
                  refine ⟨452244377976047171353705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 38591520253956025288849493 452244377976047171353705)
                  ·
                    rfl

theorem cell23_7926685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 3, 1, 8].length) (baseStart_7926685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7926685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7926685 prefixEnd_7926685 := by exact prefixLift 7926685
  have htrace : WordTrace (prefixWord ++ tailWord_7926685) baseStart_7926685 baseEnd_7926685 := by
    simpa [prefixWord, tailWord_7926685, baseEnd_7926685] using wordTrace_append hprefix tailTrace_7926685
  have hstable : (prefixWord ++ tailWord_7926685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7926685).length < 2 ^ (prefixWord ++ tailWord_7926685).sum := by decide
  have hdescent : baseEnd_7926685 < baseStart_7926685 := by decide
  rcases family_descends (prefixWord ++ tailWord_7926685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7926689 : List Nat := [1, 2, 3, 4, 1, 2, 2, 1, 3, 4]
def baseStart_7926689 : Nat := 118140960795 + 7926689 * 2 ^ 59
def prefixEnd_7926689 : Nat := 4983230072969 + 3 ^ 40 * 7926689 * 2
def baseEnd_7926689 : Nat := 1356733818569014175511109

theorem tailTrace_7926689 : CollatzResearch.WordTrace tailWord_7926689 prefixEnd_7926689 1356733818569014175511109 := by
  unfold tailWord_7926689
  simp only [CollatzResearch.WordTrace]
  refine ⟨289110099179966998547119121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192740066119977999031412747 289110099179966998547119121)
  ·
    refine ⟨216832574384975248910339341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 289110099179966998547119121 216832574384975248910339341)
    ·
      refine ⟨81312215394365718341377253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 216832574384975248910339341 81312215394365718341377253)
      ·
        refine ⟨15246040386443572189008235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81312215394365718341377253 15246040386443572189008235)
        ·
          refine ⟨22869060579665358283512353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15246040386443572189008235 22869060579665358283512353)
          ·
            refine ⟨17151795434749018712634265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22869060579665358283512353 17151795434749018712634265)
            ·
              refine ⟨12863846576061764034475699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17151795434749018712634265 12863846576061764034475699)
              ·
                refine ⟨19295769864092646051713549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12863846576061764034475699 19295769864092646051713549)
                ·
                  refine ⟨7235913699034742269392581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19295769864092646051713549 7235913699034742269392581)
                  ·
                    refine ⟨1356733818569014175511109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7235913699034742269392581 1356733818569014175511109)
                    ·
                      rfl

theorem cell23_7926689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 2, 1, 3, 4].length) (baseStart_7926689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7926689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7926689 prefixEnd_7926689 := by exact prefixLift 7926689
  have htrace : WordTrace (prefixWord ++ tailWord_7926689) baseStart_7926689 baseEnd_7926689 := by
    simpa [prefixWord, tailWord_7926689, baseEnd_7926689] using wordTrace_append hprefix tailTrace_7926689
  have hstable : (prefixWord ++ tailWord_7926689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7926689).length < 2 ^ (prefixWord ++ tailWord_7926689).sum := by decide
  have hdescent : baseEnd_7926689 < baseStart_7926689 := by decide
  rcases family_descends (prefixWord ++ tailWord_7926689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7926732 : List Nat := [2, 2, 1, 4, 1, 1, 1, 5, 1, 5]
def baseStart_7926732 : Nat := 118140960795 + 7926732 * 2 ^ 59
def prefixEnd_7926732 : Nat := 4983230072969 + 3 ^ 40 * 7926732 * 2
def baseEnd_7926732 : Nat := 1356741178458395286098543

theorem tailTrace_7926732 : CollatzResearch.WordTrace tailWord_7926732 prefixEnd_7926732 1356741178458395286098543 := by
  unfold tailWord_7926732
  simp only [CollatzResearch.WordTrace]
  refine ⟨144555833759405608445467225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192741111679207477927289633 144555833759405608445467225)
  ·
    refine ⟨108416875319554206334100419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144555833759405608445467225 108416875319554206334100419)
    ·
      refine ⟨162625312979331309501150629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108416875319554206334100419 162625312979331309501150629)
      ·
        refine ⟨30492246183624620531465743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 162625312979331309501150629 30492246183624620531465743)
        ·
          refine ⟨45738369275436930797198615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30492246183624620531465743 45738369275436930797198615)
          ·
            refine ⟨68607553913155396195797923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45738369275436930797198615 68607553913155396195797923)
            ·
              refine ⟨102911330869733094293696885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68607553913155396195797923 102911330869733094293696885)
              ·
                refine ⟨9647937269037477590034083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 102911330869733094293696885 9647937269037477590034083)
                ·
                  refine ⟨14471905903556216385051125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9647937269037477590034083 14471905903556216385051125)
                  ·
                    refine ⟨1356741178458395286098543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14471905903556216385051125 1356741178458395286098543)
                    ·
                      rfl

theorem cell23_7926732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 5, 1, 5].length) (baseStart_7926732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7926732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7926732 prefixEnd_7926732 := by exact prefixLift 7926732
  have htrace : WordTrace (prefixWord ++ tailWord_7926732) baseStart_7926732 baseEnd_7926732 := by
    simpa [prefixWord, tailWord_7926732, baseEnd_7926732] using wordTrace_append hprefix tailTrace_7926732
  have hstable : (prefixWord ++ tailWord_7926732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7926732).length < 2 ^ (prefixWord ++ tailWord_7926732).sum := by decide
  have hdescent : baseEnd_7926732 < baseStart_7926732 := by decide
  rcases family_descends (prefixWord ++ tailWord_7926732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7926746 : List Nat := [3, 1, 1, 2, 4, 3, 1, 1, 3, 1, 3]
def baseStart_7926746 : Nat := 118140960795 + 7926746 * 2 ^ 59
def prefixEnd_7926746 : Nat := 4983230072969 + 3 ^ 40 * 7926746 * 2
def baseEnd_7926746 : Nat := 4070230724104348803520565

theorem tailTrace_7926746 : CollatzResearch.WordTrace tailWord_7926746 prefixEnd_7926746 4070230724104348803520565 := by
  unfold tailWord_7926746
  simp only [CollatzResearch.WordTrace]
  refine ⟨72278044535190124320486023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192741452093840331521296061 72278044535190124320486023)
  ·
    refine ⟨108417066802785186480729035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72278044535190124320486023 108417066802785186480729035)
    ·
      refine ⟨162625600204177779721093553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108417066802785186480729035 162625600204177779721093553)
      ·
        refine ⟨121969200153133334790820165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162625600204177779721093553 121969200153133334790820165)
        ·
          refine ⟨22869225028712500273278781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 121969200153133334790820165 22869225028712500273278781)
          ·
            refine ⟨8575959385767187602479543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22869225028712500273278781 8575959385767187602479543)
            ·
              refine ⟨12863939078650781403719315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8575959385767187602479543 12863939078650781403719315)
              ·
                refine ⟨19295908617976172105578973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12863939078650781403719315 19295908617976172105578973)
                ·
                  refine ⟨7235965731741064539592115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19295908617976172105578973 7235965731741064539592115)
                  ·
                    refine ⟨10853948597611596809388173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7235965731741064539592115 10853948597611596809388173)
                    ·
                      refine ⟨4070230724104348803520565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10853948597611596809388173 4070230724104348803520565)
                      ·
                        rfl

theorem cell23_7926746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 3, 1, 3].length) (baseStart_7926746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7926746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7926746 prefixEnd_7926746 := by exact prefixLift 7926746
  have htrace : WordTrace (prefixWord ++ tailWord_7926746) baseStart_7926746 baseEnd_7926746 := by
    simpa [prefixWord, tailWord_7926746, baseEnd_7926746] using wordTrace_append hprefix tailTrace_7926746
  have hstable : (prefixWord ++ tailWord_7926746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7926746).length < 2 ^ (prefixWord ++ tailWord_7926746).sum := by decide
  have hdescent : baseEnd_7926746 < baseStart_7926746 := by decide
  rcases family_descends (prefixWord ++ tailWord_7926746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7926766 : List Nat := [4, 1, 2, 1, 4, 2, 1, 2, 1, 5]
def baseStart_7926766 : Nat := 118140960795 + 7926766 * 2 ^ 59
def prefixEnd_7926766 : Nat := 4983230072969 + 3 ^ 40 * 7926766 * 2
def baseEnd_7926766 : Nat := 1356746997905812908423491

theorem tailTrace_7926766 : CollatzResearch.WordTrace tailWord_7926766 prefixEnd_7926766 1356746997905812908423491 := by
  unfold tailWord_7926766
  simp only [CollatzResearch.WordTrace]
  refine ⟨36139113450086005087209019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 192741938400458693798448101 36139113450086005087209019)
  ·
    refine ⟨54208670175129007630813529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36139113450086005087209019 54208670175129007630813529)
    ·
      refine ⟨40656502631346755723110147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54208670175129007630813529 40656502631346755723110147)
      ·
        refine ⟨60984753947020133584665221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40656502631346755723110147 60984753947020133584665221)
        ·
          refine ⟨11434641365066275047124729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60984753947020133584665221 11434641365066275047124729)
          ·
            refine ⟨8575981023799706285343547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11434641365066275047124729 8575981023799706285343547)
            ·
              refine ⟨12863971535699559428015321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8575981023799706285343547 12863971535699559428015321)
              ·
                refine ⟨9647978651774669571011491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12863971535699559428015321 9647978651774669571011491)
                ·
                  refine ⟨14471967977662004356517237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9647978651774669571011491 14471967977662004356517237)
                  ·
                    refine ⟨1356746997905812908423491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14471967977662004356517237 1356746997905812908423491)
                    ·
                      rfl

theorem cell23_7926766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 2, 1, 2, 1, 5].length) (baseStart_7926766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7926766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7926766 prefixEnd_7926766 := by exact prefixLift 7926766
  have htrace : WordTrace (prefixWord ++ tailWord_7926766) baseStart_7926766 baseEnd_7926766 := by
    simpa [prefixWord, tailWord_7926766, baseEnd_7926766] using wordTrace_append hprefix tailTrace_7926766
  have hstable : (prefixWord ++ tailWord_7926766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7926766).length < 2 ^ (prefixWord ++ tailWord_7926766).sum := by decide
  have hdescent : baseEnd_7926766 < baseStart_7926766 := by decide
  rcases family_descends (prefixWord ++ tailWord_7926766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7926769 : List Nat := [1, 2, 2, 2, 4, 1, 3, 2, 1, 1, 4]
def baseStart_7926769 : Nat := 118140960795 + 7926769 * 2 ^ 59
def prefixEnd_7926769 : Nat := 4983230072969 + 3 ^ 40 * 7926769 * 2
def baseEnd_7926769 : Nat := 4070242534159402213532959

theorem tailTrace_7926769 : CollatzResearch.WordTrace tailWord_7926769 prefixEnd_7926769 4070242534159402213532959 := by
  unfold tailWord_7926769
  simp only [CollatzResearch.WordTrace]
  refine ⟨289113017019677172210031361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192742011346451448140020907 289113017019677172210031361)
  ·
    refine ⟨216834762764757879157523521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 289113017019677172210031361 216834762764757879157523521)
    ·
      refine ⟨162626072073568409368142641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216834762764757879157523521 162626072073568409368142641)
      ·
        refine ⟨121969554055176307026106981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162626072073568409368142641 121969554055176307026106981)
        ·
          refine ⟨22869291385345557567395059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 121969554055176307026106981 22869291385345557567395059)
          ·
            refine ⟨34303937078018336351092589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22869291385345557567395059 34303937078018336351092589)
            ·
              refine ⟨12863976404256876131659721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34303937078018336351092589 12863976404256876131659721)
              ·
                refine ⟨9647982303192657098744791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12863976404256876131659721 9647982303192657098744791)
                ·
                  refine ⟨14471973454788985648117187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9647982303192657098744791 14471973454788985648117187)
                  ·
                    refine ⟨21707960182183478472175781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14471973454788985648117187 21707960182183478472175781)
                    ·
                      refine ⟨4070242534159402213532959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21707960182183478472175781 4070242534159402213532959)
                      ·
                        rfl

theorem cell23_7926769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 3, 2, 1, 1, 4].length) (baseStart_7926769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7926769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7926769 prefixEnd_7926769 := by exact prefixLift 7926769
  have htrace : WordTrace (prefixWord ++ tailWord_7926769) baseStart_7926769 baseEnd_7926769 := by
    simpa [prefixWord, tailWord_7926769, baseEnd_7926769] using wordTrace_append hprefix tailTrace_7926769
  have hstable : (prefixWord ++ tailWord_7926769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7926769).length < 2 ^ (prefixWord ++ tailWord_7926769).sum := by decide
  have hdescent : baseEnd_7926769 < baseStart_7926769 := by decide
  rcases family_descends (prefixWord ++ tailWord_7926769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7926816 : List Nat := [2, 1, 1, 7, 1, 1, 2, 1, 1, 2, 4]
def baseStart_7926816 : Nat := 118140960795 + 7926816 * 2 ^ 59
def prefixEnd_7926816 : Nat := 4983230072969 + 3 ^ 40 * 7926816 * 2
def baseEnd_7926816 : Nat := 4070266667750163529645243

theorem tailTrace_7926816 : CollatzResearch.WordTrace tailWord_7926816 prefixEnd_7926816 4070266667750163529645243 := by
  unfold tailWord_7926816
  simp only [CollatzResearch.WordTrace]
  refine ⟨144557365625253449618496151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192743154167004599491328201 144557365625253449618496151)
  ·
    refine ⟨216836048437880174427744227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144557365625253449618496151 216836048437880174427744227)
    ·
      refine ⟨325254072656820261641616341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216836048437880174427744227 325254072656820261641616341)
      ·
        refine ⟨7623142327894224882225383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 325254072656820261641616341 7623142327894224882225383)
        ·
          refine ⟨11434713491841337323338075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7623142327894224882225383 11434713491841337323338075)
          ·
            refine ⟨17152070237762005985007113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11434713491841337323338075 17152070237762005985007113)
            ·
              refine ⟨12864052678321504488755335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17152070237762005985007113 12864052678321504488755335)
              ·
                refine ⟨19296079017482256733133003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12864052678321504488755335 19296079017482256733133003)
                ·
                  refine ⟨28944118526223385099699505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19296079017482256733133003 28944118526223385099699505)
                  ·
                    refine ⟨21708088894667538824774629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28944118526223385099699505 21708088894667538824774629)
                    ·
                      refine ⟨4070266667750163529645243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21708088894667538824774629 4070266667750163529645243)
                      ·
                        rfl

theorem cell23_7926816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 2, 1, 1, 2, 4].length) (baseStart_7926816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7926816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7926816 prefixEnd_7926816 := by exact prefixLift 7926816
  have htrace : WordTrace (prefixWord ++ tailWord_7926816) baseStart_7926816 baseEnd_7926816 := by
    simpa [prefixWord, tailWord_7926816, baseEnd_7926816] using wordTrace_append hprefix tailTrace_7926816
  have hstable : (prefixWord ++ tailWord_7926816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7926816).length < 2 ^ (prefixWord ++ tailWord_7926816).sum := by decide
  have hdescent : baseEnd_7926816 < baseStart_7926816 := by decide
  rcases family_descends (prefixWord ++ tailWord_7926816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7926819 : List Nat := [1, 1, 1, 4, 3, 3, 2, 1, 1, 3, 3]
def baseStart_7926819 : Nat := 118140960795 + 7926819 * 2 ^ 59
def prefixEnd_7926819 : Nat := 4983230072969 + 3 ^ 40 * 7926819 * 2
def baseEnd_7926819 : Nat := 4070268208192127017907729

theorem tailTrace_7926819 : CollatzResearch.WordTrace tailWord_7926819 prefixEnd_7926819 4070268208192127017907729 := by
  unfold tailWord_7926819
  simp only [CollatzResearch.WordTrace]
  refine ⟨289114840669496030749351511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192743227112997353832901007 289114840669496030749351511)
  ·
    refine ⟨433672261004244046124027267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289114840669496030749351511 433672261004244046124027267)
    ·
      refine ⟨650508391506366069186040901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 433672261004244046124027267 650508391506366069186040901)
      ·
        refine ⟨121970323407443637972382669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 650508391506366069186040901 121970323407443637972382669)
        ·
          refine ⟨45738871277791364239643501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 121970323407443637972382669 45738871277791364239643501)
          ·
            refine ⟨17152076729171761589866313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45738871277791364239643501 17152076729171761589866313)
            ·
              refine ⟨12864057546878821192399735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17152076729171761589866313 12864057546878821192399735)
              ·
                refine ⟨19296086320318231788599603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12864057546878821192399735 19296086320318231788599603)
                ·
                  refine ⟨28944129480477347682899405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19296086320318231788599603 28944129480477347682899405)
                  ·
                    refine ⟨10854048555179005381087277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28944129480477347682899405 10854048555179005381087277)
                    ·
                      refine ⟨4070268208192127017907729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10854048555179005381087277 4070268208192127017907729)
                      ·
                        rfl

theorem cell23_7926819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 2, 1, 1, 3, 3].length) (baseStart_7926819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7926819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7926819 prefixEnd_7926819 := by exact prefixLift 7926819
  have htrace : WordTrace (prefixWord ++ tailWord_7926819) baseStart_7926819 baseEnd_7926819 := by
    simpa [prefixWord, tailWord_7926819, baseEnd_7926819] using wordTrace_append hprefix tailTrace_7926819
  have hstable : (prefixWord ++ tailWord_7926819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7926819).length < 2 ^ (prefixWord ++ tailWord_7926819).sum := by decide
  have hdescent : baseEnd_7926819 < baseStart_7926819 := by decide
  rcases family_descends (prefixWord ++ tailWord_7926819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7926835 : List Nat := [1, 1, 1, 2, 4, 1, 1, 1, 3, 8]
def baseStart_7926835 : Nat := 118140960795 + 7926835 * 2 ^ 59
def prefixEnd_7926835 : Nat := 4983230072969 + 3 ^ 40 * 7926835 * 2
def baseEnd_7926835 : Nat := 1356758807960866318435885

theorem tailTrace_7926835 : CollatzResearch.WordTrace tailWord_7926835 prefixEnd_7926835 1356758807960866318435885 := by
  unfold tailWord_7926835
  simp only [CollatzResearch.WordTrace]
  refine ⟨289115424237438065481933959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192743616158292043654622639 289115424237438065481933959)
  ·
    refine ⟨433673136356157098222900939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289115424237438065481933959 433673136356157098222900939)
    ·
      refine ⟨650509704534235647334351409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 433673136356157098222900939 650509704534235647334351409)
      ·
        refine ⟨487882278400676735500763557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 650509704534235647334351409 487882278400676735500763557)
        ·
          refine ⟨91477927200126887906393167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 487882278400676735500763557 91477927200126887906393167)
          ·
            refine ⟨137216890800190331859589751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91477927200126887906393167 137216890800190331859589751)
            ·
              refine ⟨205825336200285497789384627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137216890800190331859589751 205825336200285497789384627)
              ·
                refine ⟨308738004300428246684076941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 205825336200285497789384627 308738004300428246684076941)
                ·
                  refine ⟨115776751612660592506528853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 308738004300428246684076941 115776751612660592506528853)
                  ·
                    refine ⟨1356758807960866318435885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 115776751612660592506528853 1356758807960866318435885)
                    ·
                      rfl

theorem cell23_7926835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 1, 3, 8].length) (baseStart_7926835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7926835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7926835 prefixEnd_7926835 := by exact prefixLift 7926835
  have htrace : WordTrace (prefixWord ++ tailWord_7926835) baseStart_7926835 baseEnd_7926835 := by
    simpa [prefixWord, tailWord_7926835, baseEnd_7926835] using wordTrace_append hprefix tailTrace_7926835
  have hstable : (prefixWord ++ tailWord_7926835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7926835).length < 2 ^ (prefixWord ++ tailWord_7926835).sum := by decide
  have hdescent : baseEnd_7926835 < baseStart_7926835 := by decide
  rcases family_descends (prefixWord ++ tailWord_7926835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7926836 : List Nat := [2, 5, 1, 2, 1, 1, 2, 2, 1, 3, 3]
def baseStart_7926836 : Nat := 118140960795 + 7926836 * 2 ^ 59
def prefixEnd_7926836 : Nat := 4983230072969 + 3 ^ 40 * 7926836 * 2
def baseEnd_7926836 : Nat := 4070276937363253451395151

theorem tailTrace_7926836 : CollatzResearch.WordTrace tailWord_7926836 prefixEnd_7926836 4070276937363253451395151 := by
  unfold tailWord_7926836
  simp only [CollatzResearch.WordTrace]
  refine ⟨144557730355217221326360181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192743640473622961768480241 144557730355217221326360181)
  ·
    refine ⟨13552287220801614499346267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 144557730355217221326360181 13552287220801614499346267)
    ·
      refine ⟨20328430831202421749019401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13552287220801614499346267 20328430831202421749019401)
      ·
        refine ⟨15246323123401816311764551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20328430831202421749019401 15246323123401816311764551)
        ·
          refine ⟨22869484685102724467646827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15246323123401816311764551 22869484685102724467646827)
          ·
            refine ⟨34304227027654086701470241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22869484685102724467646827 34304227027654086701470241)
            ·
              refine ⟨25728170270740565026102681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34304227027654086701470241 25728170270740565026102681)
              ·
                refine ⟨19296127703055423769577011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25728170270740565026102681 19296127703055423769577011)
                ·
                  refine ⟨28944191554583135654365517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19296127703055423769577011 28944191554583135654365517)
                  ·
                    refine ⟨10854071832968675870387069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28944191554583135654365517 10854071832968675870387069)
                    ·
                      refine ⟨4070276937363253451395151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10854071832968675870387069 4070276937363253451395151)
                      ·
                        rfl

theorem cell23_7926836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 2, 2, 1, 3, 3].length) (baseStart_7926836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7926836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7926836 prefixEnd_7926836 := by exact prefixLift 7926836
  have htrace : WordTrace (prefixWord ++ tailWord_7926836) baseStart_7926836 baseEnd_7926836 := by
    simpa [prefixWord, tailWord_7926836, baseEnd_7926836] using wordTrace_append hprefix tailTrace_7926836
  have hstable : (prefixWord ++ tailWord_7926836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7926836).length < 2 ^ (prefixWord ++ tailWord_7926836).sum := by decide
  have hdescent : baseEnd_7926836 < baseStart_7926836 := by decide
  rcases family_descends (prefixWord ++ tailWord_7926836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7926870 : List Nat := [5, 2, 2, 1, 2, 2, 1, 1, 1, 3, 3]
def baseStart_7926870 : Nat := 118140960795 + 7926870 * 2 ^ 59
def prefixEnd_7926870 : Nat := 4983230072969 + 3 ^ 40 * 7926870 * 2
def baseEnd_7926870 : Nat := 4070294395705506318369995

theorem tailTrace_7926870 : CollatzResearch.WordTrace tailWord_7926870 prefixEnd_7926870 4070294395705506318369995 := by
  unfold tailWord_7926870
  simp only [CollatzResearch.WordTrace]
  refine ⟨18069793799519454153716129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 192744467194874177639638709 18069793799519454153716129)
  ·
    refine ⟨13552345349639590615287097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18069793799519454153716129 13552345349639590615287097)
    ·
      refine ⟨10164259012229692961465323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13552345349639590615287097 10164259012229692961465323)
      ·
        refine ⟨15246388518344539442197985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10164259012229692961465323 15246388518344539442197985)
        ·
          refine ⟨11434791388758404581648489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15246388518344539442197985 11434791388758404581648489)
          ·
            refine ⟨8576093541568803436236367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11434791388758404581648489 8576093541568803436236367)
            ·
              refine ⟨12864140312353205154354551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8576093541568803436236367 12864140312353205154354551)
              ·
                refine ⟨19296210468529807731531827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12864140312353205154354551 19296210468529807731531827)
                ·
                  refine ⟨28944315702794711597297741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19296210468529807731531827 28944315702794711597297741)
                  ·
                    refine ⟨10854118388548016848986653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28944315702794711597297741 10854118388548016848986653)
                    ·
                      refine ⟨4070294395705506318369995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10854118388548016848986653 4070294395705506318369995)
                      ·
                        rfl

theorem cell23_7926870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 2, 1, 1, 1, 3, 3].length) (baseStart_7926870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7926870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7926870 prefixEnd_7926870 := by exact prefixLift 7926870
  have htrace : WordTrace (prefixWord ++ tailWord_7926870) baseStart_7926870 baseEnd_7926870 := by
    simpa [prefixWord, tailWord_7926870, baseEnd_7926870] using wordTrace_append hprefix tailTrace_7926870
  have hstable : (prefixWord ++ tailWord_7926870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7926870).length < 2 ^ (prefixWord ++ tailWord_7926870).sum := by decide
  have hdescent : baseEnd_7926870 < baseStart_7926870 := by decide
  rcases family_descends (prefixWord ++ tailWord_7926870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7926872 : List Nat := [2, 1, 2, 2, 1, 3, 1, 3, 2, 2, 4]
def baseStart_7926872 : Nat := 118140960795 + 7926872 * 2 ^ 59
def prefixEnd_7926872 : Nat := 4983230072969 + 3 ^ 40 * 7926872 * 2
def baseEnd_7926872 : Nat := 4070295422666815310544985

theorem tailTrace_7926872 : CollatzResearch.WordTrace tailWord_7926872 prefixEnd_7926872 4070295422666815310544985 := by
  unfold tailWord_7926872
  simp only [CollatzResearch.WordTrace]
  refine ⟨144558386869152010400515435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192744515825536013867353913 144558386869152010400515435)
  ·
    refine ⟨216837580303728015600773153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144558386869152010400515435 216837580303728015600773153)
    ·
      refine ⟨162628185227796011700579865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216837580303728015600773153 162628185227796011700579865)
      ·
        refine ⟨121971138920847008775434899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162628185227796011700579865 121971138920847008775434899)
        ·
          refine ⟨182956708381270513163152349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121971138920847008775434899 182956708381270513163152349)
          ·
            refine ⟨68608765642976442436182131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 182956708381270513163152349 68608765642976442436182131)
            ·
              refine ⟨102913148464464663654273197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68608765642976442436182131 102913148464464663654273197)
              ·
                refine ⟨38592430674174248870352449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 102913148464464663654273197 38592430674174248870352449)
                ·
                  refine ⟨28944323005630686652764337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38592430674174248870352449 28944323005630686652764337)
                  ·
                    refine ⟨21708242254223014989573253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28944323005630686652764337 21708242254223014989573253)
                    ·
                      refine ⟨4070295422666815310544985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21708242254223014989573253 4070295422666815310544985)
                      ·
                        rfl

theorem cell23_7926872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 3, 2, 2, 4].length) (baseStart_7926872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7926872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7926872 prefixEnd_7926872 := by exact prefixLift 7926872
  have htrace : WordTrace (prefixWord ++ tailWord_7926872) baseStart_7926872 baseEnd_7926872 := by
    simpa [prefixWord, tailWord_7926872, baseEnd_7926872] using wordTrace_append hprefix tailTrace_7926872
  have hstable : (prefixWord ++ tailWord_7926872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7926872).length < 2 ^ (prefixWord ++ tailWord_7926872).sum := by decide
  have hdescent : baseEnd_7926872 < baseStart_7926872 := by decide
  rcases family_descends (prefixWord ++ tailWord_7926872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7926912 : List Nat := [2, 1, 1, 2, 1, 3, 3, 1, 4, 5]
def baseStart_7926912 : Nat := 118140960795 + 7926912 * 2 ^ 59
def prefixEnd_7926912 : Nat := 4983230072969 + 3 ^ 40 * 7926912 * 2
def baseEnd_7926912 : Nat := 1356771987297665051348267

theorem tailTrace_7926912 : CollatzResearch.WordTrace tailWord_7926912 prefixEnd_7926912 1356771987297665051348267 := by
  unfold tailWord_7926912
  simp only [CollatzResearch.WordTrace]
  refine ⟨144559116329079553816243495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192745488438772738421657993 144559116329079553816243495)
  ·
    refine ⟨216838674493619330724365243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144559116329079553816243495 216838674493619330724365243)
    ·
      refine ⟨325258011740428996086547865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216838674493619330724365243 325258011740428996086547865)
      ·
        refine ⟨243943508805321747064910899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 325258011740428996086547865 243943508805321747064910899)
        ·
          refine ⟨365915263207982620597366349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 243943508805321747064910899 365915263207982620597366349)
          ·
            refine ⟨137218223702993482724012381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 365915263207982620597366349 137218223702993482724012381)
            ·
              refine ⟨51456833888622556021504643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 137218223702993482724012381 51456833888622556021504643)
              ·
                refine ⟨77185250832933834032256965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51456833888622556021504643 77185250832933834032256965)
                ·
                  refine ⟨14472234531175093881048181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 77185250832933834032256965 14472234531175093881048181)
                  ·
                    refine ⟨1356771987297665051348267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14472234531175093881048181 1356771987297665051348267)
                    ·
                      rfl

theorem cell23_7926912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 1, 4, 5].length) (baseStart_7926912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7926912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7926912 prefixEnd_7926912 := by exact prefixLift 7926912
  have htrace : WordTrace (prefixWord ++ tailWord_7926912) baseStart_7926912 baseEnd_7926912 := by
    simpa [prefixWord, tailWord_7926912, baseEnd_7926912] using wordTrace_append hprefix tailTrace_7926912
  have hstable : (prefixWord ++ tailWord_7926912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7926912).length < 2 ^ (prefixWord ++ tailWord_7926912).sum := by decide
  have hdescent : baseEnd_7926912 < baseStart_7926912 := by decide
  rcases family_descends (prefixWord ++ tailWord_7926912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7926919 : List Nat := [1, 1, 4, 2, 1, 1, 1, 3, 2, 5, 2]
def baseStart_7926919 : Nat := 118140960795 + 7926919 * 2 ^ 59
def prefixEnd_7926919 : Nat := 4983230072969 + 3 ^ 40 * 7926919 * 2
def baseEnd_7926919 : Nat := 4070319556257576626657269

theorem tailTrace_7926919 : CollatzResearch.WordTrace tailWord_7926919 prefixEnd_7926919 4070319556257576626657269 := by
  unfold tailWord_7926919
  simp only [CollatzResearch.WordTrace]
  refine ⟨289118487969133747827991811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192745658646089165218661207 289118487969133747827991811)
  ·
    refine ⟨433677731953700621741987717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289118487969133747827991811 433677731953700621741987717)
    ·
      refine ⟨81314574741318866576622697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 433677731953700621741987717 81314574741318866576622697)
      ·
        refine ⟨60985931055989149932467023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81314574741318866576622697 60985931055989149932467023)
        ·
          refine ⟨91478896583983724898700535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60985931055989149932467023 91478896583983724898700535)
          ·
            refine ⟨137218344875975587348050803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91478896583983724898700535 137218344875975587348050803)
            ·
              refine ⟨205827517313963381022076205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137218344875975587348050803 205827517313963381022076205)
              ·
                refine ⟨77185318992736267883278577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 205827517313963381022076205 77185318992736267883278577)
                ·
                  refine ⟨57888989244552200912458933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77185318992736267883278577 57888989244552200912458933)
                  ·
                    refine ⟨5427092741676768835543025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 57888989244552200912458933 5427092741676768835543025)
                    ·
                      refine ⟨4070319556257576626657269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5427092741676768835543025 4070319556257576626657269)
                      ·
                        rfl

theorem cell23_7926919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 3, 2, 5, 2].length) (baseStart_7926919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7926919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7926919 prefixEnd_7926919 := by exact prefixLift 7926919
  have htrace : WordTrace (prefixWord ++ tailWord_7926919) baseStart_7926919 baseEnd_7926919 := by
    simpa [prefixWord, tailWord_7926919, baseEnd_7926919] using wordTrace_append hprefix tailTrace_7926919
  have hstable : (prefixWord ++ tailWord_7926919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7926919).length < 2 ^ (prefixWord ++ tailWord_7926919).sum := by decide
  have hdescent : baseEnd_7926919 < baseStart_7926919 := by decide
  rcases family_descends (prefixWord ++ tailWord_7926919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7926949 : List Nat := [1, 3, 1, 2, 1, 4, 1, 3, 2, 1, 4]
def baseStart_7926949 : Nat := 118140960795 + 7926949 * 2 ^ 59
def prefixEnd_7926949 : Nat := 4983230072969 + 3 ^ 40 * 7926949 * 2
def baseEnd_7926949 : Nat := 4070334960677211509282131

theorem tailTrace_7926949 : CollatzResearch.WordTrace tailWord_7926949 prefixEnd_7926949 4070334960677211509282131 := by
  unfold tailWord_7926949
  simp only [CollatzResearch.WordTrace]
  refine ⟨289119582159025062951583901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192746388106016708634389267 289119582159025062951583901)
  ·
    refine ⟨108419843309634398606843963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 289119582159025062951583901 108419843309634398606843963)
    ·
      refine ⟨162629764964451597910265945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108419843309634398606843963 162629764964451597910265945)
      ·
        refine ⟨121972323723338698432699459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162629764964451597910265945 121972323723338698432699459)
        ·
          refine ⟨182958485585008047649049189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121972323723338698432699459 182958485585008047649049189)
          ·
            refine ⟨34304716047189008934196723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 182958485585008047649049189 34304716047189008934196723)
            ·
              refine ⟨51457074070783513401295085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34304716047189008934196723 51457074070783513401295085)
              ·
                refine ⟨19296402776543817525485657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51457074070783513401295085 19296402776543817525485657)
                ·
                  refine ⟨14472302082407863144114243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19296402776543817525485657 14472302082407863144114243)
                  ·
                    refine ⟨21708453123611794716171365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14472302082407863144114243 21708453123611794716171365)
                    ·
                      refine ⟨4070334960677211509282131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21708453123611794716171365 4070334960677211509282131)
                      ·
                        rfl

theorem cell23_7926949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 3, 2, 1, 4].length) (baseStart_7926949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7926949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7926949 prefixEnd_7926949 := by exact prefixLift 7926949
  have htrace : WordTrace (prefixWord ++ tailWord_7926949) baseStart_7926949 baseEnd_7926949 := by
    simpa [prefixWord, tailWord_7926949, baseEnd_7926949] using wordTrace_append hprefix tailTrace_7926949
  have hstable : (prefixWord ++ tailWord_7926949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7926949).length < 2 ^ (prefixWord ++ tailWord_7926949).sum := by decide
  have hdescent : baseEnd_7926949 < baseStart_7926949 := by decide
  rcases family_descends (prefixWord ++ tailWord_7926949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7927016 : List Nat := [2, 1, 4, 1, 2, 1, 1, 2, 5, 1, 3]
def baseStart_7927016 : Nat := 118140960795 + 7927016 * 2 ^ 59
def prefixEnd_7927016 : Nat := 4983230072969 + 3 ^ 40 * 7927016 * 2
def baseEnd_7927016 : Nat := 4070369363881062747144323

theorem tailTrace_7927016 : CollatzResearch.WordTrace tailWord_7927016 prefixEnd_7927016 4070369363881062747144323 := by
  unfold tailWord_7927016
  simp only [CollatzResearch.WordTrace]
  refine ⟨144561012924891166697136451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192748017233188222262848601 144561012924891166697136451)
  ·
    refine ⟨216841519387336750045704677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144561012924891166697136451 216841519387336750045704677)
    ·
      refine ⟨40657784885125640633569627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 216841519387336750045704677 40657784885125640633569627)
      ·
        refine ⟨60986677327688460950354441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40657784885125640633569627 60986677327688460950354441)
        ·
          refine ⟨45740007995766345712765831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60986677327688460950354441 45740007995766345712765831)
          ·
            refine ⟨68610011993649518569148747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45740007995766345712765831 68610011993649518569148747)
            ·
              refine ⟨102915017990474277853723121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68610011993649518569148747 102915017990474277853723121)
              ·
                refine ⟨77186263492855708390292341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102915017990474277853723121 77186263492855708390292341)
                ·
                  refine ⟨7236212202455222661589907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 77186263492855708390292341 7236212202455222661589907)
                  ·
                    refine ⟨10854318303682833992384861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7236212202455222661589907 10854318303682833992384861)
                    ·
                      refine ⟨4070369363881062747144323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10854318303682833992384861 4070369363881062747144323)
                      ·
                        rfl

theorem cell23_7927016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 2, 5, 1, 3].length) (baseStart_7927016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7927016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7927016 prefixEnd_7927016 := by exact prefixLift 7927016
  have htrace : WordTrace (prefixWord ++ tailWord_7927016) baseStart_7927016 baseEnd_7927016 := by
    simpa [prefixWord, tailWord_7927016, baseEnd_7927016] using wordTrace_append hprefix tailTrace_7927016
  have hstable : (prefixWord ++ tailWord_7927016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7927016).length < 2 ^ (prefixWord ++ tailWord_7927016).sum := by decide
  have hdescent : baseEnd_7927016 < baseStart_7927016 := by decide
  rcases family_descends (prefixWord ++ tailWord_7927016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7927023 : List Nat := [1, 1, 2, 1, 8, 1, 1, 2, 6]
def baseStart_7927023 : Nat := 118140960795 + 7927023 * 2 ^ 59
def prefixEnd_7927023 : Nat := 4983230072969 + 3 ^ 40 * 7927023 * 2
def baseEnd_7927023 : Nat := 452263662027293802195199

theorem tailTrace_7927023 : CollatzResearch.WordTrace tailWord_7927023 prefixEnd_7927023 452263662027293802195199 := by
  unfold tailWord_7927023
  simp only [CollatzResearch.WordTrace]
  refine ⟨289122281160756973589777723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192748187440504649059851815 289122281160756973589777723)
  ·
    refine ⟨433683421741135460384666585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289122281160756973589777723 433683421741135460384666585)
    ·
      refine ⟨325262566305851595288499939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 433683421741135460384666585 325262566305851595288499939)
      ·
        refine ⟨487893849458777392932749909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 325262566305851595288499939 487893849458777392932749909)
        ·
          refine ⟨5717506048345047573430663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 487893849458777392932749909 5717506048345047573430663)
          ·
            refine ⟨8576259072517571360145995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5717506048345047573430663 8576259072517571360145995)
            ·
              refine ⟨12864388608776357040218993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8576259072517571360145995 12864388608776357040218993)
              ·
                refine ⟨9648291456582267780164245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12864388608776357040218993 9648291456582267780164245)
                ·
                  refine ⟨452263662027293802195199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9648291456582267780164245 452263662027293802195199)
                  ·
                    rfl

theorem cell23_7927023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 1, 1, 2, 6].length) (baseStart_7927023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7927023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7927023 prefixEnd_7927023 := by exact prefixLift 7927023
  have htrace : WordTrace (prefixWord ++ tailWord_7927023) baseStart_7927023 baseEnd_7927023 := by
    simpa [prefixWord, tailWord_7927023, baseEnd_7927023] using wordTrace_append hprefix tailTrace_7927023
  have hstable : (prefixWord ++ tailWord_7927023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7927023).length < 2 ^ (prefixWord ++ tailWord_7927023).sum := by decide
  have hdescent : baseEnd_7927023 < baseStart_7927023 := by decide
  rcases family_descends (prefixWord ++ tailWord_7927023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7927032 : List Nat := [2, 1, 2, 1, 1, 2, 1, 1, 2, 10]
def baseStart_7927032 : Nat := 118140960795 + 7927032 * 2 ^ 59
def prefixEnd_7927032 : Nat := 4983230072969 + 3 ^ 40 * 7927032 * 2
def baseEnd_7927032 : Nat := 1356792526523844894848083

theorem tailTrace_7927032 : CollatzResearch.WordTrace tailWord_7927032 prefixEnd_7927032 1356792526523844894848083 := by
  unfold tailWord_7927032
  simp only [CollatzResearch.WordTrace]
  refine ⟨144561304708862184063427675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192748406278482912084570233 144561304708862184063427675)
  ·
    refine ⟨216841957063293276095141513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144561304708862184063427675 216841957063293276095141513)
    ·
      refine ⟨162631467797469957071356135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216841957063293276095141513 162631467797469957071356135)
      ·
        refine ⟨243947201696204935607034203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162631467797469957071356135 243947201696204935607034203)
        ·
          refine ⟨365920802544307403410551305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 243947201696204935607034203 365920802544307403410551305)
          ·
            refine ⟨274440601908230552557913479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 365920802544307403410551305 274440601908230552557913479)
            ·
              refine ⟨411660902862345828836870219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 274440601908230552557913479 411660902862345828836870219)
              ·
                refine ⟨617491354293518743255305329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 411660902862345828836870219 617491354293518743255305329)
                ·
                  refine ⟨463118515720139057441478997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 617491354293518743255305329 463118515720139057441478997)
                  ·
                    refine ⟨1356792526523844894848083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 463118515720139057441478997 1356792526523844894848083)
                    ·
                      rfl

theorem cell23_7927032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 2, 10].length) (baseStart_7927032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7927032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7927032 prefixEnd_7927032 := by exact prefixLift 7927032
  have htrace : WordTrace (prefixWord ++ tailWord_7927032) baseStart_7927032 baseEnd_7927032 := by
    simpa [prefixWord, tailWord_7927032, baseEnd_7927032] using wordTrace_append hprefix tailTrace_7927032
  have hstable : (prefixWord ++ tailWord_7927032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7927032).length < 2 ^ (prefixWord ++ tailWord_7927032).sum := by decide
  have hdescent : baseEnd_7927032 < baseStart_7927032 := by decide
  rcases family_descends (prefixWord ++ tailWord_7927032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7927033 : List Nat := [1, 2, 1, 3, 1, 1, 3, 6, 1, 1, 3]
def baseStart_7927033 : Nat := 118140960795 + 7927033 * 2 ^ 59
def prefixEnd_7927033 : Nat := 4983230072969 + 3 ^ 40 * 7927033 * 2
def baseEnd_7927033 : Nat := 4070378093052189180631745

theorem tailTrace_7927033 : CollatzResearch.WordTrace tailWord_7927033 prefixEnd_7927033 4070378093052189180631745 := by
  unfold tailWord_7927033
  simp only [CollatzResearch.WordTrace]
  refine ⟨289122645890720745297641753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192748430593813830198427835 289122645890720745297641753)
  ·
    refine ⟨216841984418040558973231315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 289122645890720745297641753 216841984418040558973231315)
    ·
      refine ⟨325262976627060838459846973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216841984418040558973231315 325262976627060838459846973)
      ·
        refine ⟨121973616235147814422442615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 325262976627060838459846973 121973616235147814422442615)
        ·
          refine ⟨182960424352721721633663923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121973616235147814422442615 182960424352721721633663923)
          ·
            refine ⟨274440636529082582450495885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182960424352721721633663923 274440636529082582450495885)
            ·
              refine ⟨102915238698405968418935957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 274440636529082582450495885 102915238698405968418935957)
              ·
                refine ⟨4824151813987779769637623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 102915238698405968418935957 4824151813987779769637623)
                ·
                  refine ⟨7236227720981669654456435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4824151813987779769637623 7236227720981669654456435)
                  ·
                    refine ⟨10854341581472504481684653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7236227720981669654456435 10854341581472504481684653)
                    ·
                      refine ⟨4070378093052189180631745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10854341581472504481684653 4070378093052189180631745)
                      ·
                        rfl

theorem cell23_7927033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 6, 1, 1, 3].length) (baseStart_7927033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7927033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7927033 prefixEnd_7927033 := by exact prefixLift 7927033
  have htrace : WordTrace (prefixWord ++ tailWord_7927033) baseStart_7927033 baseEnd_7927033 := by
    simpa [prefixWord, tailWord_7927033, baseEnd_7927033] using wordTrace_append hprefix tailTrace_7927033
  have hstable : (prefixWord ++ tailWord_7927033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7927033).length < 2 ^ (prefixWord ++ tailWord_7927033).sum := by decide
  have hdescent : baseEnd_7927033 < baseStart_7927033 := by decide
  rcases family_descends (prefixWord ++ tailWord_7927033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7927066 : List Nat := [3, 1, 1, 3, 3, 1, 1, 2, 4, 4]
def baseStart_7927066 : Nat := 118140960795 + 7927066 * 2 ^ 59
def prefixEnd_7927066 : Nat := 4983230072969 + 3 ^ 40 * 7927066 * 2
def baseEnd_7927066 : Nat := 1356798345971262517173031

theorem tailTrace_7927066 : CollatzResearch.WordTrace tailWord_7927066 prefixEnd_7927066 1356798345971262517173031 := by
  unfold tailWord_7927066
  simp only [CollatzResearch.WordTrace]
  refine ⟨72280962374900297983398263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192749232999734127955728701 72280962374900297983398263)
  ·
    refine ⟨108421443562350446975097395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72280962374900297983398263 108421443562350446975097395)
    ·
      refine ⟨162632165343525670462646093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108421443562350446975097395 162632165343525670462646093)
      ·
        refine ⟨60987062003822126423492285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 162632165343525670462646093 60987062003822126423492285)
        ·
          refine ⟨22870148251433297408809607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60987062003822126423492285 22870148251433297408809607)
          ·
            refine ⟨34305222377149946113214411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22870148251433297408809607 34305222377149946113214411)
            ·
              refine ⟨51457833565724919169821617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34305222377149946113214411 51457833565724919169821617)
              ·
                refine ⟨38593375174293689377366213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51457833565724919169821617 38593375174293689377366213)
                ·
                  refine ⟨7236257845180066758256165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38593375174293689377366213 7236257845180066758256165)
                  ·
                    refine ⟨1356798345971262517173031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7236257845180066758256165 1356798345971262517173031)
                    ·
                      rfl

theorem cell23_7927066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 2, 4, 4].length) (baseStart_7927066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7927066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7927066 prefixEnd_7927066 := by exact prefixLift 7927066
  have htrace : WordTrace (prefixWord ++ tailWord_7927066) baseStart_7927066 baseEnd_7927066 := by
    simpa [prefixWord, tailWord_7927066, baseEnd_7927066] using wordTrace_append hprefix tailTrace_7927066
  have hstable : (prefixWord ++ tailWord_7927066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7927066).length < 2 ^ (prefixWord ++ tailWord_7927066).sum := by decide
  have hdescent : baseEnd_7927066 < baseStart_7927066 := by decide
  rcases family_descends (prefixWord ++ tailWord_7927066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7927076 : List Nat := [2, 3, 1, 3, 1, 1, 4, 1, 1, 1, 5]
def baseStart_7927076 : Nat := 118140960795 + 7927076 * 2 ^ 59
def prefixEnd_7927076 : Nat := 4983230072969 + 3 ^ 40 * 7927076 * 2
def baseEnd_7927076 : Nat := 4070400172720332512394047

theorem tailTrace_7927076 : CollatzResearch.WordTrace tailWord_7927076 prefixEnd_7927076 4070400172720332512394047 := by
  unfold tailWord_7927076
  simp only [CollatzResearch.WordTrace]
  refine ⟨144562107114782481820728541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192749476153043309094304721 144562107114782481820728541)
  ·
    refine ⟨54210790168043430682773203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144562107114782481820728541 54210790168043430682773203)
    ·
      refine ⟨81316185252065146024159805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54210790168043430682773203 81316185252065146024159805)
      ·
        refine ⟨30493569469524429759059927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81316185252065146024159805 30493569469524429759059927)
        ·
          refine ⟨45740354204286644638589891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30493569469524429759059927 45740354204286644638589891)
          ·
            refine ⟨68610531306429966957884837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45740354204286644638589891 68610531306429966957884837)
            ·
              refine ⟨12864474619955618804603407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68610531306429966957884837 12864474619955618804603407)
              ·
                refine ⟨19296711929933428206905111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12864474619955618804603407 19296711929933428206905111)
                ·
                  refine ⟨28945067894900142310357667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19296711929933428206905111 28945067894900142310357667)
                  ·
                    refine ⟨43417601842350213465536501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28945067894900142310357667 43417601842350213465536501)
                    ·
                      refine ⟨4070400172720332512394047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43417601842350213465536501 4070400172720332512394047)
                      ·
                        rfl

theorem cell23_7927076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 4, 1, 1, 1, 5].length) (baseStart_7927076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7927076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7927076 prefixEnd_7927076 := by exact prefixLift 7927076
  have htrace : WordTrace (prefixWord ++ tailWord_7927076) baseStart_7927076 baseEnd_7927076 := by
    simpa [prefixWord, tailWord_7927076, baseEnd_7927076] using wordTrace_append hprefix tailTrace_7927076
  have hstable : (prefixWord ++ tailWord_7927076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7927076).length < 2 ^ (prefixWord ++ tailWord_7927076).sum := by decide
  have hdescent : baseEnd_7927076 < baseStart_7927076 := by decide
  rcases family_descends (prefixWord ++ tailWord_7927076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7927090 : List Nat := [3, 2, 1, 1, 4, 1, 3, 1, 3, 2, 2]
def baseStart_7927090 : Nat := 118140960795 + 7927090 * 2 ^ 59
def prefixEnd_7927090 : Nat := 4983230072969 + 3 ^ 40 * 7927090 * 2
def baseEnd_7927090 : Nat := 4070407361449495457618983

theorem tailTrace_7927090 : CollatzResearch.WordTrace tailWord_7927090 prefixEnd_7927090 4070407361449495457618983 := by
  unfold tailWord_7927090
  simp only [CollatzResearch.WordTrace]
  refine ⟨72281181212878561008116681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192749816567676162688311149 72281181212878561008116681)
  ·
    refine ⟨54210885909658920756087511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72281181212878561008116681 54210885909658920756087511)
    ·
      refine ⟨81316328864488381134131267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54210885909658920756087511 81316328864488381134131267)
      ·
        refine ⟨121974493296732571701196901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81316328864488381134131267 121974493296732571701196901)
        ·
          refine ⟨22870217493137357193974419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 121974493296732571701196901 22870217493137357193974419)
          ·
            refine ⟨34305326239706035790961629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22870217493137357193974419 34305326239706035790961629)
            ·
              refine ⟨12864497339889763421610611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34305326239706035790961629 12864497339889763421610611)
              ·
                refine ⟨19296746009834645132415917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12864497339889763421610611 19296746009834645132415917)
                ·
                  refine ⟨7236279753687991924655969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19296746009834645132415917 7236279753687991924655969)
                  ·
                    refine ⟨5427209815265993943491977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7236279753687991924655969 5427209815265993943491977)
                    ·
                      refine ⟨4070407361449495457618983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5427209815265993943491977 4070407361449495457618983)
                      ·
                        rfl

theorem cell23_7927090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 3, 1, 3, 2, 2].length) (baseStart_7927090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7927090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7927090 prefixEnd_7927090 := by exact prefixLift 7927090
  have htrace : WordTrace (prefixWord ++ tailWord_7927090) baseStart_7927090 baseEnd_7927090 := by
    simpa [prefixWord, tailWord_7927090, baseEnd_7927090] using wordTrace_append hprefix tailTrace_7927090
  have hstable : (prefixWord ++ tailWord_7927090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7927090).length < 2 ^ (prefixWord ++ tailWord_7927090).sum := by decide
  have hdescent : baseEnd_7927090 < baseStart_7927090 := by decide
  rcases family_descends (prefixWord ++ tailWord_7927090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7927100 : List Nat := [2, 2, 2, 2, 1, 5, 2, 1, 2, 4]
def baseStart_7927100 : Nat := 118140960795 + 7927100 * 2 ^ 59
def prefixEnd_7927100 : Nat := 4983230072969 + 3 ^ 40 * 7927100 * 2
def baseEnd_7927100 : Nat := 1356804165418680139497979

theorem tailTrace_7927100 : CollatzResearch.WordTrace tailWord_7927100 prefixEnd_7927100 1356804165418680139497979 := by
  unfold tailWord_7927100
  simp only [CollatzResearch.WordTrace]
  refine ⟨144562544790739007870165377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192750059720985343826887169 144562544790739007870165377)
  ·
    refine ⟨108421908593054255902624033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144562544790739007870165377 108421908593054255902624033)
    ·
      refine ⟨81316431444790691926968025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108421908593054255902624033 81316431444790691926968025)
      ·
        refine ⟨60987323583593018945226019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81316431444790691926968025 60987323583593018945226019)
        ·
          refine ⟨91480985375389528417839029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60987323583593018945226019 91480985375389528417839029)
          ·
            refine ⟨8576342378942768289172409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 91480985375389528417839029 8576342378942768289172409)
            ·
              refine ⟨6432256784207076216879307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8576342378942768289172409 6432256784207076216879307)
              ·
                refine ⟨9648385176310614325318961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6432256784207076216879307 9648385176310614325318961)
                ·
                  refine ⟨7236288882232960743989221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9648385176310614325318961 7236288882232960743989221)
                  ·
                    refine ⟨1356804165418680139497979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7236288882232960743989221 1356804165418680139497979)
                    ·
                      rfl

theorem cell23_7927100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 5, 2, 1, 2, 4].length) (baseStart_7927100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7927100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7927100 prefixEnd_7927100 := by exact prefixLift 7927100
  have htrace : WordTrace (prefixWord ++ tailWord_7927100) baseStart_7927100 baseEnd_7927100 := by
    simpa [prefixWord, tailWord_7927100, baseEnd_7927100] using wordTrace_append hprefix tailTrace_7927100
  have hstable : (prefixWord ++ tailWord_7927100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7927100).length < 2 ^ (prefixWord ++ tailWord_7927100).sum := by decide
  have hdescent : baseEnd_7927100 < baseStart_7927100 := by decide
  rcases family_descends (prefixWord ++ tailWord_7927100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7927140 : List Nat := [2, 3, 1, 1, 3, 3, 2, 2, 2, 1, 3]
def baseStart_7927140 : Nat := 118140960795 + 7927140 * 2 ^ 59
def prefixEnd_7927140 : Nat := 4983230072969 + 3 ^ 40 * 7927140 * 2
def baseEnd_7927140 : Nat := 4070433035482220261993753

theorem tailTrace_7927140 : CollatzResearch.WordTrace tailWord_7927140 prefixEnd_7927140 4070433035482220261993753 := by
  unfold tailWord_7927140
  simp only [CollatzResearch.WordTrace]
  refine ⟨144563274250666551285893437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192751032334222068381191249 144563274250666551285893437)
  ·
    refine ⟨54211227843999956732210039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144563274250666551285893437 54211227843999956732210039)
    ·
      refine ⟨81316841765999935098315059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54211227843999956732210039 81316841765999935098315059)
      ·
        refine ⟨121975262648999902647472589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81316841765999935098315059 121975262648999902647472589)
        ·
          refine ⟨45740723493374963492802221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 121975262648999902647472589 45740723493374963492802221)
          ·
            refine ⟨17152771310015611309800833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45740723493374963492802221 17152771310015611309800833)
            ·
              refine ⟨12864578482511708482350625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17152771310015611309800833 12864578482511708482350625)
              ·
                refine ⟨9648433861883781361762969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12864578482511708482350625 9648433861883781361762969)
                ·
                  refine ⟨7236325396412836021322227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9648433861883781361762969 7236325396412836021322227)
                  ·
                    refine ⟨10854488094619254031983341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7236325396412836021322227 10854488094619254031983341)
                    ·
                      refine ⟨4070433035482220261993753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10854488094619254031983341 4070433035482220261993753)
                      ·
                        rfl

theorem cell23_7927140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 2, 2, 2, 1, 3].length) (baseStart_7927140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7927140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7927140 prefixEnd_7927140 := by exact prefixLift 7927140
  have htrace : WordTrace (prefixWord ++ tailWord_7927140) baseStart_7927140 baseEnd_7927140 := by
    simpa [prefixWord, tailWord_7927140, baseEnd_7927140] using wordTrace_append hprefix tailTrace_7927140
  have hstable : (prefixWord ++ tailWord_7927140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7927140).length < 2 ^ (prefixWord ++ tailWord_7927140).sum := by decide
  have hdescent : baseEnd_7927140 < baseStart_7927140 := by decide
  rcases family_descends (prefixWord ++ tailWord_7927140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7927163 : List Nat := [1, 1, 1, 1, 1, 6, 4, 1, 1, 4, 2]
def baseStart_7927163 : Nat := 118140960795 + 7927163 * 2 ^ 59
def prefixEnd_7927163 : Nat := 4983230072969 + 3 ^ 40 * 7927163 * 2
def baseEnd_7927163 : Nat := 4070444845537273672006147

theorem tailTrace_7927163 : CollatzResearch.WordTrace tailWord_7927163 prefixEnd_7927163 4070444845537273672006147 := by
  unfold tailWord_7927163
  simp only [CollatzResearch.WordTrace]
  refine ⟨289127387380249777499874143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192751591586833184999916095 289127387380249777499874143)
  ·
    refine ⟨433691081070374666249811215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289127387380249777499874143 433691081070374666249811215)
    ·
      refine ⟨650536621605561999374716823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 433691081070374666249811215 650536621605561999374716823)
      ·
        refine ⟨975804932408342999062075235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 650536621605561999374716823 975804932408342999062075235)
        ·
          refine ⟨1463707398612514498593112853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 975804932408342999062075235 1463707398612514498593112853)
          ·
            refine ⟨68611284309961617121552165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 1463707398612514498593112853 68611284309961617121552165)
            ·
              refine ⟨12864615808117803210291031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68611284309961617121552165 12864615808117803210291031)
              ·
                refine ⟨19296923712176704815436547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12864615808117803210291031 19296923712176704815436547)
                ·
                  refine ⟨28945385568265057223154821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19296923712176704815436547 28945385568265057223154821)
                  ·
                    refine ⟨5427259794049698229341529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28945385568265057223154821 5427259794049698229341529)
                    ·
                      refine ⟨4070444845537273672006147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5427259794049698229341529 4070444845537273672006147)
                      ·
                        rfl

theorem cell23_7927163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 4, 1, 1, 4, 2].length) (baseStart_7927163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7927163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7927163 prefixEnd_7927163 := by exact prefixLift 7927163
  have htrace : WordTrace (prefixWord ++ tailWord_7927163) baseStart_7927163 baseEnd_7927163 := by
    simpa [prefixWord, tailWord_7927163, baseEnd_7927163] using wordTrace_append hprefix tailTrace_7927163
  have hstable : (prefixWord ++ tailWord_7927163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7927163).length < 2 ^ (prefixWord ++ tailWord_7927163).sum := by decide
  have hdescent : baseEnd_7927163 < baseStart_7927163 := by decide
  rcases family_descends (prefixWord ++ tailWord_7927163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7927197 : List Nat := [1, 4, 2, 1, 3, 1, 3, 2, 2, 2, 2]
def baseStart_7927197 : Nat := 118140960795 + 7927197 * 2 ^ 59
def prefixEnd_7927197 : Nat := 4983230072969 + 3 ^ 40 * 7927197 * 2
def baseEnd_7927197 : Nat := 4070462303879526538980991

theorem tailTrace_7927197 : CollatzResearch.WordTrace tailWord_7927197 prefixEnd_7927197 4070462303879526538980991 := by
  unfold tailWord_7927197
  simp only [CollatzResearch.WordTrace]
  refine ⟨289128627462126601306611845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192752418308084400871074563 289128627462126601306611845)
  ·
    refine ⟨54211617649148737744989721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 289128627462126601306611845 54211617649148737744989721)
    ·
      refine ⟨40658713236861553308742291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54211617649148737744989721 40658713236861553308742291)
      ·
        refine ⟨60988069855292329963113437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40658713236861553308742291 60988069855292329963113437)
        ·
          refine ⟨22870526195734623736167539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60988069855292329963113437 22870526195734623736167539)
          ·
            refine ⟨34305789293601935604251309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22870526195734623736167539 34305789293601935604251309)
            ·
              refine ⟨12864670985100725851594241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34305789293601935604251309 12864670985100725851594241)
              ·
                refine ⟨9648503238825544388695681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12864670985100725851594241 9648503238825544388695681)
                ·
                  refine ⟨7236377429119158291521761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9648503238825544388695681 7236377429119158291521761)
                  ·
                    refine ⟨5427283071839368718641321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7236377429119158291521761 5427283071839368718641321)
                    ·
                      refine ⟨4070462303879526538980991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5427283071839368718641321 4070462303879526538980991)
                      ·
                        rfl

theorem cell23_7927197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 3, 2, 2, 2, 2].length) (baseStart_7927197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7927197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7927197 prefixEnd_7927197 := by exact prefixLift 7927197
  have htrace : WordTrace (prefixWord ++ tailWord_7927197) baseStart_7927197 baseEnd_7927197 := by
    simpa [prefixWord, tailWord_7927197, baseEnd_7927197] using wordTrace_append hprefix tailTrace_7927197
  have hstable : (prefixWord ++ tailWord_7927197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7927197).length < 2 ^ (prefixWord ++ tailWord_7927197).sum := by decide
  have hdescent : baseEnd_7927197 < baseStart_7927197 := by decide
  rcases family_descends (prefixWord ++ tailWord_7927197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7927234 : List Nat := [3, 5, 2, 1, 1, 1, 1, 1, 2, 1, 5]
def baseStart_7927234 : Nat := 118140960795 + 7927234 * 2 ^ 59
def prefixEnd_7927234 : Nat := 4983230072969 + 3 ^ 40 * 7927234 * 2
def baseEnd_7927234 : Nat := 4070481302663742894218321

theorem tailTrace_7927234 : CollatzResearch.WordTrace tailWord_7927234 prefixEnd_7927234 4070481302663742894218321 := by
  unfold tailWord_7927234
  simp only [CollatzResearch.WordTrace]
  refine ⟨72282494240748139156427189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192753317975328371083805837 72282494240748139156427189)
  ·
    refine ⟨6776483835070138045915049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 72282494240748139156427189 6776483835070138045915049)
    ·
      refine ⟨5082362876302603534436287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6776483835070138045915049 5082362876302603534436287)
      ·
        refine ⟨7623544314453905301654431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5082362876302603534436287 7623544314453905301654431)
        ·
          refine ⟨11435316471680857952481647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7623544314453905301654431 11435316471680857952481647)
          ·
            refine ⟨17152974707521286928722471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11435316471680857952481647 17152974707521286928722471)
            ·
              refine ⟨25729462061281930393083707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17152974707521286928722471 25729462061281930393083707)
              ·
                refine ⟨38594193091922895589625561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25729462061281930393083707 38594193091922895589625561)
                ·
                  refine ⟨28945644818942171692219171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38594193091922895589625561 28945644818942171692219171)
                  ·
                    refine ⟨43418467228413257538328757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28945644818942171692219171 43418467228413257538328757)
                    ·
                      refine ⟨4070481302663742894218321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43418467228413257538328757 4070481302663742894218321)
                      ·
                        rfl

theorem cell23_7927234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 1, 1, 2, 1, 5].length) (baseStart_7927234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7927234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7927234 prefixEnd_7927234 := by exact prefixLift 7927234
  have htrace : WordTrace (prefixWord ++ tailWord_7927234) baseStart_7927234 baseEnd_7927234 := by
    simpa [prefixWord, tailWord_7927234, baseEnd_7927234] using wordTrace_append hprefix tailTrace_7927234
  have hstable : (prefixWord ++ tailWord_7927234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7927234).length < 2 ^ (prefixWord ++ tailWord_7927234).sum := by decide
  have hdescent : baseEnd_7927234 < baseStart_7927234 := by decide
  rcases family_descends (prefixWord ++ tailWord_7927234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7927253 : List Nat := [1, 3, 2, 3, 1, 1, 3, 2, 2, 1, 4]
def baseStart_7927253 : Nat := 118140960795 + 7927253 * 2 ^ 59
def prefixEnd_7927253 : Nat := 4983230072969 + 3 ^ 40 * 7927253 * 2
def baseEnd_7927253 : Nat := 4070491058796178319880733

theorem tailTrace_7927253 : CollatzResearch.WordTrace tailWord_7927253 prefixEnd_7927253 4070491058796178319880733 := by
  unfold tailWord_7927253
  simp only [CollatzResearch.WordTrace]
  refine ⟨289130669949923722870650413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192753779966615815247100275 289130669949923722870650413)
  ·
    refine ⟨108424001231221396076493905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 289130669949923722870650413 108424001231221396076493905)
    ·
      refine ⟨81318000923416047057370429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108424001231221396076493905 81318000923416047057370429)
      ·
        refine ⟨30494250346281017646513911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81318000923416047057370429 30494250346281017646513911)
        ·
          refine ⟨45741375519421526469770867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30494250346281017646513911 45741375519421526469770867)
          ·
            refine ⟨68612063279132289704656301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45741375519421526469770867 68612063279132289704656301)
            ·
              refine ⟨25729523729674608639246113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68612063279132289704656301 25729523729674608639246113)
              ·
                refine ⟨19297142797255956479434585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25729523729674608639246113 19297142797255956479434585)
                ·
                  refine ⟨14472857097941967359575939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19297142797255956479434585 14472857097941967359575939)
                  ·
                    refine ⟨21709285646912951039363909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14472857097941967359575939 21709285646912951039363909)
                    ·
                      refine ⟨4070491058796178319880733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21709285646912951039363909 4070491058796178319880733)
                      ·
                        rfl

theorem cell23_7927253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 3, 2, 2, 1, 4].length) (baseStart_7927253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7927253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7927253 prefixEnd_7927253 := by exact prefixLift 7927253
  have htrace : WordTrace (prefixWord ++ tailWord_7927253) baseStart_7927253 baseEnd_7927253 := by
    simpa [prefixWord, tailWord_7927253, baseEnd_7927253] using wordTrace_append hprefix tailTrace_7927253
  have hstable : (prefixWord ++ tailWord_7927253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7927253).length < 2 ^ (prefixWord ++ tailWord_7927253).sum := by decide
  have hdescent : baseEnd_7927253 < baseStart_7927253 := by decide
  rcases family_descends (prefixWord ++ tailWord_7927253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7927310 : List Nat := [4, 1, 1, 2, 4, 1, 2, 2, 6]
def baseStart_7927310 : Nat := 118140960795 + 7927310 * 2 ^ 59
def prefixEnd_7927310 : Nat := 4983230072969 + 3 ^ 40 * 7927310 * 2
def baseEnd_7927310 : Nat := 452280036354831621874219

theorem tailTrace_7927310 : CollatzResearch.WordTrace tailWord_7927310 prefixEnd_7927310 452280036354831621874219 := by
  unfold tailWord_7927310
  simp only [CollatzResearch.WordTrace]
  refine ⟨36141593613839652700684423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 192755165940478147736983589 36141593613839652700684423)
  ·
    refine ⟨54212390420759479051026635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36141593613839652700684423 54212390420759479051026635)
    ·
      refine ⟨81318585631139218576539953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54212390420759479051026635 81318585631139218576539953)
      ·
        refine ⟨60988939223354413932404965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81318585631139218576539953 60988939223354413932404965)
        ·
          refine ⟨11435426104378952612325931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60988939223354413932404965 11435426104378952612325931)
          ·
            refine ⟨17153139156568428918488897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11435426104378952612325931 17153139156568428918488897)
            ·
              refine ⟨12864854367426321688866673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17153139156568428918488897 12864854367426321688866673)
              ·
                refine ⟨9648640775569741266650005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12864854367426321688866673 9648640775569741266650005)
                ·
                  refine ⟨452280036354831621874219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9648640775569741266650005 452280036354831621874219)
                  ·
                    rfl

theorem cell23_7927310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 2, 2, 6].length) (baseStart_7927310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7927310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7927310 prefixEnd_7927310 := by exact prefixLift 7927310
  have htrace : WordTrace (prefixWord ++ tailWord_7927310) baseStart_7927310 baseEnd_7927310 := by
    simpa [prefixWord, tailWord_7927310, baseEnd_7927310] using wordTrace_append hprefix tailTrace_7927310
  have hstable : (prefixWord ++ tailWord_7927310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7927310).length < 2 ^ (prefixWord ++ tailWord_7927310).sum := by decide
  have hdescent : baseEnd_7927310 < baseStart_7927310 := by decide
  rcases family_descends (prefixWord ++ tailWord_7927310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7927330 : List Nat := [3, 3, 1, 1, 1, 1, 2, 2, 4, 3, 2]
def baseStart_7927330 : Nat := 118140960795 + 7927330 * 2 ^ 59
def prefixEnd_7927330 : Nat := 4983230072969 + 3 ^ 40 * 7927330 * 2
def baseEnd_7927330 : Nat := 4070530596806574518617879

theorem tailTrace_7927330 : CollatzResearch.WordTrace tailWord_7927330 prefixEnd_7927330 4070530596806574518617879 := by
  unfold tailWord_7927330
  simp only [CollatzResearch.WordTrace]
  refine ⟨72283369592661191255300861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192755652247096510014135629 72283369592661191255300861)
  ·
    refine ⟨27106263597247946720737823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72283369592661191255300861 27106263597247946720737823)
    ·
      refine ⟨40659395395871920081106735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27106263597247946720737823 40659395395871920081106735)
      ·
        refine ⟨60989093093807880121660103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40659395395871920081106735 60989093093807880121660103)
        ·
          refine ⟨91483639640711820182490155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60989093093807880121660103 91483639640711820182490155)
          ·
            refine ⟨137225459461067730273735233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91483639640711820182490155 137225459461067730273735233)
            ·
              refine ⟨102919094595800797705301425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137225459461067730273735233 102919094595800797705301425)
              ·
                refine ⟨77189320946850598278976069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102919094595800797705301425 77189320946850598278976069)
                ·
                  refine ⟨14472997677534487177308013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 77189320946850598278976069 14472997677534487177308013)
                  ·
                    refine ⟨5427374129075432691490505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14472997677534487177308013 5427374129075432691490505)
                    ·
                      refine ⟨4070530596806574518617879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5427374129075432691490505 4070530596806574518617879)
                      ·
                        rfl

theorem cell23_7927330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 2, 4, 3, 2].length) (baseStart_7927330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7927330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7927330 prefixEnd_7927330 := by exact prefixLift 7927330
  have htrace : WordTrace (prefixWord ++ tailWord_7927330) baseStart_7927330 baseEnd_7927330 := by
    simpa [prefixWord, tailWord_7927330, baseEnd_7927330] using wordTrace_append hprefix tailTrace_7927330
  have hstable : (prefixWord ++ tailWord_7927330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7927330).length < 2 ^ (prefixWord ++ tailWord_7927330).sum := by decide
  have hdescent : baseEnd_7927330 < baseStart_7927330 := by decide
  rcases family_descends (prefixWord ++ tailWord_7927330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7927347 : List Nat := [1, 1, 1, 2, 4, 5, 1, 1, 2, 3, 2]
def baseStart_7927347 : Nat := 118140960795 + 7927347 * 2 ^ 59
def prefixEnd_7927347 : Nat := 4983230072969 + 3 ^ 40 * 7927347 * 2
def baseEnd_7927347 : Nat := 4070539325977700952105301

theorem tailTrace_7927347 : CollatzResearch.WordTrace tailWord_7927347 prefixEnd_7927347 4070539325977700952105301 := by
  unfold tailWord_7927347
  simp only [CollatzResearch.WordTrace]
  refine ⟨289134098411583176924572295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192756065607722117949714863 289134098411583176924572295)
  ·
    refine ⟨433701147617374765386858443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289134098411583176924572295 433701147617374765386858443)
    ·
      refine ⟨650551721426062148080287665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 433701147617374765386858443 650551721426062148080287665)
      ·
        refine ⟨487913791069546611060215749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 650551721426062148080287665 487913791069546611060215749)
        ·
          refine ⟨91483835825539989573790453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 487913791069546611060215749 91483835825539989573790453)
          ·
            refine ⟨8576609608644374022542855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 91483835825539989573790453 8576609608644374022542855)
            ·
              refine ⟨12864914412966561033814283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8576609608644374022542855 12864914412966561033814283)
              ·
                refine ⟨19297371619449841550721425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12864914412966561033814283 19297371619449841550721425)
                ·
                  refine ⟨14473028714587381163041069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19297371619449841550721425 14473028714587381163041069)
                  ·
                    refine ⟨5427385767970267936140401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14473028714587381163041069 5427385767970267936140401)
                    ·
                      refine ⟨4070539325977700952105301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5427385767970267936140401 4070539325977700952105301)
                      ·
                        rfl

theorem cell23_7927347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 5, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 5, 1, 1, 2, 3, 2].length) (baseStart_7927347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7927347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7927347 prefixEnd_7927347 := by exact prefixLift 7927347
  have htrace : WordTrace (prefixWord ++ tailWord_7927347) baseStart_7927347 baseEnd_7927347 := by
    simpa [prefixWord, tailWord_7927347, baseEnd_7927347] using wordTrace_append hprefix tailTrace_7927347
  have hstable : (prefixWord ++ tailWord_7927347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7927347).length < 2 ^ (prefixWord ++ tailWord_7927347).sum := by decide
  have hdescent : baseEnd_7927347 < baseStart_7927347 := by decide
  rcases family_descends (prefixWord ++ tailWord_7927347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7927353 : List Nat := [1, 2, 1, 5, 1, 2, 2, 2, 1, 6]
def baseStart_7927353 : Nat := 118140960795 + 7927353 * 2 ^ 59
def prefixEnd_7927353 : Nat := 4983230072969 + 3 ^ 40 * 7927353 * 2
def baseEnd_7927353 : Nat := 1356847468953875976210091

theorem tailTrace_7927353 : CollatzResearch.WordTrace tailWord_7927353 prefixEnd_7927353 1356847468953875976210091 := by
  unfold tailWord_7927353
  simp only [CollatzResearch.WordTrace]
  refine ⟨289134317249561439949290713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192756211499707626632860475 289134317249561439949290713)
  ·
    refine ⟨216850737937171079961968035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 289134317249561439949290713 216850737937171079961968035)
    ·
      refine ⟨325276106905756619942952053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216850737937171079961968035 325276106905756619942952053)
      ·
        refine ⟨30494635022414683119651755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 325276106905756619942952053 30494635022414683119651755)
        ·
          refine ⟨45741952533622024679477633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30494635022414683119651755 45741952533622024679477633)
          ·
            refine ⟨34306464400216518509608225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45741952533622024679477633 34306464400216518509608225)
            ·
              refine ⟨25729848300162388882206169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34306464400216518509608225 25729848300162388882206169)
              ·
                refine ⟨19297386225121791661654627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25729848300162388882206169 19297386225121791661654627)
                ·
                  refine ⟨28946079337682687492481941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19297386225121791661654627 28946079337682687492481941)
                  ·
                    refine ⟨1356847468953875976210091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28946079337682687492481941 1356847468953875976210091)
                    ·
                      rfl

theorem cell23_7927353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 2, 2, 1, 6].length) (baseStart_7927353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7927353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7927353 prefixEnd_7927353 := by exact prefixLift 7927353
  have htrace : WordTrace (prefixWord ++ tailWord_7927353) baseStart_7927353 baseEnd_7927353 := by
    simpa [prefixWord, tailWord_7927353, baseEnd_7927353] using wordTrace_append hprefix tailTrace_7927353
  have hstable : (prefixWord ++ tailWord_7927353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7927353).length < 2 ^ (prefixWord ++ tailWord_7927353).sum := by decide
  have hdescent : baseEnd_7927353 < baseStart_7927353 := by decide
  rcases family_descends (prefixWord ++ tailWord_7927353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7927360 : List Nat := [2, 1, 1, 2, 2, 2, 1, 1, 7, 2, 2]
def baseStart_7927360 : Nat := 118140960795 + 7927360 * 2 ^ 59
def prefixEnd_7927360 : Nat := 4983230072969 + 3 ^ 40 * 7927360 * 2
def baseEnd_7927360 : Nat := 4070546001226209401242741

theorem tailTrace_7927360 : CollatzResearch.WordTrace tailWord_7927360 prefixEnd_7927360 4070546001226209401242741 := by
  unfold tailWord_7927360
  simp only [CollatzResearch.WordTrace]
  refine ⟨144567286280268040072397767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192756381707024053429863689 144567286280268040072397767)
  ·
    refine ⟨216850929420402060108596651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144567286280268040072397767 216850929420402060108596651)
    ·
      refine ⟨325276394130603090162894977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216850929420402060108596651 325276394130603090162894977)
      ·
        refine ⟨243957295597952317622171233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 325276394130603090162894977 243957295597952317622171233)
        ·
          refine ⟨182967971698464238216628425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 243957295597952317622171233 182967971698464238216628425)
          ·
            refine ⟨137225978773848178662471319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 182967971698464238216628425 137225978773848178662471319)
            ·
              refine ⟨205838968160772267993706979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137225978773848178662471319 205838968160772267993706979)
              ·
                refine ⟨308758452241158401990560469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 205838968160772267993706979 308758452241158401990560469)
                ·
                  refine ⟨7236526224402150046653761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 308758452241158401990560469 7236526224402150046653761)
                  ·
                    refine ⟨5427394668301612534990321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7236526224402150046653761 5427394668301612534990321)
                    ·
                      refine ⟨4070546001226209401242741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5427394668301612534990321 4070546001226209401242741)
                      ·
                        rfl

theorem cell23_7927360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 1, 7, 2, 2].length) (baseStart_7927360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7927360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7927360 prefixEnd_7927360 := by exact prefixLift 7927360
  have htrace : WordTrace (prefixWord ++ tailWord_7927360) baseStart_7927360 baseEnd_7927360 := by
    simpa [prefixWord, tailWord_7927360, baseEnd_7927360] using wordTrace_append hprefix tailTrace_7927360
  have hstable : (prefixWord ++ tailWord_7927360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7927360).length < 2 ^ (prefixWord ++ tailWord_7927360).sum := by decide
  have hdescent : baseEnd_7927360 < baseStart_7927360 := by decide
  rcases family_descends (prefixWord ++ tailWord_7927360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7927377 : List Nat := [1, 2, 2, 1, 3, 2, 4, 1, 3, 2, 2]
def baseStart_7927377 : Nat := 118140960795 + 7927377 * 2 ^ 59
def prefixEnd_7927377 : Nat := 4983230072969 + 3 ^ 40 * 7927377 * 2
def baseEnd_7927377 : Nat := 4070554730397335834730163

theorem tailTrace_7927377 : CollatzResearch.WordTrace tailWord_7927377 prefixEnd_7927377 4070554730397335834730163 := by
  unfold tailWord_7927377
  simp only [CollatzResearch.WordTrace]
  refine ⟨289135192601474492048164385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192756795067649661365442923 289135192601474492048164385)
  ·
    refine ⟨216851394451105869036123289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 289135192601474492048164385 216851394451105869036123289)
    ·
      refine ⟨162638545838329401777092467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216851394451105869036123289 162638545838329401777092467)
      ·
        refine ⟨243957818757494102665638701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162638545838329401777092467 243957818757494102665638701)
        ·
          refine ⟨91484182034060288499614513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 243957818757494102665638701 91484182034060288499614513)
          ·
            refine ⟨68613136525545216374710885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91484182034060288499614513 68613136525545216374710885)
            ·
              refine ⟨12864963098539728070258291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68613136525545216374710885 12864963098539728070258291)
              ·
                refine ⟨19297444647809592105387437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12864963098539728070258291 19297444647809592105387437)
                ·
                  refine ⟨7236541742928597039520289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19297444647809592105387437 7236541742928597039520289)
                  ·
                    refine ⟨5427406307196447779640217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7236541742928597039520289 5427406307196447779640217)
                    ·
                      refine ⟨4070554730397335834730163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5427406307196447779640217 4070554730397335834730163)
                      ·
                        rfl

theorem cell23_7927377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 4, 1, 3, 2, 2].length) (baseStart_7927377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7927377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7927377 prefixEnd_7927377 := by exact prefixLift 7927377
  have htrace : WordTrace (prefixWord ++ tailWord_7927377) baseStart_7927377 baseEnd_7927377 := by
    simpa [prefixWord, tailWord_7927377, baseEnd_7927377] using wordTrace_append hprefix tailTrace_7927377
  have hstable : (prefixWord ++ tailWord_7927377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7927377).length < 2 ^ (prefixWord ++ tailWord_7927377).sum := by decide
  have hdescent : baseEnd_7927377 < baseStart_7927377 := by decide
  rcases family_descends (prefixWord ++ tailWord_7927377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7927397 : List Nat := [1, 3, 1, 3, 3, 2, 2, 2, 1, 2, 3]
def baseStart_7927397 : Nat := 118140960795 + 7927397 * 2 ^ 59
def prefixEnd_7927397 : Nat := 4983230072969 + 3 ^ 40 * 7927397 * 2
def baseEnd_7927397 : Nat := 4070565000010425756480071

theorem tailTrace_7927397 : CollatzResearch.WordTrace tailWord_7927397 prefixEnd_7927397 4070565000010425756480071 := by
  unfold tailWord_7927397
  simp only [CollatzResearch.WordTrace]
  refine ⟨289135922061402035463892445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192757281374268023642594963 289135922061402035463892445)
  ·
    refine ⟨108425970773025763298959667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 289135922061402035463892445 108425970773025763298959667)
    ·
      refine ⟨162638956159538644948439501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108425970773025763298959667 162638956159538644948439501)
      ·
        refine ⟨60989608559826991855664813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 162638956159538644948439501 60989608559826991855664813)
        ·
          refine ⟨22871103209935121945874305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60989608559826991855664813 22871103209935121945874305)
          ·
            refine ⟨17153327407451341459405729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22871103209935121945874305 17153327407451341459405729)
            ·
              refine ⟨12864995555588506094554297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17153327407451341459405729 12864995555588506094554297)
              ·
                refine ⟨9648746666691379570915723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12864995555588506094554297 9648746666691379570915723)
                ·
                  refine ⟨14473120000037069356373585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9648746666691379570915723 14473120000037069356373585)
                  ·
                    refine ⟨10854840000027802017280189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14473120000037069356373585 10854840000027802017280189)
                    ·
                      refine ⟨4070565000010425756480071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10854840000027802017280189 4070565000010425756480071)
                      ·
                        rfl

theorem cell23_7927397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 2, 2, 1, 2, 3].length) (baseStart_7927397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7927397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7927397 prefixEnd_7927397 := by exact prefixLift 7927397
  have htrace : WordTrace (prefixWord ++ tailWord_7927397) baseStart_7927397 baseEnd_7927397 := by
    simpa [prefixWord, tailWord_7927397, baseEnd_7927397] using wordTrace_append hprefix tailTrace_7927397
  have hstable : (prefixWord ++ tailWord_7927397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7927397).length < 2 ^ (prefixWord ++ tailWord_7927397).sum := by decide
  have hdescent : baseEnd_7927397 < baseStart_7927397 := by decide
  rcases family_descends (prefixWord ++ tailWord_7927397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7927400 : List Nat := [2, 1, 4, 3, 1, 1, 4, 7]
def baseStart_7927400 : Nat := 118140960795 + 7927400 * 2 ^ 59
def prefixEnd_7927400 : Nat := 4983230072969 + 3 ^ 40 * 7927400 * 2
def baseEnd_7927400 : Nat := 150761723720458860916391

theorem tailTrace_7927400 : CollatzResearch.WordTrace tailWord_7927400 prefixEnd_7927400 150761723720458860916391 := by
  unfold tailWord_7927400
  simp only [CollatzResearch.WordTrace]
  refine ⟨144568015740195583488125827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192757354320260777984167769 144568015740195583488125827)
  ·
    refine ⟨216852023610293375232188741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144568015740195583488125827 216852023610293375232188741)
    ·
      refine ⟨40659754426930007856035389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 216852023610293375232188741 40659754426930007856035389)
      ·
        refine ⟨15247407910098752946013271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40659754426930007856035389 15247407910098752946013271)
        ·
          refine ⟨22871111865148129419019907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15247407910098752946013271 22871111865148129419019907)
          ·
            refine ⟨34306667797722194128529861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22871111865148129419019907 34306667797722194128529861)
            ·
              refine ⟨6432500212072911399099349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34306667797722194128529861 6432500212072911399099349)
              ·
                refine ⟨150761723720458860916391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6432500212072911399099349 150761723720458860916391)
                ·
                  rfl

theorem cell23_7927400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 4, 7].length) (baseStart_7927400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7927400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7927400 prefixEnd_7927400 := by exact prefixLift 7927400
  have htrace : WordTrace (prefixWord ++ tailWord_7927400) baseStart_7927400 baseEnd_7927400 := by
    simpa [prefixWord, tailWord_7927400, baseEnd_7927400] using wordTrace_append hprefix tailTrace_7927400
  have hstable : (prefixWord ++ tailWord_7927400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7927400).length < 2 ^ (prefixWord ++ tailWord_7927400).sum := by decide
  have hdescent : baseEnd_7927400 < baseStart_7927400 := by decide
  rcases family_descends (prefixWord ++ tailWord_7927400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7927420 : List Nat := [2, 2, 2, 1, 1, 2, 1, 2, 5, 3, 2]
def baseStart_7927420 : Nat := 118140960795 + 7927420 * 2 ^ 59
def prefixEnd_7927420 : Nat := 4983230072969 + 3 ^ 40 * 7927420 * 2
def baseEnd_7927420 : Nat := 4070576810065479166492465

theorem tailTrace_7927420 : CollatzResearch.WordTrace tailWord_7927420 prefixEnd_7927420 4070576810065479166492465 := by
  unfold tailWord_7927420
  simp only [CollatzResearch.WordTrace]
  refine ⟨144568380470159355195989857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192757840626879140261319809 144568380470159355195989857)
  ·
    refine ⟨108426285352619516396992393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144568380470159355195989857 108426285352619516396992393)
    ·
      refine ⟨81319714014464637297744295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108426285352619516396992393 81319714014464637297744295)
      ·
        refine ⟨121979571021696955946616443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81319714014464637297744295 121979571021696955946616443)
        ·
          refine ⟨182969356532545433919924665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121979571021696955946616443 182969356532545433919924665)
          ·
            refine ⟨137227017399409075439943499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 182969356532545433919924665 137227017399409075439943499)
            ·
              refine ⟨205840526099113613159915249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137227017399409075439943499 205840526099113613159915249)
              ·
                refine ⟨154380394574335209869936437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 205840526099113613159915249 154380394574335209869936437)
                ·
                  refine ⟨14473161991343925925306541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 154380394574335209869936437 14473161991343925925306541)
                  ·
                    refine ⟨5427435746753972221989953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14473161991343925925306541 5427435746753972221989953)
                    ·
                      refine ⟨4070576810065479166492465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5427435746753972221989953 4070576810065479166492465)
                      ·
                        rfl

theorem cell23_7927420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 2, 5, 3, 2].length) (baseStart_7927420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7927420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7927420 prefixEnd_7927420 := by exact prefixLift 7927420
  have htrace : WordTrace (prefixWord ++ tailWord_7927420) baseStart_7927420 baseEnd_7927420 := by
    simpa [prefixWord, tailWord_7927420, baseEnd_7927420] using wordTrace_append hprefix tailTrace_7927420
  have hstable : (prefixWord ++ tailWord_7927420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7927420).length < 2 ^ (prefixWord ++ tailWord_7927420).sum := by decide
  have hdescent : baseEnd_7927420 < baseStart_7927420 := by decide
  rcases family_descends (prefixWord ++ tailWord_7927420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7927428 : List Nat := [2, 3, 2, 1, 4, 1, 3, 2, 1, 2, 2]
def baseStart_7927428 : Nat := 118140960795 + 7927428 * 2 ^ 59
def prefixEnd_7927428 : Nat := 4983230072969 + 3 ^ 40 * 7927428 * 2
def baseEnd_7927428 : Nat := 4070580917910715135192429

theorem tailTrace_7927428 : CollatzResearch.WordTrace tailWord_7927428 prefixEnd_7927428 4070580917910715135192429 := by
  unfold tailWord_7927428
  simp only [CollatzResearch.WordTrace]
  refine ⟨144568526362144863879135469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192758035149526485172180625 144568526362144863879135469)
  ·
    refine ⟨54213197385804323954675801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144568526362144863879135469 54213197385804323954675801)
    ·
      refine ⟨40659898039353242966006851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54213197385804323954675801 40659898039353242966006851)
      ·
        refine ⟨60989847059029864449010277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40659898039353242966006851 60989847059029864449010277)
        ·
          refine ⟨11435596323568099584189427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60989847059029864449010277 11435596323568099584189427)
          ·
            refine ⟨17153394485352149376284141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11435596323568099584189427 17153394485352149376284141)
            ·
              refine ⟨6432522932007056016106553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17153394485352149376284141 6432522932007056016106553)
              ·
                refine ⟨4824392199005292012079915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6432522932007056016106553 4824392199005292012079915)
                ·
                  refine ⟨7236588298507938018119873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4824392199005292012079915 7236588298507938018119873)
                  ·
                    refine ⟨5427441223880953513589905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7236588298507938018119873 5427441223880953513589905)
                    ·
                      refine ⟨4070580917910715135192429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5427441223880953513589905 4070580917910715135192429)
                      ·
                        rfl

theorem cell23_7927428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 3, 2, 1, 2, 2].length) (baseStart_7927428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7927428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7927428 prefixEnd_7927428 := by exact prefixLift 7927428
  have htrace : WordTrace (prefixWord ++ tailWord_7927428) baseStart_7927428 baseEnd_7927428 := by
    simpa [prefixWord, tailWord_7927428, baseEnd_7927428] using wordTrace_append hprefix tailTrace_7927428
  have hstable : (prefixWord ++ tailWord_7927428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7927428).length < 2 ^ (prefixWord ++ tailWord_7927428).sum := by decide
  have hdescent : baseEnd_7927428 < baseStart_7927428 := by decide
  rcases family_descends (prefixWord ++ tailWord_7927428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7927454 : List Nat := [4, 3, 1, 1, 1, 3, 1, 1, 3, 3, 2]
def baseStart_7927454 : Nat := 118140960795 + 7927454 * 2 ^ 59
def prefixEnd_7927454 : Nat := 4983230072969 + 3 ^ 40 * 7927454 * 2
def baseEnd_7927454 : Nat := 4070594268407732033467309

theorem tailTrace_7927454 : CollatzResearch.WordTrace tailWord_7927454 prefixEnd_7927454 4070594268407732033467309 := by
  unfold tailWord_7927454
  simp only [CollatzResearch.WordTrace]
  refine ⟨36142250127774441774839677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 192758667348130356132478277 36142250127774441774839677)
  ·
    refine ⟨13553343797915415665564879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36142250127774441774839677 13553343797915415665564879)
    ·
      refine ⟨20330015696873123498347319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13553343797915415665564879 20330015696873123498347319)
      ·
        refine ⟨30495023545309685247520979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20330015696873123498347319 30495023545309685247520979)
        ·
          refine ⟨45742535317964527871281469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30495023545309685247520979 45742535317964527871281469)
          ·
            refine ⟨17153450744236697951730551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45742535317964527871281469 17153450744236697951730551)
            ·
              refine ⟨25730176116355046927595827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17153450744236697951730551 25730176116355046927595827)
              ·
                refine ⟨38595264174532570391393741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25730176116355046927595827 38595264174532570391393741)
                ·
                  refine ⟨14473224065449713896772653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38595264174532570391393741 14473224065449713896772653)
                  ·
                    refine ⟨5427459024543642711289745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14473224065449713896772653 5427459024543642711289745)
                    ·
                      refine ⟨4070594268407732033467309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5427459024543642711289745 4070594268407732033467309)
                      ·
                        rfl

theorem cell23_7927454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 1, 1, 3, 3, 2].length) (baseStart_7927454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7927454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7927454 prefixEnd_7927454 := by exact prefixLift 7927454
  have htrace : WordTrace (prefixWord ++ tailWord_7927454) baseStart_7927454 baseEnd_7927454 := by
    simpa [prefixWord, tailWord_7927454, baseEnd_7927454] using wordTrace_append hprefix tailTrace_7927454
  have hstable : (prefixWord ++ tailWord_7927454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7927454).length < 2 ^ (prefixWord ++ tailWord_7927454).sum := by decide
  have hdescent : baseEnd_7927454 < baseStart_7927454 := by decide
  rcases family_descends (prefixWord ++ tailWord_7927454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7927483 : List Nat := [1, 1, 1, 1, 1, 2, 3, 2, 3, 5, 3]
def baseStart_7927483 : Nat := 118140960795 + 7927483 * 2 ^ 59
def prefixEnd_7927483 : Nat := 4983230072969 + 3 ^ 40 * 7927483 * 2
def baseEnd_7927483 : Nat := 4070609159346712420004675

theorem tailTrace_7927483 : CollatzResearch.WordTrace tailWord_7927483 prefixEnd_7927483 4070609159346712420004675 := by
  unfold tailWord_7927483
  simp only [CollatzResearch.WordTrace]
  refine ⟨289139058739090472151523103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192759372492726981434348735 289139058739090472151523103)
  ·
    refine ⟨433708588108635708227284655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289139058739090472151523103 433708588108635708227284655)
    ·
      refine ⟨650562882162953562340926983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 433708588108635708227284655 650562882162953562340926983)
      ·
        refine ⟨975844323244430343511390475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 650562882162953562340926983 975844323244430343511390475)
        ·
          refine ⟨1463766484866645515267085713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 975844323244430343511390475 1463766484866645515267085713)
          ·
            refine ⟨1097824863649984136450314285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1463766484866645515267085713 1097824863649984136450314285)
            ·
              refine ⟨411684323868744051168867857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1097824863649984136450314285 411684323868744051168867857)
              ·
                refine ⟨308763242901558038376650893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 411684323868744051168867857 308763242901558038376650893)
                ·
                  refine ⟨115786216088084264391244085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 308763242901558038376650893 115786216088084264391244085)
                  ·
                    refine ⟨10854957758257899786679133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 115786216088084264391244085 10854957758257899786679133)
                    ·
                      refine ⟨4070609159346712420004675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10854957758257899786679133 4070609159346712420004675)
                      ·
                        rfl

theorem cell23_7927483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 2, 3, 5, 3].length) (baseStart_7927483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7927483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7927483 prefixEnd_7927483 := by exact prefixLift 7927483
  have htrace : WordTrace (prefixWord ++ tailWord_7927483) baseStart_7927483 baseEnd_7927483 := by
    simpa [prefixWord, tailWord_7927483, baseEnd_7927483] using wordTrace_append hprefix tailTrace_7927483
  have hstable : (prefixWord ++ tailWord_7927483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7927483).length < 2 ^ (prefixWord ++ tailWord_7927483).sum := by decide
  have hdescent : baseEnd_7927483 < baseStart_7927483 := by decide
  rcases family_descends (prefixWord ++ tailWord_7927483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7927484 : List Nat := [2, 2, 2, 3, 1, 2, 1, 4, 2, 2, 2]
def baseStart_7927484 : Nat := 118140960795 + 7927484 * 2 ^ 59
def prefixEnd_7927484 : Nat := 4983230072969 + 3 ^ 40 * 7927484 * 2
def baseEnd_7927484 : Nat := 4070609672827366916092171

theorem tailTrace_7927484 : CollatzResearch.WordTrace tailWord_7927484 prefixEnd_7927484 4070609672827366916092171 := by
  unfold tailWord_7927484
  simp only [CollatzResearch.WordTrace]
  refine ⟨144569547606043424661154753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192759396808057899548206337 144569547606043424661154753)
  ·
    refine ⟨108427160704532568495866065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144569547606043424661154753 108427160704532568495866065)
    ·
      refine ⟨81320370528399426371899549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108427160704532568495866065 81320370528399426371899549)
      ·
        refine ⟨30495138948149784889462331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81320370528399426371899549 30495138948149784889462331)
        ·
          refine ⟨45742708422224677334193497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30495138948149784889462331 45742708422224677334193497)
          ·
            refine ⟨34307031316668508000645123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45742708422224677334193497 34307031316668508000645123)
            ·
              refine ⟨51460546975002762000967685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34307031316668508000645123 51460546975002762000967685)
              ·
                refine ⟨9648852557813017875181441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51460546975002762000967685 9648852557813017875181441)
                ·
                  refine ⟨7236639418359763406386081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9648852557813017875181441 7236639418359763406386081)
                  ·
                    refine ⟨5427479563769822554789561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7236639418359763406386081 5427479563769822554789561)
                    ·
                      refine ⟨4070609672827366916092171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5427479563769822554789561 4070609672827366916092171)
                      ·
                        rfl

theorem cell23_7927484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 4, 2, 2, 2].length) (baseStart_7927484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7927484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7927484 prefixEnd_7927484 := by exact prefixLift 7927484
  have htrace : WordTrace (prefixWord ++ tailWord_7927484) baseStart_7927484 baseEnd_7927484 := by
    simpa [prefixWord, tailWord_7927484, baseEnd_7927484] using wordTrace_append hprefix tailTrace_7927484
  have hstable : (prefixWord ++ tailWord_7927484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7927484).length < 2 ^ (prefixWord ++ tailWord_7927484).sum := by decide
  have hdescent : baseEnd_7927484 < baseStart_7927484 := by decide
  rcases family_descends (prefixWord ++ tailWord_7927484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7927494 : List Nat := [6, 1, 2, 1, 1, 2, 1, 1, 2, 6]
def baseStart_7927494 : Nat := 118140960795 + 7927494 * 2 ^ 59
def prefixEnd_7927494 : Nat := 4983230072969 + 3 ^ 40 * 7927494 * 2
def baseEnd_7927494 : Nat := 1356871602544637292322375

theorem tailTrace_7927494 : CollatzResearch.WordTrace tailWord_7927494 prefixEnd_7927494 1356871602544637292322375 := by
  unfold tailWord_7927494
  simp only [CollatzResearch.WordTrace]
  refine ⟨9035608123189081907192923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 192759639961367080686782357 9035608123189081907192923)
  ·
    refine ⟨13553412184783622860789385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9035608123189081907192923 13553412184783622860789385)
    ·
      refine ⟨10165059138587717145592039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13553412184783622860789385 10165059138587717145592039)
      ·
        refine ⟨15247588707881575718388059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10165059138587717145592039 15247588707881575718388059)
        ·
          refine ⟨22871383061822363577582089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15247588707881575718388059 22871383061822363577582089)
          ·
            refine ⟨17153537296366772683186567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22871383061822363577582089 17153537296366772683186567)
            ·
              refine ⟨25730305944550159024779851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17153537296366772683186567 25730305944550159024779851)
              ·
                refine ⟨38595458916825238537169777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25730305944550159024779851 38595458916825238537169777)
                ·
                  refine ⟨28946594187618928902877333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38595458916825238537169777 28946594187618928902877333)
                  ·
                    refine ⟨1356871602544637292322375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28946594187618928902877333 1356871602544637292322375)
                    ·
                      rfl

theorem cell23_7927494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 1, 1, 2, 6].length) (baseStart_7927494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7927494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7927494 prefixEnd_7927494 := by exact prefixLift 7927494
  have htrace : WordTrace (prefixWord ++ tailWord_7927494) baseStart_7927494 baseEnd_7927494 := by
    simpa [prefixWord, tailWord_7927494, baseEnd_7927494] using wordTrace_append hprefix tailTrace_7927494
  have hstable : (prefixWord ++ tailWord_7927494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7927494).length < 2 ^ (prefixWord ++ tailWord_7927494).sum := by decide
  have hdescent : baseEnd_7927494 < baseStart_7927494 := by decide
  rcases family_descends (prefixWord ++ tailWord_7927494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7927501 : List Nat := [1, 6, 2, 1, 1, 2, 2, 1, 1, 4, 2]
def baseStart_7927501 : Nat := 118140960795 + 7927501 * 2 ^ 59
def prefixEnd_7927501 : Nat := 4983230072969 + 3 ^ 40 * 7927501 * 2
def baseEnd_7927501 : Nat := 4070618401998493349579593

theorem tailTrace_7927501 : CollatzResearch.WordTrace tailWord_7927501 prefixEnd_7927501 4070618401998493349579593 := by
  unfold tailWord_7927501
  simp only [CollatzResearch.WordTrace]
  refine ⟨289139715253025261225678357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192759810168683507483785571 289139715253025261225678357)
  ·
    refine ⟨13553424152485559119953673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 289139715253025261225678357 13553424152485559119953673)
    ·
      refine ⟨10165068114364169339965255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13553424152485559119953673 10165068114364169339965255)
      ·
        refine ⟨15247602171546254009947883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10165068114364169339965255 15247602171546254009947883)
        ·
          refine ⟨22871403257319381014921825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15247602171546254009947883 22871403257319381014921825)
          ·
            refine ⟨17153552442989535761191369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22871403257319381014921825 17153552442989535761191369)
            ·
              refine ⟨12865164332242151820893527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17153552442989535761191369 12865164332242151820893527)
              ·
                refine ⟨19297746498363227731340291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12865164332242151820893527 19297746498363227731340291)
                ·
                  refine ⟨28946619747544841597010437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19297746498363227731340291 28946619747544841597010437)
                  ·
                    refine ⟨5427491202664657799439457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28946619747544841597010437 5427491202664657799439457)
                    ·
                      refine ⟨4070618401998493349579593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5427491202664657799439457 4070618401998493349579593)
                      ·
                        rfl

theorem cell23_7927501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 2, 1, 1, 4, 2].length) (baseStart_7927501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7927501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7927501 prefixEnd_7927501 := by exact prefixLift 7927501
  have htrace : WordTrace (prefixWord ++ tailWord_7927501) baseStart_7927501 baseEnd_7927501 := by
    simpa [prefixWord, tailWord_7927501, baseEnd_7927501] using wordTrace_append hprefix tailTrace_7927501
  have hstable : (prefixWord ++ tailWord_7927501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7927501).length < 2 ^ (prefixWord ++ tailWord_7927501).sum := by decide
  have hdescent : baseEnd_7927501 < baseStart_7927501 := by decide
  rcases family_descends (prefixWord ++ tailWord_7927501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7927503 : List Nat := [1, 1, 2, 1, 1, 3, 1, 4, 4, 5]
def baseStart_7927503 : Nat := 118140960795 + 7927503 * 2 ^ 59
def prefixEnd_7927503 : Nat := 4983230072969 + 3 ^ 40 * 7927503 * 2
def baseEnd_7927503 : Nat := 1356873142986600780584861

theorem tailTrace_7927503 : CollatzResearch.WordTrace tailWord_7927503 prefixEnd_7927503 1356873142986600780584861 := by
  unfold tailWord_7927503
  simp only [CollatzResearch.WordTrace]
  refine ⟨289139788199018015567251163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192759858799345343711500775 289139788199018015567251163)
  ·
    refine ⟨433709682298527023350876745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289139788199018015567251163 433709682298527023350876745)
    ·
      refine ⟨325282261723895267513157559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 433709682298527023350876745 325282261723895267513157559)
      ·
        refine ⟨487923392585842901269736339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 325282261723895267513157559 487923392585842901269736339)
        ·
          refine ⟨731885088878764351904604509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 487923392585842901269736339 731885088878764351904604509)
          ·
            refine ⟨274456908329536631964226691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 731885088878764351904604509 274456908329536631964226691)
            ·
              refine ⟨411685362494304947946340037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 274456908329536631964226691 411685362494304947946340037)
              ·
                refine ⟨77191005467682177739938757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 411685362494304947946340037 77191005467682177739938757)
                ·
                  refine ⟨14473313525190408326238517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 77191005467682177739938757 14473313525190408326238517)
                  ·
                    refine ⟨1356873142986600780584861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14473313525190408326238517 1356873142986600780584861)
                    ·
                      rfl

theorem cell23_7927503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 4, 4, 5].length) (baseStart_7927503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7927503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7927503 prefixEnd_7927503 := by exact prefixLift 7927503
  have htrace : WordTrace (prefixWord ++ tailWord_7927503) baseStart_7927503 baseEnd_7927503 := by
    simpa [prefixWord, tailWord_7927503, baseEnd_7927503] using wordTrace_append hprefix tailTrace_7927503
  have hstable : (prefixWord ++ tailWord_7927503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7927503).length < 2 ^ (prefixWord ++ tailWord_7927503).sum := by decide
  have hdescent : baseEnd_7927503 < baseStart_7927503 := by decide
  rcases family_descends (prefixWord ++ tailWord_7927503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7927520 : List Nat := [2, 1, 1, 3, 1, 2, 5, 1, 2, 5]
def baseStart_7927520 : Nat := 118140960795 + 7927520 * 2 ^ 59
def prefixEnd_7927520 : Nat := 4983230072969 + 3 ^ 40 * 7927520 * 2
def baseEnd_7927520 : Nat := 1356876052710309591747335

theorem tailTrace_7927520 : CollatzResearch.WordTrace tailWord_7927520 prefixEnd_7927520 1356876052710309591747335 := by
  unfold tailWord_7927520
  simp only [CollatzResearch.WordTrace]
  refine ⟨144570204119978213735310007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192760272159970951647080009 144570204119978213735310007)
  ·
    refine ⟨216855306179967320602965011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144570204119978213735310007 216855306179967320602965011)
    ·
      refine ⟨325282959269950980904447517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216855306179967320602965011 325282959269950980904447517)
      ·
        refine ⟨121981109726231617839167819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 325282959269950980904447517 121981109726231617839167819)
        ·
          refine ⟨182971664589347426758751729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121981109726231617839167819 182971664589347426758751729)
          ·
            refine ⟨137228748442010570069063797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 182971664589347426758751729 137228748442010570069063797)
            ·
              refine ⟨12865195166438490943974731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 137228748442010570069063797 12865195166438490943974731)
              ·
                refine ⟨19297792749657736415962097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12865195166438490943974731 19297792749657736415962097)
                ·
                  refine ⟨14473344562243302311971573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19297792749657736415962097 14473344562243302311971573)
                  ·
                    refine ⟨1356876052710309591747335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14473344562243302311971573 1356876052710309591747335)
                    ·
                      rfl

theorem cell23_7927520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 5, 1, 2, 5].length) (baseStart_7927520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7927520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7927520 prefixEnd_7927520 := by exact prefixLift 7927520
  have htrace : WordTrace (prefixWord ++ tailWord_7927520) baseStart_7927520 baseEnd_7927520 := by
    simpa [prefixWord, tailWord_7927520, baseEnd_7927520] using wordTrace_append hprefix tailTrace_7927520
  have hstable : (prefixWord ++ tailWord_7927520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7927520).length < 2 ^ (prefixWord ++ tailWord_7927520).sum := by decide
  have hdescent : baseEnd_7927520 < baseStart_7927520 := by decide
  rcases family_descends (prefixWord ++ tailWord_7927520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7927543 : List Nat := [1, 1, 3, 1, 1, 1, 4, 1, 2, 3, 5]
def baseStart_7927543 : Nat := 118140960795 + 7927543 * 2 ^ 59
def prefixEnd_7927543 : Nat := 4983230072969 + 3 ^ 40 * 7927543 * 2
def baseEnd_7927543 : Nat := 4070639968185982185254399

theorem tailTrace_7927543 : CollatzResearch.WordTrace tailWord_7927543 prefixEnd_7927543 4070639968185982185254399 := by
  unfold tailWord_7927543
  simp only [CollatzResearch.WordTrace]
  refine ⟨289141247118873102398707283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192760831412582068265804855 289141247118873102398707283)
  ·
    refine ⟨433711870678309653598060925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289141247118873102398707283 433711870678309653598060925)
    ·
      refine ⟨162641951504366120099272847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 433711870678309653598060925 162641951504366120099272847)
      ·
        refine ⟨243962927256549180148909271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162641951504366120099272847 243962927256549180148909271)
        ·
          refine ⟨365944390884823770223363907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 243962927256549180148909271 365944390884823770223363907)
          ·
            refine ⟨548916586327235655335045861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 365944390884823770223363907 548916586327235655335045861)
            ·
              refine ⟨102921859936356685375321099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 548916586327235655335045861 102921859936356685375321099)
              ·
                refine ⟨154382789904535028062981649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102921859936356685375321099 154382789904535028062981649)
                ·
                  refine ⟨115787092428401271047236237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 154382789904535028062981649 115787092428401271047236237)
                  ·
                    refine ⟨43420159660650476642713589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 115787092428401271047236237 43420159660650476642713589)
                    ·
                      refine ⟨4070639968185982185254399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43420159660650476642713589 4070639968185982185254399)
                      ·
                        rfl

theorem cell23_7927543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 1, 2, 3, 5].length) (baseStart_7927543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7927543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7927543 prefixEnd_7927543 := by exact prefixLift 7927543
  have htrace : WordTrace (prefixWord ++ tailWord_7927543) baseStart_7927543 baseEnd_7927543 := by
    simpa [prefixWord, tailWord_7927543, baseEnd_7927543] using wordTrace_append hprefix tailTrace_7927543
  have hstable : (prefixWord ++ tailWord_7927543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7927543).length < 2 ^ (prefixWord ++ tailWord_7927543).sum := by decide
  have hdescent : baseEnd_7927543 < baseStart_7927543 := by decide
  rcases family_descends (prefixWord ++ tailWord_7927543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7927560 : List Nat := [2, 1, 3, 2, 2, 1, 1, 1, 3, 4, 3]
def baseStart_7927560 : Nat := 118140960795 + 7927560 * 2 ^ 59
def prefixEnd_7927560 : Nat := 4983230072969 + 3 ^ 40 * 7927560 * 2
def baseEnd_7927560 : Nat := 4070648697357108618741821

theorem tailTrace_7927560 : CollatzResearch.WordTrace tailWord_7927560 prefixEnd_7927560 4070648697357108618741821 := by
  unfold tailWord_7927560
  simp only [CollatzResearch.WordTrace]
  refine ⟨144570933579905757151038067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192761244773207676201384089 144570933579905757151038067)
  ·
    refine ⟨216856400369858635726557101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144570933579905757151038067 216856400369858635726557101)
    ·
      refine ⟨81321150138696988397458913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 216856400369858635726557101 81321150138696988397458913)
      ·
        refine ⟨60990862604022741298094185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81321150138696988397458913 60990862604022741298094185)
        ·
          refine ⟨45743146953017055973570639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60990862604022741298094185 45743146953017055973570639)
          ·
            refine ⟨68614720429525583960355959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45743146953017055973570639 68614720429525583960355959)
            ·
              refine ⟨102922080644288375940533939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68614720429525583960355959 102922080644288375940533939)
              ·
                refine ⟨154383120966432563910800909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102922080644288375940533939 154383120966432563910800909)
                ·
                  refine ⟨57893670362412211466550341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 154383120966432563910800909 57893670362412211466550341)
                  ·
                    refine ⟨10855063192952289649978189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 57893670362412211466550341 10855063192952289649978189)
                    ·
                      refine ⟨4070648697357108618741821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10855063192952289649978189 4070648697357108618741821)
                      ·
                        rfl

theorem cell23_7927560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 1, 3, 4, 3].length) (baseStart_7927560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7927560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7927560 prefixEnd_7927560 := by exact prefixLift 7927560
  have htrace : WordTrace (prefixWord ++ tailWord_7927560) baseStart_7927560 baseEnd_7927560 := by
    simpa [prefixWord, tailWord_7927560, baseEnd_7927560] using wordTrace_append hprefix tailTrace_7927560
  have hstable : (prefixWord ++ tailWord_7927560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7927560).length < 2 ^ (prefixWord ++ tailWord_7927560).sum := by decide
  have hdescent : baseEnd_7927560 < baseStart_7927560 := by decide
  rcases family_descends (prefixWord ++ tailWord_7927560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7927601 : List Nat := [1, 2, 2, 3, 2, 3, 3, 2, 1, 4]
def baseStart_7927601 : Nat := 118140960795 + 7927601 * 2 ^ 59
def prefixEnd_7927601 : Nat := 4983230072969 + 3 ^ 40 * 7927601 * 2
def baseEnd_7927601 : Nat := 1356889916687980986109711

theorem tailTrace_7927601 : CollatzResearch.WordTrace tailWord_7927601 prefixEnd_7927601 1356889916687980986109711 := by
  unfold tailWord_7927601
  simp only [CollatzResearch.WordTrace]
  refine ⟨289143362552662978304318657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192762241701775318869545771 289143362552662978304318657)
  ·
    refine ⟨216857521914497233728238993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 289143362552662978304318657 216857521914497233728238993)
    ·
      refine ⟨162643141435872925296179245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216857521914497233728238993 162643141435872925296179245)
      ·
        refine ⟨60991178038452346986067217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 162643141435872925296179245 60991178038452346986067217)
        ·
          refine ⟨45743383528839260239550413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60991178038452346986067217 45743383528839260239550413)
          ·
            refine ⟨17153768823314722589831405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45743383528839260239550413 17153768823314722589831405)
            ·
              refine ⟨6432663308743020971186777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17153768823314722589831405 6432663308743020971186777)
              ·
                refine ⟨4824497481557265728390083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6432663308743020971186777 4824497481557265728390083)
                ·
                  refine ⟨7236746222335898592585125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4824497481557265728390083 7236746222335898592585125)
                  ·
                    refine ⟨1356889916687980986109711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7236746222335898592585125 1356889916687980986109711)
                    ·
                      rfl

theorem cell23_7927601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 3, 2, 1, 4].length) (baseStart_7927601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7927601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7927601 prefixEnd_7927601 := by exact prefixLift 7927601
  have htrace : WordTrace (prefixWord ++ tailWord_7927601) baseStart_7927601 baseEnd_7927601 := by
    simpa [prefixWord, tailWord_7927601, baseEnd_7927601] using wordTrace_append hprefix tailTrace_7927601
  have hstable : (prefixWord ++ tailWord_7927601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7927601).length < 2 ^ (prefixWord ++ tailWord_7927601).sum := by decide
  have hdescent : baseEnd_7927601 < baseStart_7927601 := by decide
  rcases family_descends (prefixWord ++ tailWord_7927601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7927607 : List Nat := [1, 1, 3, 1, 2, 1, 2, 5, 3, 1, 3]
def baseStart_7927607 : Nat := 118140960795 + 7927607 * 2 ^ 59
def prefixEnd_7927607 : Nat := 4983230072969 + 3 ^ 40 * 7927607 * 2
def baseEnd_7927607 : Nat := 4070672830947869934854105

theorem tailTrace_7927607 : CollatzResearch.WordTrace tailWord_7927607 prefixEnd_7927607 4070672830947869934854105 := by
  unfold tailWord_7927607
  simp only [CollatzResearch.WordTrace]
  refine ⟨289143581390641241329037075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192762387593760827552691383 289143581390641241329037075)
  ·
    refine ⟨433715372085961861993555613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289143581390641241329037075 433715372085961861993555613)
    ·
      refine ⟨162643264532235698247583355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 433715372085961861993555613 162643264532235698247583355)
      ·
        refine ⟨243964896798353547371375033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162643264532235698247583355 243964896798353547371375033)
        ·
          refine ⟨182973672598765160528531275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 243964896798353547371375033 182973672598765160528531275)
          ·
            refine ⟨274460508898147740792796913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182973672598765160528531275 274460508898147740792796913)
            ·
              refine ⟨205845381673610805594597685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 274460508898147740792796913 205845381673610805594597685)
              ·
                refine ⟨19298004531901013024493533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 205845381673610805594597685 19298004531901013024493533)
                ·
                  refine ⟨7236751699462879884185075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19298004531901013024493533 7236751699462879884185075)
                  ·
                    refine ⟨10855127549194319826277613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7236751699462879884185075 10855127549194319826277613)
                    ·
                      refine ⟨4070672830947869934854105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10855127549194319826277613 4070672830947869934854105)
                      ·
                        rfl

theorem cell23_7927607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 5, 3, 1, 3].length) (baseStart_7927607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7927607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7927607 prefixEnd_7927607 := by exact prefixLift 7927607
  have htrace : WordTrace (prefixWord ++ tailWord_7927607) baseStart_7927607 baseEnd_7927607 := by
    simpa [prefixWord, tailWord_7927607, baseEnd_7927607] using wordTrace_append hprefix tailTrace_7927607
  have hstable : (prefixWord ++ tailWord_7927607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7927607).length < 2 ^ (prefixWord ++ tailWord_7927607).sum := by decide
  have hdescent : baseEnd_7927607 < baseStart_7927607 := by decide
  rcases family_descends (prefixWord ++ tailWord_7927607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7927614 : List Nat := [4, 2, 1, 2, 2, 1, 4, 1, 6]
def baseStart_7927614 : Nat := 118140960795 + 7927614 * 2 ^ 59
def prefixEnd_7927614 : Nat := 4983230072969 + 3 ^ 40 * 7927614 * 2
def baseEnd_7927614 : Nat := 452297380590272378607397

theorem tailTrace_7927614 : CollatzResearch.WordTrace tailWord_7927614 prefixEnd_7927614 452297380590272378607397 := by
  unfold tailWord_7927614
  simp only [CollatzResearch.WordTrace]
  refine ⟨36142979587701985190567737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 192762557801077254349694597 36142979587701985190567737)
  ·
    refine ⟨27107234690776488892925803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36142979587701985190567737 27107234690776488892925803)
    ·
      refine ⟨40660852036164733339388705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27107234690776488892925803 40660852036164733339388705)
      ·
        refine ⟨30495639027123550004541529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40660852036164733339388705 30495639027123550004541529)
        ·
          refine ⟨22871729270342662503406147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30495639027123550004541529 22871729270342662503406147)
          ·
            refine ⟨34307593905513993755109221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22871729270342662503406147 34307593905513993755109221)
            ·
              refine ⟨6432673857283873829082979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34307593905513993755109221 6432673857283873829082979)
              ·
                refine ⟨9649010785925810743624469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6432673857283873829082979 9649010785925810743624469)
                ·
                  refine ⟨452297380590272378607397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9649010785925810743624469 452297380590272378607397)
                  ·
                    rfl

theorem cell23_7927614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 4, 1, 6].length) (baseStart_7927614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7927614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7927614 prefixEnd_7927614 := by exact prefixLift 7927614
  have htrace : WordTrace (prefixWord ++ tailWord_7927614) baseStart_7927614 baseEnd_7927614 := by
    simpa [prefixWord, tailWord_7927614, baseEnd_7927614] using wordTrace_append hprefix tailTrace_7927614
  have hstable : (prefixWord ++ tailWord_7927614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7927614).length < 2 ^ (prefixWord ++ tailWord_7927614).sum := by decide
  have hdescent : baseEnd_7927614 < baseStart_7927614 := by decide
  rcases family_descends (prefixWord ++ tailWord_7927614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7927634 : List Nat := [3, 2, 2, 1, 1, 3, 1, 3, 2, 3, 2]
def baseStart_7927634 : Nat := 118140960795 + 7927634 * 2 ^ 59
def prefixEnd_7927634 : Nat := 4983230072969 + 3 ^ 40 * 7927634 * 2
def baseEnd_7927634 : Nat := 4070686694925541329216481

theorem tailTrace_7927634 : CollatzResearch.WordTrace tailWord_7927634 prefixEnd_7927634 4070686694925541329216481 := by
  unfold tailWord_7927634
  simp only [CollatzResearch.WordTrace]
  refine ⟨72286141540385856235067489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192763044107695616626846637 72286141540385856235067489)
  ·
    refine ⟨54214606155289392176300617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72286141540385856235067489 54214606155289392176300617)
    ·
      refine ⟨40660954616467044132225463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54214606155289392176300617 40660954616467044132225463)
      ·
        refine ⟨60991431924700566198338195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40660954616467044132225463 60991431924700566198338195)
        ·
          refine ⟨91487147887050849297507293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60991431924700566198338195 91487147887050849297507293)
          ·
            refine ⟨34307680457644068486565235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91487147887050849297507293 34307680457644068486565235)
            ·
              refine ⟨51461520686466102729847853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34307680457644068486565235 51461520686466102729847853)
              ·
                refine ⟨19298070257424788523692945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51461520686466102729847853 19298070257424788523692945)
                ·
                  refine ⟨14473552693068591392769709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19298070257424788523692945 14473552693068591392769709)
                  ·
                    refine ⟨5427582259900721772288641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14473552693068591392769709 5427582259900721772288641)
                    ·
                      refine ⟨4070686694925541329216481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5427582259900721772288641 4070686694925541329216481)
                      ·
                        rfl

theorem cell23_7927634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 3, 2, 3, 2].length) (baseStart_7927634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7927634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7927634 prefixEnd_7927634 := by exact prefixLift 7927634
  have htrace : WordTrace (prefixWord ++ tailWord_7927634) baseStart_7927634 baseEnd_7927634 := by
    simpa [prefixWord, tailWord_7927634, baseEnd_7927634] using wordTrace_append hprefix tailTrace_7927634
  have hstable : (prefixWord ++ tailWord_7927634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7927634).length < 2 ^ (prefixWord ++ tailWord_7927634).sum := by decide
  have hdescent : baseEnd_7927634 < baseStart_7927634 := by decide
  rcases family_descends (prefixWord ++ tailWord_7927634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7927664 : List Nat := [2, 1, 1, 1, 4, 1, 1, 5, 3, 2, 2]
def baseStart_7927664 : Nat := 118140960795 + 7927664 * 2 ^ 59
def prefixEnd_7927664 : Nat := 4983230072969 + 3 ^ 40 * 7927664 * 2
def baseEnd_7927664 : Nat := 4070702099345176211841343

theorem tailTrace_7927664 : CollatzResearch.WordTrace tailWord_7927664 prefixEnd_7927664 4070702099345176211841343 := by
  unfold tailWord_7927664
  simp only [CollatzResearch.WordTrace]
  refine ⟨144572830175717370031931023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192763773567623160042574697 144572830175717370031931023)
  ·
    refine ⟨216859245263576055047896535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144572830175717370031931023 216859245263576055047896535)
    ·
      refine ⟨325288867895364082571844803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216859245263576055047896535 325288867895364082571844803)
      ·
        refine ⟨487933301843046123857767205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 325288867895364082571844803 487933301843046123857767205)
        ·
          refine ⟨91487494095571148223331351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 487933301843046123857767205 91487494095571148223331351)
          ·
            refine ⟨137231241143356722334997027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91487494095571148223331351 137231241143356722334997027)
            ·
              refine ⟨205846861715035083502495541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137231241143356722334997027 205846861715035083502495541)
              ·
                refine ⟨19298143285784539078358957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 205846861715035083502495541 19298143285784539078358957)
                ·
                  refine ⟨7236803732169202154384609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19298143285784539078358957 7236803732169202154384609)
                  ·
                    refine ⟨5427602799126901615788457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7236803732169202154384609 5427602799126901615788457)
                    ·
                      refine ⟨4070702099345176211841343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5427602799126901615788457 4070702099345176211841343)
                      ·
                        rfl

theorem cell23_7927664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 5, 3, 2, 2].length) (baseStart_7927664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7927664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7927664 prefixEnd_7927664 := by exact prefixLift 7927664
  have htrace : WordTrace (prefixWord ++ tailWord_7927664) baseStart_7927664 baseEnd_7927664 := by
    simpa [prefixWord, tailWord_7927664, baseEnd_7927664] using wordTrace_append hprefix tailTrace_7927664
  have hstable : (prefixWord ++ tailWord_7927664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7927664).length < 2 ^ (prefixWord ++ tailWord_7927664).sum := by decide
  have hdescent : baseEnd_7927664 < baseStart_7927664 := by decide
  rcases family_descends (prefixWord ++ tailWord_7927664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7927697 : List Nat := [1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 3]
def baseStart_7927697 : Nat := 118140960795 + 7927697 * 2 ^ 59
def prefixEnd_7927697 : Nat := 4983230072969 + 3 ^ 40 * 7927697 * 2
def baseEnd_7927697 : Nat := 4070719044206774582728691

theorem tailTrace_7927697 : CollatzResearch.WordTrace tailWord_7927697 prefixEnd_7927697 4070719044206774582728691 := by
  unfold tailWord_7927697
  simp only [CollatzResearch.WordTrace]
  refine ⟨289146863960315186699813345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192764575973543457799875563 289146863960315186699813345)
  ·
    refine ⟨216860147970236390024860009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 289146863960315186699813345 216860147970236390024860009)
    ·
      refine ⟨162645110977677292518645007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216860147970236390024860009 162645110977677292518645007)
      ·
        refine ⟨243967666466515938777967511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162645110977677292518645007 243967666466515938777967511)
        ·
          refine ⟨365951499699773908166951267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 243967666466515938777967511 365951499699773908166951267)
          ·
            refine ⟨548927249549660862250426901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 365951499699773908166951267 548927249549660862250426901)
            ·
              refine ⟨25730964822640352917988761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 548927249549660862250426901 25730964822640352917988761)
              ·
                refine ⟨19298223616980264688491571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25730964822640352917988761 19298223616980264688491571)
                ·
                  refine ⟨28947335425470397032737357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19298223616980264688491571 28947335425470397032737357)
                  ·
                    refine ⟨10855250784551398887276509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28947335425470397032737357 10855250784551398887276509)
                    ·
                      refine ⟨4070719044206774582728691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10855250784551398887276509 4070719044206774582728691)
                      ·
                        rfl

theorem cell23_7927697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 3].length) (baseStart_7927697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7927697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7927697 prefixEnd_7927697 := by exact prefixLift 7927697
  have htrace : WordTrace (prefixWord ++ tailWord_7927697) baseStart_7927697 baseEnd_7927697 := by
    simpa [prefixWord, tailWord_7927697, baseEnd_7927697] using wordTrace_append hprefix tailTrace_7927697
  have hstable : (prefixWord ++ tailWord_7927697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7927697).length < 2 ^ (prefixWord ++ tailWord_7927697).sum := by decide
  have hdescent : baseEnd_7927697 < baseStart_7927697 := by decide
  rcases family_descends (prefixWord ++ tailWord_7927697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7927698 : List Nat := [3, 2, 3, 2, 1, 3, 2, 1, 1, 1, 4]
def baseStart_7927698 : Nat := 118140960795 + 7927698 * 2 ^ 59
def prefixEnd_7927698 : Nat := 4983230072969 + 3 ^ 40 * 7927698 * 2
def baseEnd_7927698 : Nat := 4070719557687429078816187

theorem tailTrace_7927698 : CollatzResearch.WordTrace tailWord_7927698 prefixEnd_7927698 4070719557687429078816187 := by
  unfold tailWord_7927698
  simp only [CollatzResearch.WordTrace]
  refine ⟨72286725108327890967649937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192764600288874375913733165 72286725108327890967649937)
  ·
    refine ⟨54215043831245918225737453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72286725108327890967649937 54215043831245918225737453)
    ·
      refine ⟨20330641436717219334651545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54215043831245918225737453 20330641436717219334651545)
      ·
        refine ⟨15247981077537914500988659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20330641436717219334651545 15247981077537914500988659)
        ·
          refine ⟨22871971616306871751482989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15247981077537914500988659 22871971616306871751482989)
          ·
            refine ⟨8576989356115076906806121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22871971616306871751482989 8576989356115076906806121)
            ·
              refine ⟨6432742017086307680104591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8576989356115076906806121 6432742017086307680104591)
              ·
                refine ⟨9649113025629461520156887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6432742017086307680104591 9649113025629461520156887)
                ·
                  refine ⟨14473669538444192280235331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9649113025629461520156887 14473669538444192280235331)
                  ·
                    refine ⟨21710504307666288420352997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14473669538444192280235331 21710504307666288420352997)
                    ·
                      refine ⟨4070719557687429078816187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21710504307666288420352997 4070719557687429078816187)
                      ·
                        rfl

theorem cell23_7927698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 3, 2, 1, 1, 1, 4].length) (baseStart_7927698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7927698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7927698 prefixEnd_7927698 := by exact prefixLift 7927698
  have htrace : WordTrace (prefixWord ++ tailWord_7927698) baseStart_7927698 baseEnd_7927698 := by
    simpa [prefixWord, tailWord_7927698, baseEnd_7927698] using wordTrace_append hprefix tailTrace_7927698
  have hstable : (prefixWord ++ tailWord_7927698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7927698).length < 2 ^ (prefixWord ++ tailWord_7927698).sum := by decide
  have hdescent : baseEnd_7927698 < baseStart_7927698 := by decide
  rcases family_descends (prefixWord ++ tailWord_7927698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7927731 : List Nat := [1, 1, 1, 2, 3, 1, 7, 1, 2, 1, 3]
def baseStart_7927731 : Nat := 118140960795 + 7927731 * 2 ^ 59
def prefixEnd_7927731 : Nat := 4983230072969 + 3 ^ 40 * 7927731 * 2
def baseEnd_7927731 : Nat := 4070736502549027449703535

theorem tailTrace_7927731 : CollatzResearch.WordTrace tailWord_7927731 prefixEnd_7927731 4070736502549027449703535 := by
  unfold tailWord_7927731
  simp only [CollatzResearch.WordTrace]
  refine ⟨289148104042192010506551047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192765402694794673671034031 289148104042192010506551047)
  ·
    refine ⟨433722156063288015759826571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289148104042192010506551047 433722156063288015759826571)
    ·
      refine ⟨650583234094932023639739857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 433722156063288015759826571 650583234094932023639739857)
      ·
        refine ⟨487937425571199017729804893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 650583234094932023639739857 487937425571199017729804893)
        ·
          refine ⟨182976534589199631648676835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 487937425571199017729804893 182976534589199631648676835)
          ·
            refine ⟨274464801883799447473015253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182976534589199631648676835 274464801883799447473015253)
            ·
              refine ⟨6432768794151549550148795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 274464801883799447473015253 6432768794151549550148795)
              ·
                refine ⟨9649153191227324325223193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6432768794151549550148795 9649153191227324325223193)
                ·
                  refine ⟨7236864893420493243917395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9649153191227324325223193 7236864893420493243917395)
                  ·
                    refine ⟨10855297340130739865876093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7236864893420493243917395 10855297340130739865876093)
                    ·
                      refine ⟨4070736502549027449703535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10855297340130739865876093 4070736502549027449703535)
                      ·
                        rfl

theorem cell23_7927731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 7, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 7, 1, 2, 1, 3].length) (baseStart_7927731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7927731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7927731 prefixEnd_7927731 := by exact prefixLift 7927731
  have htrace : WordTrace (prefixWord ++ tailWord_7927731) baseStart_7927731 baseEnd_7927731 := by
    simpa [prefixWord, tailWord_7927731, baseEnd_7927731] using wordTrace_append hprefix tailTrace_7927731
  have hstable : (prefixWord ++ tailWord_7927731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7927731).length < 2 ^ (prefixWord ++ tailWord_7927731).sum := by decide
  have hdescent : baseEnd_7927731 < baseStart_7927731 := by decide
  rcases family_descends (prefixWord ++ tailWord_7927731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7927741 : List Nat := [1, 4, 1, 2, 3, 1, 1, 4, 1, 3, 2]
def baseStart_7927741 : Nat := 118140960795 + 7927741 * 2 ^ 59
def prefixEnd_7927741 : Nat := 4983230072969 + 3 ^ 40 * 7927741 * 2
def baseEnd_7927741 : Nat := 4070741637355572410578489

theorem tailTrace_7927741 : CollatzResearch.WordTrace tailWord_7927741 prefixEnd_7927741 4070741637355572410578489 := by
  unfold tailWord_7927741
  simp only [CollatzResearch.WordTrace]
  refine ⟨289148468772155782214415077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192765645848103854809610051 289148468772155782214415077)
  ·
    refine ⟨54215337894779209165202827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 289148468772155782214415077 54215337894779209165202827)
    ·
      refine ⟨81323006842168813747804241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54215337894779209165202827 81323006842168813747804241)
      ·
        refine ⟨60992255131626610310853181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81323006842168813747804241 60992255131626610310853181)
        ·
          refine ⟨22872095674359978866569943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60992255131626610310853181 22872095674359978866569943)
          ·
            refine ⟨34308143511539968299854915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22872095674359978866569943 34308143511539968299854915)
            ·
              refine ⟨51462215267309952449782373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34308143511539968299854915 51462215267309952449782373)
              ·
                refine ⟨9649165362620616084334195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51462215267309952449782373 9649165362620616084334195)
                ·
                  refine ⟨14473748043930924126501293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9649165362620616084334195 14473748043930924126501293)
                  ·
                    refine ⟨5427655516474096547437985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14473748043930924126501293 5427655516474096547437985)
                    ·
                      refine ⟨4070741637355572410578489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5427655516474096547437985 4070741637355572410578489)
                      ·
                        rfl

theorem cell23_7927741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 4, 1, 3, 2].length) (baseStart_7927741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7927741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7927741 prefixEnd_7927741 := by exact prefixLift 7927741
  have htrace : WordTrace (prefixWord ++ tailWord_7927741) baseStart_7927741 baseEnd_7927741 := by
    simpa [prefixWord, tailWord_7927741, baseEnd_7927741] using wordTrace_append hprefix tailTrace_7927741
  have hstable : (prefixWord ++ tailWord_7927741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7927741).length < 2 ^ (prefixWord ++ tailWord_7927741).sum := by decide
  have hdescent : baseEnd_7927741 < baseStart_7927741 := by decide
  rcases family_descends (prefixWord ++ tailWord_7927741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7927754 : List Nat := [3, 1, 2, 1, 2, 1, 2, 4, 1, 4, 2]
def baseStart_7927754 : Nat := 118140960795 + 7927754 * 2 ^ 59
def prefixEnd_7927754 : Nat := 4983230072969 + 3 ^ 40 * 7927754 * 2
def baseEnd_7927754 : Nat := 4070748312604080859715929

theorem tailTrace_7927754 : CollatzResearch.WordTrace tailWord_7927754 prefixEnd_7927754 4070748312604080859715929 := by
  unfold tailWord_7927754
  simp only [CollatzResearch.WordTrace]
  refine ⟨72287235730277171358659579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192765961947405790289758877 72287235730277171358659579)
  ·
    refine ⟨108430853595415757037989369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72287235730277171358659579 108430853595415757037989369)
    ·
      refine ⟨81323140196561817778492027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108430853595415757037989369 81323140196561817778492027)
      ·
        refine ⟨121984710294842726667738041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81323140196561817778492027 121984710294842726667738041)
        ·
          refine ⟨91488532721132045000803531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121984710294842726667738041 91488532721132045000803531)
          ·
            refine ⟨137232799081698067501205297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91488532721132045000803531 137232799081698067501205297)
            ·
              refine ⟨102924599311273550625903973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137232799081698067501205297 102924599311273550625903973)
              ·
                refine ⟨19298362370863790742356995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 102924599311273550625903973 19298362370863790742356995)
                ·
                  refine ⟨28947543556295686113535493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19298362370863790742356995 28947543556295686113535493)
                  ·
                    refine ⟨5427664416805441146287905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28947543556295686113535493 5427664416805441146287905)
                    ·
                      refine ⟨4070748312604080859715929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5427664416805441146287905 4070748312604080859715929)
                      ·
                        rfl

theorem cell23_7927754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 4, 1, 4, 2].length) (baseStart_7927754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7927754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7927754 prefixEnd_7927754 := by exact prefixLift 7927754
  have htrace : WordTrace (prefixWord ++ tailWord_7927754) baseStart_7927754 baseEnd_7927754 := by
    simpa [prefixWord, tailWord_7927754, baseEnd_7927754] using wordTrace_append hprefix tailTrace_7927754
  have hstable : (prefixWord ++ tailWord_7927754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7927754).length < 2 ^ (prefixWord ++ tailWord_7927754).sum := by decide
  have hdescent : baseEnd_7927754 < baseStart_7927754 := by decide
  rcases family_descends (prefixWord ++ tailWord_7927754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7927760 : List Nat := [2, 1, 1, 1, 1, 2, 4, 2, 9]
def baseStart_7927760 : Nat := 118140960795 + 7927760 * 2 ^ 59
def prefixEnd_7927760 : Nat := 4983230072969 + 3 ^ 40 * 7927760 * 2
def baseEnd_7927760 : Nat := 452305710387556426248989

theorem tailTrace_7927760 : CollatzResearch.WordTrace tailWord_7927760 prefixEnd_7927760 452305710387556426248989 := by
  unfold tailWord_7927760
  simp only [CollatzResearch.WordTrace]
  refine ⟨144574580879543474229678367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192766107839391298972904489 144574580879543474229678367)
  ·
    refine ⟨216861871319315211344517551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144574580879543474229678367 216861871319315211344517551)
    ·
      refine ⟨325292806978972817016776327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216861871319315211344517551 325292806978972817016776327)
      ·
        refine ⟨487939210468459225525164491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 325292806978972817016776327 487939210468459225525164491)
        ·
          refine ⟨731908815702688838287746737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 487939210468459225525164491 731908815702688838287746737)
          ·
            refine ⟨548931611777016628715810053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 731908815702688838287746737 548931611777016628715810053)
            ·
              refine ⟨102924677208190617884214385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 548931611777016628715810053 102924677208190617884214385)
              ·
                refine ⟨77193507906142963413160789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102924677208190617884214385 77193507906142963413160789)
                ·
                  refine ⟨452305710387556426248989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 77193507906142963413160789 452305710387556426248989)
                  ·
                    rfl

theorem cell23_7927760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 2, 9].length) (baseStart_7927760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7927760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7927760 prefixEnd_7927760 := by exact prefixLift 7927760
  have htrace : WordTrace (prefixWord ++ tailWord_7927760) baseStart_7927760 baseEnd_7927760 := by
    simpa [prefixWord, tailWord_7927760, baseEnd_7927760] using wordTrace_append hprefix tailTrace_7927760
  have hstable : (prefixWord ++ tailWord_7927760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7927760).length < 2 ^ (prefixWord ++ tailWord_7927760).sum := by decide
  have hdescent : baseEnd_7927760 < baseStart_7927760 := by decide
  rcases family_descends (prefixWord ++ tailWord_7927760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7927777 : List Nat := [1, 2, 3, 1, 2, 1, 5, 1, 7]
def baseStart_7927777 : Nat := 118140960795 + 7927777 * 2 ^ 59
def prefixEnd_7927777 : Nat := 4983230072969 + 3 ^ 40 * 7927777 * 2
def baseEnd_7927777 : Nat := 452306680295459363303147

theorem tailTrace_7927777 : CollatzResearch.WordTrace tailWord_7927777 prefixEnd_7927777 452306680295459363303147 := by
  unfold tailWord_7927777
  simp only [CollatzResearch.WordTrace]
  refine ⟨289149781800025360362725585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192766521200016906908483723 289149781800025360362725585)
  ·
    refine ⟨216862336350019020272044189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 289149781800025360362725585 216862336350019020272044189)
    ·
      refine ⟨81323376131257132602016571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 216862336350019020272044189 81323376131257132602016571)
      ·
        refine ⟨121985064196885698903024857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81323376131257132602016571 121985064196885698903024857)
        ·
          refine ⟨91488798147664274177268643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121985064196885698903024857 91488798147664274177268643)
          ·
            refine ⟨137233197221496411265902965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91488798147664274177268643 137233197221496411265902965)
            ·
              refine ⟨12865612239515288556178403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 137233197221496411265902965 12865612239515288556178403)
              ·
                refine ⟨19298418359272932834267605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12865612239515288556178403 19298418359272932834267605)
                ·
                  refine ⟨452306680295459363303147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19298418359272932834267605 452306680295459363303147)
                  ·
                    rfl

theorem cell23_7927777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 5, 1, 7].length) (baseStart_7927777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7927777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7927777 prefixEnd_7927777 := by exact prefixLift 7927777
  have htrace : WordTrace (prefixWord ++ tailWord_7927777) baseStart_7927777 baseEnd_7927777 := by
    simpa [prefixWord, tailWord_7927777, baseEnd_7927777] using wordTrace_append hprefix tailTrace_7927777
  have hstable : (prefixWord ++ tailWord_7927777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7927777).length < 2 ^ (prefixWord ++ tailWord_7927777).sum := by decide
  have hdescent : baseEnd_7927777 < baseStart_7927777 := by decide
  rcases family_descends (prefixWord ++ tailWord_7927777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7927787 : List Nat := [1, 1, 1, 1, 2, 3, 1, 5, 2, 3, 3]
def baseStart_7927787 : Nat := 118140960795 + 7927787 * 2 ^ 59
def prefixEnd_7927787 : Nat := 4983230072969 + 3 ^ 40 * 7927787 * 2
def baseEnd_7927787 : Nat := 4070765257465679230603277

theorem tailTrace_7927787 : CollatzResearch.WordTrace tailWord_7927787 prefixEnd_7927787 4070765257465679230603277 := by
  unfold tailWord_7927787
  simp only [CollatzResearch.WordTrace]
  refine ⟨289150146529989132070589615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192766764353326088047059743 289150146529989132070589615)
  ·
    refine ⟨433725219794983698105884423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289150146529989132070589615 433725219794983698105884423)
    ·
      refine ⟨650587829692475547158826635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 433725219794983698105884423 650587829692475547158826635)
      ·
        refine ⟨975881744538713320738239953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 650587829692475547158826635 975881744538713320738239953)
        ·
          refine ⟨731911308404034990553679965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 975881744538713320738239953 731911308404034990553679965)
          ·
            refine ⟨274466740651513121457629987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 731911308404034990553679965 274466740651513121457629987)
            ·
              refine ⟨411700110977269682186444981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 274466740651513121457629987 411700110977269682186444981)
              ·
                refine ⟨38596885404119032704979217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 411700110977269682186444981 38596885404119032704979217)
                ·
                  refine ⟨28947664053089274528734413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38596885404119032704979217 28947664053089274528734413)
                  ·
                    refine ⟨10855374019908477948275405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28947664053089274528734413 10855374019908477948275405)
                    ·
                      refine ⟨4070765257465679230603277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10855374019908477948275405 4070765257465679230603277)
                      ·
                        rfl

theorem cell23_7927787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 5, 2, 3, 3].length) (baseStart_7927787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7927787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7927787 prefixEnd_7927787 := by exact prefixLift 7927787
  have htrace : WordTrace (prefixWord ++ tailWord_7927787) baseStart_7927787 baseEnd_7927787 := by
    simpa [prefixWord, tailWord_7927787, baseEnd_7927787] using wordTrace_append hprefix tailTrace_7927787
  have hstable : (prefixWord ++ tailWord_7927787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7927787).length < 2 ^ (prefixWord ++ tailWord_7927787).sum := by decide
  have hdescent : baseEnd_7927787 < baseStart_7927787 := by decide
  rcases family_descends (prefixWord ++ tailWord_7927787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7927871 : List Nat := [1, 1, 2, 2, 3, 1, 3, 5, 1, 4]
def baseStart_7927871 : Nat := 118140960795 + 7927871 * 2 ^ 59
def prefixEnd_7927871 : Nat := 4983230072969 + 3 ^ 40 * 7927871 * 2
def baseEnd_7927871 : Nat := 1356936129946885633984297

theorem tailTrace_7927871 : CollatzResearch.WordTrace tailWord_7927871 prefixEnd_7927871 1356936129946885633984297 := by
  unfold tailWord_7927871
  simp only [CollatzResearch.WordTrace]
  refine ⟨289153210261684814416647467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192768806841123209611098311 289153210261684814416647467)
  ·
    refine ⟨433729815392527221624971201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289153210261684814416647467 433729815392527221624971201)
    ·
      refine ⟨325297361544395416218728401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 433729815392527221624971201 325297361544395416218728401)
      ·
        refine ⟨243973021158296562164046301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 325297361544395416218728401 243973021158296562164046301)
        ·
          refine ⟨91489882934361210811517363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 243973021158296562164046301 91489882934361210811517363)
          ·
            refine ⟨137234824401541816217276045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91489882934361210811517363 137234824401541816217276045)
            ·
              refine ⟨51463059150578181081478517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 137234824401541816217276045 51463059150578181081478517)
              ·
                refine ⟨4824661795366704476388611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 51463059150578181081478517 4824661795366704476388611)
                ·
                  refine ⟨7236992693050056714582917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4824661795366704476388611 7236992693050056714582917)
                  ·
                    refine ⟨1356936129946885633984297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7236992693050056714582917 1356936129946885633984297)
                    ·
                      rfl

theorem cell23_7927871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 5, 1, 4].length) (baseStart_7927871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7927871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7927871 prefixEnd_7927871 := by exact prefixLift 7927871
  have htrace : WordTrace (prefixWord ++ tailWord_7927871) baseStart_7927871 baseEnd_7927871 := by
    simpa [prefixWord, tailWord_7927871, baseEnd_7927871] using wordTrace_append hprefix tailTrace_7927871
  have hstable : (prefixWord ++ tailWord_7927871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7927871).length < 2 ^ (prefixWord ++ tailWord_7927871).sum := by decide
  have hdescent : baseEnd_7927871 < baseStart_7927871 := by decide
  rcases family_descends (prefixWord ++ tailWord_7927871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7927878 : List Nat := [6, 1, 1, 1, 1, 1, 1, 1, 4, 4, 2]
def baseStart_7927878 : Nat := 118140960795 + 7927878 * 2 ^ 59
def prefixEnd_7927878 : Nat := 4983230072969 + 3 ^ 40 * 7927878 * 2
def baseEnd_7927878 : Nat := 4070811984205238374565359

theorem tailTrace_7927878 : CollatzResearch.WordTrace tailWord_7927878 prefixEnd_7927878 4070811984205238374565359 := by
  unfold tailWord_7927878
  simp only [CollatzResearch.WordTrace]
  refine ⟨9036045799145607956629759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 192768977048439636408101525 9036045799145607956629759)
  ·
    refine ⟨13554068698718411934944639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9036045799145607956629759 13554068698718411934944639)
    ·
      refine ⟨20331103048077617902416959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13554068698718411934944639 20331103048077617902416959)
      ·
        refine ⟨30496654572116426853625439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20331103048077617902416959 30496654572116426853625439)
        ·
          refine ⟨45744981858174640280438159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30496654572116426853625439 45744981858174640280438159)
          ·
            refine ⟨68617472787261960420657239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45744981858174640280438159 68617472787261960420657239)
            ·
              refine ⟨102926209180892940630985859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68617472787261960420657239 102926209180892940630985859)
              ·
                refine ⟨154389313771339410946478789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102926209180892940630985859 154389313771339410946478789)
                ·
                  refine ⟨28947996332126139552464773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 154389313771339410946478789 28947996332126139552464773)
                  ·
                    refine ⟨5427749312273651166087145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28947996332126139552464773 5427749312273651166087145)
                    ·
                      refine ⟨4070811984205238374565359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5427749312273651166087145 4070811984205238374565359)
                      ·
                        rfl

theorem cell23_7927878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 1, 4, 4, 2].length) (baseStart_7927878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7927878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7927878 prefixEnd_7927878 := by exact prefixLift 7927878
  have htrace : WordTrace (prefixWord ++ tailWord_7927878) baseStart_7927878 baseEnd_7927878 := by
    simpa [prefixWord, tailWord_7927878, baseEnd_7927878] using wordTrace_append hprefix tailTrace_7927878
  have hstable : (prefixWord ++ tailWord_7927878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7927878).length < 2 ^ (prefixWord ++ tailWord_7927878).sum := by decide
  have hdescent : baseEnd_7927878 < baseStart_7927878 := by decide
  rcases family_descends (prefixWord ++ tailWord_7927878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7927884 : List Nat := [2, 2, 1, 3, 1, 1, 5, 2, 6]
def baseStart_7927884 : Nat := 118140960795 + 7927884 * 2 ^ 59
def prefixEnd_7927884 : Nat := 4983230072969 + 3 ^ 40 * 7927884 * 2
def baseEnd_7927884 : Nat := 452312785009907261232259

theorem tailTrace_7927884 : CollatzResearch.WordTrace tailWord_7927884 prefixEnd_7927884 452312785009907261232259 := by
  unfold tailWord_7927884
  simp only [CollatzResearch.WordTrace]
  refine ⟨144576842205318858818435353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192769122940425145091247137 144576842205318858818435353)
  ·
    refine ⟨108432631653989144113826515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144576842205318858818435353 108432631653989144113826515)
    ·
      refine ⟨162648947480983716170739773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108432631653989144113826515 162648947480983716170739773)
      ·
        refine ⟨60993355305368893564027415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 162648947480983716170739773 60993355305368893564027415)
        ·
          refine ⟨91490032958053340346041123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60993355305368893564027415 91490032958053340346041123)
          ·
            refine ⟨137235049437080010519061685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91490032958053340346041123 137235049437080010519061685)
            ·
              refine ⟨12865785884726250986162033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 137235049437080010519061685 12865785884726250986162033)
              ·
                refine ⟨9649339413544688239621525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12865785884726250986162033 9649339413544688239621525)
                ·
                  refine ⟨452312785009907261232259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9649339413544688239621525 452312785009907261232259)
                  ·
                    rfl

theorem cell23_7927884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 5, 2, 6].length) (baseStart_7927884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7927884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7927884 prefixEnd_7927884 := by exact prefixLift 7927884
  have htrace : WordTrace (prefixWord ++ tailWord_7927884) baseStart_7927884 baseEnd_7927884 := by
    simpa [prefixWord, tailWord_7927884, baseEnd_7927884] using wordTrace_append hprefix tailTrace_7927884
  have hstable : (prefixWord ++ tailWord_7927884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7927884).length < 2 ^ (prefixWord ++ tailWord_7927884).sum := by decide
  have hdescent : baseEnd_7927884 < baseStart_7927884 := by decide
  rcases family_descends (prefixWord ++ tailWord_7927884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7927907 : List Nat := [1, 1, 1, 5, 1, 1, 2, 1, 2, 1, 7]
def baseStart_7927907 : Nat := 118140960795 + 7927907 * 2 ^ 59
def prefixEnd_7927907 : Nat := 4983230072969 + 3 ^ 40 * 7927907 * 2
def baseEnd_7927907 : Nat := 4070826875144218761102725

theorem tailTrace_7927907 : CollatzResearch.WordTrace tailWord_7927907 prefixEnd_7927907 4070826875144218761102725 := by
  unfold tailWord_7927907
  simp only [CollatzResearch.WordTrace]
  refine ⟨289154523289554392564957975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192769682193036261709971983 289154523289554392564957975)
  ·
    refine ⟨433731784934331588847436963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289154523289554392564957975 433731784934331588847436963)
    ·
      refine ⟨650597677401497383271155445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 433731784934331588847436963 650597677401497383271155445)
      ·
        refine ⟨60993532256390379681670823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 650597677401497383271155445 60993532256390379681670823)
        ·
          refine ⟨91490298384585569522506235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60993532256390379681670823 91490298384585569522506235)
          ·
            refine ⟨137235447576878354283759353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91490298384585569522506235 137235447576878354283759353)
            ·
              refine ⟨102926585682658765712819515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137235447576878354283759353 102926585682658765712819515)
              ·
                refine ⟨154389878523988148569229273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102926585682658765712819515 154389878523988148569229273)
                ·
                  refine ⟨115792408892991111426921955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 154389878523988148569229273 115792408892991111426921955)
                  ·
                    refine ⟨173688613339486667140382933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 115792408892991111426921955 173688613339486667140382933)
                    ·
                      refine ⟨4070826875144218761102725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 173688613339486667140382933 4070826875144218761102725)
                      ·
                        rfl

theorem cell23_7927907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 1, 2, 1, 7].length) (baseStart_7927907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7927907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7927907 prefixEnd_7927907 := by exact prefixLift 7927907
  have htrace : WordTrace (prefixWord ++ tailWord_7927907) baseStart_7927907 baseEnd_7927907 := by
    simpa [prefixWord, tailWord_7927907, baseEnd_7927907] using wordTrace_append hprefix tailTrace_7927907
  have hstable : (prefixWord ++ tailWord_7927907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7927907).length < 2 ^ (prefixWord ++ tailWord_7927907).sum := by decide
  have hdescent : baseEnd_7927907 < baseStart_7927907 := by decide
  rcases family_descends (prefixWord ++ tailWord_7927907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7927911 : List Nat := [1, 1, 5, 1, 1, 2, 1, 4, 3, 1, 3]
def baseStart_7927911 : Nat := 118140960795 + 7927911 * 2 ^ 59
def prefixEnd_7927911 : Nat := 4983230072969 + 3 ^ 40 * 7927911 * 2
def baseEnd_7927911 : Nat := 4070828929066836745452707

theorem tailTrace_7927911 : CollatzResearch.WordTrace tailWord_7927911 prefixEnd_7927911 4070828929066836745452707 := by
  unfold tailWord_7927911
  simp only [CollatzResearch.WordTrace]
  refine ⟨289154669181539901248103587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192769779454359934165402391 289154669181539901248103587)
  ·
    refine ⟨433732003772309851872155381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289154669181539901248103587 433732003772309851872155381)
    ·
      refine ⟨40662375353654048613014567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 433732003772309851872155381 40662375353654048613014567)
      ·
        refine ⟨60993563030481072919521851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40662375353654048613014567 60993563030481072919521851)
        ·
          refine ⟨91490344545721609379282777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60993563030481072919521851 91490344545721609379282777)
          ·
            refine ⟨68617758409291207034462083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91490344545721609379282777 68617758409291207034462083)
            ·
              refine ⟨102926637613936810551693125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68617758409291207034462083 102926637613936810551693125)
              ·
                refine ⟨19298744552613151978442461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 102926637613936810551693125 19298744552613151978442461)
                ·
                  refine ⟨7237029207229931991915923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19298744552613151978442461 7237029207229931991915923)
                  ·
                    refine ⟨10855543810844897987873885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7237029207229931991915923 10855543810844897987873885)
                    ·
                      refine ⟨4070828929066836745452707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10855543810844897987873885 4070828929066836745452707)
                      ·
                        rfl

theorem cell23_7927911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 4, 3, 1, 3].length) (baseStart_7927911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7927911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7927911 prefixEnd_7927911 := by exact prefixLift 7927911
  have htrace : WordTrace (prefixWord ++ tailWord_7927911) baseStart_7927911 baseEnd_7927911 := by
    simpa [prefixWord, tailWord_7927911, baseEnd_7927911] using wordTrace_append hprefix tailTrace_7927911
  have hstable : (prefixWord ++ tailWord_7927911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7927911).length < 2 ^ (prefixWord ++ tailWord_7927911).sum := by decide
  have hdescent : baseEnd_7927911 < baseStart_7927911 := by decide
  rcases family_descends (prefixWord ++ tailWord_7927911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7927921 : List Nat := [1, 2, 2, 2, 1, 1, 4, 3, 2, 3, 2]
def baseStart_7927921 : Nat := 118140960795 + 7927921 * 2 ^ 59
def prefixEnd_7927921 : Nat := 4983230072969 + 3 ^ 40 * 7927921 * 2
def baseEnd_7927921 : Nat := 4070834063873381706327661

theorem tailTrace_7927921 : CollatzResearch.WordTrace tailWord_7927921 prefixEnd_7927921 4070834063873381706327661 := by
  unfold tailWord_7927921
  simp only [CollatzResearch.WordTrace]
  refine ⟨289155033911503672955967617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192770022607669115303978411 289155033911503672955967617)
  ·
    refine ⟨216866275433627754716975713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 289155033911503672955967617 216866275433627754716975713)
    ·
      refine ⟨162649706575220816037731785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216866275433627754716975713 162649706575220816037731785)
      ·
        refine ⟨121987279931415612028298839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162649706575220816037731785 121987279931415612028298839)
        ·
          refine ⟨182980919897123418042448259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121987279931415612028298839 182980919897123418042448259)
          ·
            refine ⟨274471379845685127063672389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182980919897123418042448259 274471379845685127063672389)
            ·
              refine ⟨51463383721065961324438573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 274471379845685127063672389 51463383721065961324438573)
              ·
                refine ⟨19298768895399735496664465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51463383721065961324438573 19298768895399735496664465)
                ·
                  refine ⟨14474076671549801622498349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19298768895399735496664465 14474076671549801622498349)
                  ·
                    refine ⟨5427778751831175608436881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14474076671549801622498349 5427778751831175608436881)
                    ·
                      refine ⟨4070834063873381706327661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5427778751831175608436881 4070834063873381706327661)
                      ·
                        rfl

theorem cell23_7927921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 3, 2, 3, 2].length) (baseStart_7927921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7927921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7927921 prefixEnd_7927921 := by exact prefixLift 7927921
  have htrace : WordTrace (prefixWord ++ tailWord_7927921) baseStart_7927921 baseEnd_7927921 := by
    simpa [prefixWord, tailWord_7927921, baseEnd_7927921] using wordTrace_append hprefix tailTrace_7927921
  have hstable : (prefixWord ++ tailWord_7927921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7927921).length < 2 ^ (prefixWord ++ tailWord_7927921).sum := by decide
  have hdescent : baseEnd_7927921 < baseStart_7927921 := by decide
  rcases family_descends (prefixWord ++ tailWord_7927921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7927945 : List Nat := [1, 2, 1, 1, 4, 2, 5, 2, 1, 1, 3]
def baseStart_7927945 : Nat := 118140960795 + 7927945 * 2 ^ 59
def prefixEnd_7927945 : Nat := 4983230072969 + 3 ^ 40 * 7927945 * 2
def baseEnd_7927945 : Nat := 4070846387409089612427551

theorem tailTrace_7927945 : CollatzResearch.WordTrace tailWord_7927945 prefixEnd_7927945 4070846387409089612427551 := by
  unfold tailWord_7927945
  simp only [CollatzResearch.WordTrace]
  refine ⟨289155909263416725054841289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192770606175611150036560859 289155909263416725054841289)
  ·
    refine ⟨216866931947562543791130967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 289155909263416725054841289 216866931947562543791130967)
    ·
      refine ⟨325300397921343815686696451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216866931947562543791130967 325300397921343815686696451)
      ·
        refine ⟨487950596882015723530044677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 325300397921343815686696451 487950596882015723530044677)
        ·
          refine ⟨91490736915377948161883377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 487950596882015723530044677 91490736915377948161883377)
          ·
            refine ⟨68618052686533461121412533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91490736915377948161883377 68618052686533461121412533)
            ·
              refine ⟨6432942439362511980132425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 68618052686533461121412533 6432942439362511980132425)
              ·
                refine ⟨4824706829521883985099319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6432942439362511980132425 4824706829521883985099319)
                ·
                  refine ⟨7237060244282825977648979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4824706829521883985099319 7237060244282825977648979)
                  ·
                    refine ⟨10855590366424238966473469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7237060244282825977648979 10855590366424238966473469)
                    ·
                      refine ⟨4070846387409089612427551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10855590366424238966473469 4070846387409089612427551)
                      ·
                        rfl

theorem cell23_7927945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 5, 2, 1, 1, 3].length) (baseStart_7927945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7927945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7927945 prefixEnd_7927945 := by exact prefixLift 7927945
  have htrace : WordTrace (prefixWord ++ tailWord_7927945) baseStart_7927945 baseEnd_7927945 := by
    simpa [prefixWord, tailWord_7927945, baseEnd_7927945] using wordTrace_append hprefix tailTrace_7927945
  have hstable : (prefixWord ++ tailWord_7927945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7927945).length < 2 ^ (prefixWord ++ tailWord_7927945).sum := by decide
  have hdescent : baseEnd_7927945 < baseStart_7927945 := by decide
  rcases family_descends (prefixWord ++ tailWord_7927945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7927964 : List Nat := [2, 2, 3, 2, 1, 1, 1, 3, 1, 1, 6]
def baseStart_7927964 : Nat := 118140960795 + 7927964 * 2 ^ 59
def prefixEnd_7927964 : Nat := 4983230072969 + 3 ^ 40 * 7927964 * 2
def baseEnd_7927964 : Nat := 4070856143541525038089963

theorem tailTrace_7927964 : CollatzResearch.WordTrace tailWord_7927964 prefixEnd_7927964 4070856143541525038089963 := by
  unfold tailWord_7927964
  simp only [CollatzResearch.WordTrace]
  refine ⟨144578301125173945649891473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192771068166898594199855297 144578301125173945649891473)
  ·
    refine ⟨108433725843880459237418605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144578301125173945649891473 108433725843880459237418605)
    ·
      refine ⟨40662647191455172214031977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108433725843880459237418605 40662647191455172214031977)
      ·
        refine ⟨30496985393591379160523983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40662647191455172214031977 30496985393591379160523983)
        ·
          refine ⟨45745478090387068740785975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30496985393591379160523983 45745478090387068740785975)
          ·
            refine ⟨68618217135580603111178963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45745478090387068740785975 68618217135580603111178963)
            ·
              refine ⟨102927325703370904666768445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68618217135580603111178963 102927325703370904666768445)
              ·
                refine ⟨38597747138764089250038167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 102927325703370904666768445 38597747138764089250038167)
                ·
                  refine ⟨57896620708146133875057251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38597747138764089250038167 57896620708146133875057251)
                  ·
                    refine ⟨86844931062219200812585877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 57896620708146133875057251 86844931062219200812585877)
                    ·
                      refine ⟨4070856143541525038089963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 86844931062219200812585877 4070856143541525038089963)
                      ·
                        rfl

theorem cell23_7927964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 3, 1, 1, 6].length) (baseStart_7927964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7927964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7927964 prefixEnd_7927964 := by exact prefixLift 7927964
  have htrace : WordTrace (prefixWord ++ tailWord_7927964) baseStart_7927964 baseEnd_7927964 := by
    simpa [prefixWord, tailWord_7927964, baseEnd_7927964] using wordTrace_append hprefix tailTrace_7927964
  have hstable : (prefixWord ++ tailWord_7927964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7927964).length < 2 ^ (prefixWord ++ tailWord_7927964).sum := by decide
  have hdescent : baseEnd_7927964 < baseStart_7927964 := by decide
  rcases family_descends (prefixWord ++ tailWord_7927964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7927968 : List Nat := [2, 1, 1, 4, 2, 4, 1, 2, 1, 1, 4]
def baseStart_7927968 : Nat := 118140960795 + 7927968 * 2 ^ 59
def prefixEnd_7927968 : Nat := 4983230072969 + 3 ^ 40 * 7927968 * 2
def baseEnd_7927968 : Nat := 4070858197464143022439945

theorem tailTrace_7927968 : CollatzResearch.WordTrace tailWord_7927968 prefixEnd_7927968 4070858197464143022439945 := by
  unfold tailWord_7927968
  simp only [CollatzResearch.WordTrace]
  refine ⟨144578374071166699991464279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192771165428222266655285705 144578374071166699991464279)
  ·
    refine ⟨216867561106750049987196419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144578374071166699991464279 216867561106750049987196419)
    ·
      refine ⟨325301341660125074980794629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216867561106750049987196419 325301341660125074980794629)
      ·
        refine ⟨60994001561273451558898993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 325301341660125074980794629 60994001561273451558898993)
        ·
          refine ⟨45745501170955088669174245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60994001561273451558898993 45745501170955088669174245)
          ·
            refine ⟨8577281469554079125470171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45745501170955088669174245 8577281469554079125470171)
            ·
              refine ⟨12865922204331118688205257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8577281469554079125470171 12865922204331118688205257)
              ·
                refine ⟨9649441653248339016153943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12865922204331118688205257 9649441653248339016153943)
                ·
                  refine ⟨14474162479872508524230915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9649441653248339016153943 14474162479872508524230915)
                  ·
                    refine ⟨21711243719808762786346373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14474162479872508524230915 21711243719808762786346373)
                    ·
                      refine ⟨4070858197464143022439945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21711243719808762786346373 4070858197464143022439945)
                      ·
                        rfl

theorem cell23_7927968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 4, 1, 2, 1, 1, 4].length) (baseStart_7927968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7927968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7927968 prefixEnd_7927968 := by exact prefixLift 7927968
  have htrace : WordTrace (prefixWord ++ tailWord_7927968) baseStart_7927968 baseEnd_7927968 := by
    simpa [prefixWord, tailWord_7927968, baseEnd_7927968] using wordTrace_append hprefix tailTrace_7927968
  have hstable : (prefixWord ++ tailWord_7927968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7927968).length < 2 ^ (prefixWord ++ tailWord_7927968).sum := by decide
  have hdescent : baseEnd_7927968 < baseStart_7927968 := by decide
  rcases family_descends (prefixWord ++ tailWord_7927968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7927978 : List Nat := [3, 1, 5, 1, 2, 1, 1, 2, 1, 6]
def baseStart_7927978 : Nat := 118140960795 + 7927978 * 2 ^ 59
def prefixEnd_7927978 : Nat := 4983230072969 + 3 ^ 40 * 7927978 * 2
def baseEnd_7927978 : Nat := 1356954444090229327771633

theorem tailTrace_7927978 : CollatzResearch.WordTrace tailWord_7927978 prefixEnd_7927978 1356954444090229327771633 := by
  unfold tailWord_7927978
  simp only [CollatzResearch.WordTrace]
  refine ⟨72289278218074292922698147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192771408581531447793861725 72289278218074292922698147)
  ·
    refine ⟨108433917327111439384047221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72289278218074292922698147 108433917327111439384047221)
    ·
      refine ⟨10165679749416697442254427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 108433917327111439384047221 10165679749416697442254427)
      ·
        refine ⟨15248519624125046163381641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10165679749416697442254427 15248519624125046163381641)
        ·
          refine ⟨11436389718093784622536231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15248519624125046163381641 11436389718093784622536231)
          ·
            refine ⟨17154584577140676933804347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11436389718093784622536231 17154584577140676933804347)
            ·
              refine ⟨25731876865711015400706521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17154584577140676933804347 25731876865711015400706521)
              ·
                refine ⟨19298907649283261550529891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25731876865711015400706521 19298907649283261550529891)
                ·
                  refine ⟨28948361473924892325794837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19298907649283261550529891 28948361473924892325794837)
                  ·
                    refine ⟨1356954444090229327771633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28948361473924892325794837 1356954444090229327771633)
                    ·
                      rfl

theorem cell23_7927978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 1, 2, 1, 6].length) (baseStart_7927978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7927978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7927978 prefixEnd_7927978 := by exact prefixLift 7927978
  have htrace : WordTrace (prefixWord ++ tailWord_7927978) baseStart_7927978 baseEnd_7927978 := by
    simpa [prefixWord, tailWord_7927978, baseEnd_7927978] using wordTrace_append hprefix tailTrace_7927978
  have hstable : (prefixWord ++ tailWord_7927978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7927978).length < 2 ^ (prefixWord ++ tailWord_7927978).sum := by decide
  have hdescent : baseEnd_7927978 < baseStart_7927978 := by decide
  rcases family_descends (prefixWord ++ tailWord_7927978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7927981 : List Nat := [1, 5, 2, 1, 2, 1, 1, 1, 3, 2, 4]
def baseStart_7927981 : Nat := 118140960795 + 7927981 * 2 ^ 59
def prefixEnd_7927981 : Nat := 4983230072969 + 3 ^ 40 * 7927981 * 2
def baseEnd_7927981 : Nat := 4070864872712651471577385

theorem tailTrace_7927981 : CollatzResearch.WordTrace tailWord_7927981 prefixEnd_7927981 4070864872712651471577385 := by
  unfold tailWord_7927981
  simp only [CollatzResearch.WordTrace]
  refine ⟨289157222291286303203151797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192771481527524202135434531 289157222291286303203151797)
  ·
    refine ⟨27108489589808090925295481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 289157222291286303203151797 27108489589808090925295481)
    ·
      refine ⟨20331367192356068193971611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27108489589808090925295481 20331367192356068193971611)
      ·
        refine ⟨30497050788534102290957417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20331367192356068193971611 30497050788534102290957417)
        ·
          refine ⟨22872788091400576718218063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30497050788534102290957417 22872788091400576718218063)
          ·
            refine ⟨34309182137100865077327095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22872788091400576718218063 34309182137100865077327095)
            ·
              refine ⟨51463773205651297615990643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34309182137100865077327095 51463773205651297615990643)
              ·
                refine ⟨77195659808476946423985965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51463773205651297615990643 77195659808476946423985965)
                ·
                  refine ⟨28948372428178854908994737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77195659808476946423985965 28948372428178854908994737)
                  ·
                    refine ⟨21711279321134141181746053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28948372428178854908994737 21711279321134141181746053)
                    ·
                      refine ⟨4070864872712651471577385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21711279321134141181746053 4070864872712651471577385)
                      ·
                        rfl

theorem cell23_7927981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 1, 3, 2, 4].length) (baseStart_7927981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7927981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7927981 prefixEnd_7927981 := by exact prefixLift 7927981
  have htrace : WordTrace (prefixWord ++ tailWord_7927981) baseStart_7927981 baseEnd_7927981 := by
    simpa [prefixWord, tailWord_7927981, baseEnd_7927981] using wordTrace_append hprefix tailTrace_7927981
  have hstable : (prefixWord ++ tailWord_7927981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7927981).length < 2 ^ (prefixWord ++ tailWord_7927981).sum := by decide
  have hdescent : baseEnd_7927981 < baseStart_7927981 := by decide
  rcases family_descends (prefixWord ++ tailWord_7927981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7927982 : List Nat := [4, 1, 4, 2, 1, 1, 3, 1, 1, 5]
def baseStart_7927982 : Nat := 118140960795 + 7927982 * 2 ^ 59
def prefixEnd_7927982 : Nat := 4983230072969 + 3 ^ 40 * 7927982 * 2
def baseEnd_7927982 : Nat := 1356955128731101989221627

theorem tailTrace_7927982 : CollatzResearch.WordTrace tailWord_7927982 prefixEnd_7927982 1356955128731101989221627 := by
  unfold tailWord_7927982
  simp only [CollatzResearch.WordTrace]
  refine ⟨36144657345535335046742275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 192771505842855120249292133 36144657345535335046742275)
  ·
    refine ⟨54216986018303002570113413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36144657345535335046742275 54216986018303002570113413)
    ·
      refine ⟨10165684878431812981896265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54216986018303002570113413 10165684878431812981896265)
      ·
        refine ⟨7624263658823859736422199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10165684878431812981896265 7624263658823859736422199)
        ·
          refine ⟨11436395488235789604633299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7624263658823859736422199 11436395488235789604633299)
          ·
            refine ⟨17154593232353684406949949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11436395488235789604633299 17154593232353684406949949)
            ·
              refine ⟨6432972462132631652606231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17154593232353684406949949 6432972462132631652606231)
              ·
                refine ⟨9649458693198947478909347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6432972462132631652606231 9649458693198947478909347)
                ·
                  refine ⟨14474188039798421218364021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9649458693198947478909347 14474188039798421218364021)
                  ·
                    refine ⟨1356955128731101989221627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14474188039798421218364021 1356955128731101989221627)
                    ·
                      rfl

theorem cell23_7927982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 3, 1, 1, 5].length) (baseStart_7927982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7927982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7927982 prefixEnd_7927982 := by exact prefixLift 7927982
  have htrace : WordTrace (prefixWord ++ tailWord_7927982) baseStart_7927982 baseEnd_7927982 := by
    simpa [prefixWord, tailWord_7927982, baseEnd_7927982] using wordTrace_append hprefix tailTrace_7927982
  have hstable : (prefixWord ++ tailWord_7927982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7927982).length < 2 ^ (prefixWord ++ tailWord_7927982).sum := by decide
  have hdescent : baseEnd_7927982 < baseStart_7927982 := by decide
  rcases family_descends (prefixWord ++ tailWord_7927982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7927985 : List Nat := [1, 2, 2, 5, 2, 1, 3, 1, 1, 1, 4]
def baseStart_7927985 : Nat := 118140960795 + 7927985 * 2 ^ 59
def prefixEnd_7927985 : Nat := 4983230072969 + 3 ^ 40 * 7927985 * 2
def baseEnd_7927985 : Nat := 4070866926635269455927367

theorem tailTrace_7927985 : CollatzResearch.WordTrace tailWord_7927985 prefixEnd_7927985 4070866926635269455927367 := by
  unfold tailWord_7927985
  simp only [CollatzResearch.WordTrace]
  refine ⟨289157368183271811886297409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192771578788847874590864939 289157368183271811886297409)
  ·
    refine ⟨216868026137453858914723057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 289157368183271811886297409 216868026137453858914723057)
    ·
      refine ⟨162651019603090394186042293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216868026137453858914723057 162651019603090394186042293)
      ·
        refine ⟨15248533087789724454941465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 162651019603090394186042293 15248533087789724454941465)
        ·
          refine ⟨11436399815842293341206099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15248533087789724454941465 11436399815842293341206099)
          ·
            refine ⟨17154599723763440011809149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11436399815842293341206099 17154599723763440011809149)
            ·
              refine ⟨6432974896411290004428431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17154599723763440011809149 6432974896411290004428431)
              ·
                refine ⟨9649462344616935006642647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6432974896411290004428431 9649462344616935006642647)
                ·
                  refine ⟨14474193516925402509963971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9649462344616935006642647 14474193516925402509963971)
                  ·
                    refine ⟨21711290275388103764945957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14474193516925402509963971 21711290275388103764945957)
                    ·
                      refine ⟨4070866926635269455927367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21711290275388103764945957 4070866926635269455927367)
                      ·
                        rfl

theorem cell23_7927985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 3, 1, 1, 1, 4].length) (baseStart_7927985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7927985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7927985 prefixEnd_7927985 := by exact prefixLift 7927985
  have htrace : WordTrace (prefixWord ++ tailWord_7927985) baseStart_7927985 baseEnd_7927985 := by
    simpa [prefixWord, tailWord_7927985, baseEnd_7927985] using wordTrace_append hprefix tailTrace_7927985
  have hstable : (prefixWord ++ tailWord_7927985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7927985).length < 2 ^ (prefixWord ++ tailWord_7927985).sum := by decide
  have hdescent : baseEnd_7927985 < baseStart_7927985 := by decide
  rcases family_descends (prefixWord ++ tailWord_7927985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7928011 : List Nat := [1, 1, 1, 1, 3, 2, 3, 1, 5, 3, 2]
def baseStart_7928011 : Nat := 118140960795 + 7928011 * 2 ^ 59
def prefixEnd_7928011 : Nat := 4983230072969 + 3 ^ 40 * 7928011 * 2
def baseEnd_7928011 : Nat := 4070880277132286354202247

theorem tailTrace_7928011 : CollatzResearch.WordTrace tailWord_7928011 prefixEnd_7928011 4070880277132286354202247 := by
  unfold tailWord_7928011
  simp only [CollatzResearch.WordTrace]
  refine ⟨289158316481177618326743887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192772210987451745551162591 289158316481177618326743887)
  ·
    refine ⟨433737474721766427490115831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289158316481177618326743887 433737474721766427490115831)
    ·
      refine ⟨650606212082649641235173747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 433737474721766427490115831 650606212082649641235173747)
      ·
        refine ⟨975909318123974461852760621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 650606212082649641235173747 975909318123974461852760621)
        ·
          refine ⟨365965994296490423194785233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 975909318123974461852760621 365965994296490423194785233)
          ·
            refine ⟨274474495722367817396088925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 365965994296490423194785233 274474495722367817396088925)
            ·
              refine ⟨102927935895887931523533347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 274474495722367817396088925 102927935895887931523533347)
              ·
                refine ⟨154391903843831897285300021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102927935895887931523533347 154391903843831897285300021)
                ·
                  refine ⟨14474240985359240370496877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 154391903843831897285300021 14474240985359240370496877)
                  ·
                    refine ⟨5427840369509715138936329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14474240985359240370496877 5427840369509715138936329)
                    ·
                      refine ⟨4070880277132286354202247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5427840369509715138936329 4070880277132286354202247)
                      ·
                        rfl

theorem cell23_7928011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 1, 5, 3, 2].length) (baseStart_7928011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7928011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7928011 prefixEnd_7928011 := by exact prefixLift 7928011
  have htrace : WordTrace (prefixWord ++ tailWord_7928011) baseStart_7928011 baseEnd_7928011 := by
    simpa [prefixWord, tailWord_7928011, baseEnd_7928011] using wordTrace_append hprefix tailTrace_7928011
  have hstable : (prefixWord ++ tailWord_7928011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7928011).length < 2 ^ (prefixWord ++ tailWord_7928011).sum := by decide
  have hdescent : baseEnd_7928011 < baseStart_7928011 := by decide
  rcases family_descends (prefixWord ++ tailWord_7928011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7928018 : List Nat := [3, 2, 2, 2, 1, 3, 2, 1, 1, 3, 3]
def baseStart_7928018 : Nat := 118140960795 + 7928018 * 2 ^ 59
def prefixEnd_7928018 : Nat := 4983230072969 + 3 ^ 40 * 7928018 * 2
def baseEnd_7928018 : Nat := 4070883871496867826814715

theorem tailTrace_7928018 : CollatzResearch.WordTrace tailWord_7928018 prefixEnd_7928018 4070883871496867826814715 := by
  unfold tailWord_7928018
  simp only [CollatzResearch.WordTrace]
  refine ⟨72289642948038064630562177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192772381194768172348165805 72289642948038064630562177)
  ·
    refine ⟨54217232211028548472921633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72289642948038064630562177 54217232211028548472921633)
    ·
      refine ⟨40662924158271411354691225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54217232211028548472921633 40662924158271411354691225)
      ·
        refine ⟨30497193118703558516018419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40662924158271411354691225 30497193118703558516018419)
        ·
          refine ⟨45745789678055337774027629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30497193118703558516018419 45745789678055337774027629)
          ·
            refine ⟨17154671129270751665260361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45745789678055337774027629 17154671129270751665260361)
            ·
              refine ⟨12866003346953063748945271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17154671129270751665260361 12866003346953063748945271)
              ·
                refine ⟨19299005020429595623417907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12866003346953063748945271 19299005020429595623417907)
                ·
                  refine ⟨28948507530644393435126861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19299005020429595623417907 28948507530644393435126861)
                  ·
                    refine ⟨10855690323991647538172573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28948507530644393435126861 10855690323991647538172573)
                    ·
                      refine ⟨4070883871496867826814715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10855690323991647538172573 4070883871496867826814715)
                      ·
                        rfl

theorem cell23_7928018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 2, 1, 1, 3, 3].length) (baseStart_7928018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7928018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7928018 prefixEnd_7928018 := by exact prefixLift 7928018
  have htrace : WordTrace (prefixWord ++ tailWord_7928018) baseStart_7928018 baseEnd_7928018 := by
    simpa [prefixWord, tailWord_7928018, baseEnd_7928018] using wordTrace_append hprefix tailTrace_7928018
  have hstable : (prefixWord ++ tailWord_7928018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7928018).length < 2 ^ (prefixWord ++ tailWord_7928018).sum := by decide
  have hdescent : baseEnd_7928018 < baseStart_7928018 := by decide
  rcases family_descends (prefixWord ++ tailWord_7928018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7928044 : List Nat := [2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 5]
def baseStart_7928044 : Nat := 118140960795 + 7928044 * 2 ^ 59
def prefixEnd_7928044 : Nat := 4983230072969 + 3 ^ 40 * 7928044 * 2
def baseEnd_7928044 : Nat := 4070897221993884725089595

theorem tailTrace_7928044 : CollatzResearch.WordTrace tailWord_7928044 prefixEnd_7928044 4070897221993884725089595 := by
  unfold tailWord_7928044
  simp only [CollatzResearch.WordTrace]
  refine ⟨144579760045029032481347593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192773013393372043308463457 144579760045029032481347593)
  ·
    refine ⟨108434820033771774361010695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144579760045029032481347593 108434820033771774361010695)
    ·
      refine ⟨162652230050657661541516043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108434820033771774361010695 162652230050657661541516043)
      ·
        refine ⟨243978345075986492312274065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162652230050657661541516043 243978345075986492312274065)
        ·
          refine ⟨182983758806989869234205549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 243978345075986492312274065 182983758806989869234205549)
          ·
            refine ⟨68618909552621200962827081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 182983758806989869234205549 68618909552621200962827081)
            ·
              refine ⟨51464182164465900722120311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68618909552621200962827081 51464182164465900722120311)
              ·
                refine ⟨77196273246698851083180467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51464182164465900722120311 77196273246698851083180467)
                ·
                  refine ⟨115794409870048276624770701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77196273246698851083180467 115794409870048276624770701)
                  ·
                    refine ⟨43422903701268103734289013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 115794409870048276624770701 43422903701268103734289013)
                    ·
                      refine ⟨4070897221993884725089595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43422903701268103734289013 4070897221993884725089595)
                      ·
                        rfl

theorem cell23_7928044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 5].length) (baseStart_7928044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7928044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7928044 prefixEnd_7928044 := by exact prefixLift 7928044
  have htrace : WordTrace (prefixWord ++ tailWord_7928044) baseStart_7928044 baseEnd_7928044 := by
    simpa [prefixWord, tailWord_7928044, baseEnd_7928044] using wordTrace_append hprefix tailTrace_7928044
  have hstable : (prefixWord ++ tailWord_7928044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7928044).length < 2 ^ (prefixWord ++ tailWord_7928044).sum := by decide
  have hdescent : baseEnd_7928044 < baseStart_7928044 := by decide
  rcases family_descends (prefixWord ++ tailWord_7928044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7928064 : List Nat := [2, 1, 1, 2, 1, 1, 5, 3, 7]
def baseStart_7928064 : Nat := 118140960795 + 7928064 * 2 ^ 59
def prefixEnd_7928064 : Nat := 4983230072969 + 3 ^ 40 * 7928064 * 2
def baseEnd_7928064 : Nat := 452323054622997182982167

theorem tailTrace_7928064 : CollatzResearch.WordTrace tailWord_7928064 prefixEnd_7928064 452323054622997182982167 := by
  unfold tailWord_7928064
  simp only [CollatzResearch.WordTrace]
  refine ⟨144580124774992804189211623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192773499699990405585615497 144580124774992804189211623)
  ·
    refine ⟨216870187162489206283817435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144580124774992804189211623 216870187162489206283817435)
    ·
      refine ⟨325305280743733809425726153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216870187162489206283817435 325305280743733809425726153)
      ·
        refine ⟨243978960557800357069294615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 325305280743733809425726153 243978960557800357069294615)
        ·
          refine ⟨365968440836700535603941923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 243978960557800357069294615 365968440836700535603941923)
          ·
            refine ⟨548952661255050803405912885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 365968440836700535603941923 548952661255050803405912885)
            ·
              refine ⟨51464311992661012819304333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 548952661255050803405912885 51464311992661012819304333)
              ·
                refine ⟨19299116997247879807239125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51464311992661012819304333 19299116997247879807239125)
                ·
                  refine ⟨452323054622997182982167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19299116997247879807239125 452323054622997182982167)
                  ·
                    rfl

theorem cell23_7928064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 3, 7].length) (baseStart_7928064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7928064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7928064 prefixEnd_7928064 := by exact prefixLift 7928064
  have htrace : WordTrace (prefixWord ++ tailWord_7928064) baseStart_7928064 baseEnd_7928064 := by
    simpa [prefixWord, tailWord_7928064, baseEnd_7928064] using wordTrace_append hprefix tailTrace_7928064
  have hstable : (prefixWord ++ tailWord_7928064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7928064).length < 2 ^ (prefixWord ++ tailWord_7928064).sum := by decide
  have hdescent : baseEnd_7928064 < baseStart_7928064 := by decide
  rcases family_descends (prefixWord ++ tailWord_7928064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7928121 : List Nat := [1, 2, 1, 6, 1, 1, 1, 1, 1, 1, 7]
def baseStart_7928121 : Nat := 118140960795 + 7928121 * 2 ^ 59
def prefixEnd_7928121 : Nat := 4983230072969 + 3 ^ 40 * 7928121 * 2
def baseEnd_7928121 : Nat := 4070936760004280923826741

theorem tailTrace_7928121 : CollatzResearch.WordTrace tailWord_7928121 prefixEnd_7928121 4070936760004280923826741 := by
  unfold tailWord_7928121
  simp only [CollatzResearch.WordTrace]
  refine ⟨289162328510779107113248217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192774885673852738075498811 289162328510779107113248217)
  ·
    refine ⟨216871746383084330334936163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 289162328510779107113248217 216871746383084330334936163)
    ·
      refine ⟨325307619574626495502404245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216871746383084330334936163 325307619574626495502404245)
      ·
        refine ⟨15248794667560616976675199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 325307619574626495502404245 15248794667560616976675199)
        ·
          refine ⟨22873192001340925465012799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15248794667560616976675199 22873192001340925465012799)
          ·
            refine ⟨34309788002011388197519199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22873192001340925465012799 34309788002011388197519199)
            ·
              refine ⟨51464682003017082296278799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34309788002011388197519199 51464682003017082296278799)
              ·
                refine ⟨77197023004525623444418199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51464682003017082296278799 77197023004525623444418199)
                ·
                  refine ⟨115795534506788435166627299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77197023004525623444418199 115795534506788435166627299)
                  ·
                    refine ⟨173693301760182652749940949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 115795534506788435166627299 173693301760182652749940949)
                    ·
                      refine ⟨4070936760004280923826741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 173693301760182652749940949 4070936760004280923826741)
                      ·
                        rfl

theorem cell23_7928121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 1, 1, 1, 7].length) (baseStart_7928121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7928121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7928121 prefixEnd_7928121 := by exact prefixLift 7928121
  have htrace : WordTrace (prefixWord ++ tailWord_7928121) baseStart_7928121 baseEnd_7928121 := by
    simpa [prefixWord, tailWord_7928121, baseEnd_7928121] using wordTrace_append hprefix tailTrace_7928121
  have hstable : (prefixWord ++ tailWord_7928121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7928121).length < 2 ^ (prefixWord ++ tailWord_7928121).sum := by decide
  have hdescent : baseEnd_7928121 < baseStart_7928121 := by decide
  rcases family_descends (prefixWord ++ tailWord_7928121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7928148 : List Nat := [2, 4, 1, 1, 2, 2, 1, 3, 2, 1, 4]
def baseStart_7928148 : Nat := 118140960795 + 7928148 * 2 ^ 59
def prefixEnd_7928148 : Nat := 4983230072969 + 3 ^ 40 * 7928148 * 2
def baseEnd_7928148 : Nat := 4070950623981952318189117

theorem tailTrace_7928148 : CollatzResearch.WordTrace tailWord_7928148 prefixEnd_7928148 4070950623981952318189117 := by
  unfold tailWord_7928148
  simp only [CollatzResearch.WordTrace]
  refine ⟨144581656640840645362240549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192775542187787527149654065 144581656640840645362240549)
  ·
    refine ⟨27109060620157621005420103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 144581656640840645362240549 27109060620157621005420103)
    ·
      refine ⟨40663590930236431508130155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27109060620157621005420103 40663590930236431508130155)
      ·
        refine ⟨60995386395354647262195233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40663590930236431508130155 60995386395354647262195233)
        ·
          refine ⟨45746539796515985446646425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60995386395354647262195233 45746539796515985446646425)
          ·
            refine ⟨34309904847386989084984819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45746539796515985446646425 34309904847386989084984819)
            ·
              refine ⟨51464857271080483627477229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34309904847386989084984819 51464857271080483627477229)
              ·
                refine ⟨19299321476655181360303961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51464857271080483627477229 19299321476655181360303961)
                ·
                  refine ⟨14474491107491386020227971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19299321476655181360303961 14474491107491386020227971)
                  ·
                    refine ⟨21711736661237079030341957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14474491107491386020227971 21711736661237079030341957)
                    ·
                      refine ⟨4070950623981952318189117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21711736661237079030341957 4070950623981952318189117)
                      ·
                        rfl

theorem cell23_7928148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 3, 2, 1, 4].length) (baseStart_7928148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7928148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7928148 prefixEnd_7928148 := by exact prefixLift 7928148
  have htrace : WordTrace (prefixWord ++ tailWord_7928148) baseStart_7928148 baseEnd_7928148 := by
    simpa [prefixWord, tailWord_7928148, baseEnd_7928148] using wordTrace_append hprefix tailTrace_7928148
  have hstable : (prefixWord ++ tailWord_7928148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7928148).length < 2 ^ (prefixWord ++ tailWord_7928148).sum := by decide
  have hdescent : baseEnd_7928148 < baseStart_7928148 := by decide
  rcases family_descends (prefixWord ++ tailWord_7928148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7928208 : List Nat := [2, 1, 1, 1, 1, 1, 2, 1, 8, 3, 2]
def baseStart_7928208 : Nat := 118140960795 + 7928208 * 2 ^ 59
def prefixEnd_7928208 : Nat := 4983230072969 + 3 ^ 40 * 7928208 * 2
def baseEnd_7928208 : Nat := 4070981432821222083438841

theorem tailTrace_7928208 : CollatzResearch.WordTrace tailWord_7928208 prefixEnd_7928208 4070981432821222083438841 := by
  unfold tailWord_7928208
  simp only [CollatzResearch.WordTrace]
  refine ⟨144582750830731960485832639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192777001107642613981110185 144582750830731960485832639)
  ·
    refine ⟨216874126246097940728748959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144582750830731960485832639 216874126246097940728748959)
    ·
      refine ⟨325311189369146911093123439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216874126246097940728748959 325311189369146911093123439)
      ·
        refine ⟨487966784053720366639685159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 325311189369146911093123439 487966784053720366639685159)
        ·
          refine ⟨731950176080580549959527739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 487966784053720366639685159 731950176080580549959527739)
          ·
            refine ⟨1097925264120870824939291609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 731950176080580549959527739 1097925264120870824939291609)
            ·
              refine ⟨823443948090653118704468707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1097925264120870824939291609 823443948090653118704468707)
              ·
                refine ⟨1235165922135979678056703061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 823443948090653118704468707 1235165922135979678056703061)
                ·
                  refine ⟨14474600650031011852226989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1235165922135979678056703061 14474600650031011852226989)
                  ·
                    refine ⟨5427975243761629444585121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14474600650031011852226989 5427975243761629444585121)
                    ·
                      refine ⟨4070981432821222083438841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5427975243761629444585121 4070981432821222083438841)
                      ·
                        rfl

theorem cell23_7928208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 8, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 8, 3, 2].length) (baseStart_7928208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7928208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7928208 prefixEnd_7928208 := by exact prefixLift 7928208
  have htrace : WordTrace (prefixWord ++ tailWord_7928208) baseStart_7928208 baseEnd_7928208 := by
    simpa [prefixWord, tailWord_7928208, baseEnd_7928208] using wordTrace_append hprefix tailTrace_7928208
  have hstable : (prefixWord ++ tailWord_7928208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7928208).length < 2 ^ (prefixWord ++ tailWord_7928208).sum := by decide
  have hdescent : baseEnd_7928208 < baseStart_7928208 := by decide
  rcases family_descends (prefixWord ++ tailWord_7928208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7928222 : List Nat := [4, 3, 1, 2, 1, 3, 1, 2, 6]
def baseStart_7928222 : Nat := 118140960795 + 7928222 * 2 ^ 59
def prefixEnd_7928222 : Nat := 4983230072969 + 3 ^ 40 * 7928222 * 2
def baseEnd_7928222 : Nat := 452332069061153892073753

theorem tailTrace_7928222 : CollatzResearch.WordTrace tailWord_7928222 prefixEnd_7928222 452332069061153892073753 := by
  unfold tailWord_7928222
  simp only [CollatzResearch.WordTrace]
  refine ⟨36145751535426650170334365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 192777341522275467575116613 36145751535426650170334365)
  ·
    refine ⟨13554656825784993813875387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36145751535426650170334365 13554656825784993813875387)
    ·
      refine ⟨20331985238677490720813081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13554656825784993813875387 20331985238677490720813081)
      ·
        refine ⟨15248988929008118040609811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20331985238677490720813081 15248988929008118040609811)
        ·
          refine ⟨22873483393512177060914717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15248988929008118040609811 22873483393512177060914717)
          ·
            refine ⟨8577556272567066397843019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22873483393512177060914717 8577556272567066397843019)
            ·
              refine ⟨12866334408850599596764529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8577556272567066397843019 12866334408850599596764529)
              ·
                refine ⟨9649750806637949697573397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12866334408850599596764529 9649750806637949697573397)
                ·
                  refine ⟨452332069061153892073753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9649750806637949697573397 452332069061153892073753)
                  ·
                    rfl

theorem cell23_7928222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 3, 1, 2, 6].length) (baseStart_7928222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7928222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7928222 prefixEnd_7928222 := by exact prefixLift 7928222
  have htrace : WordTrace (prefixWord ++ tailWord_7928222) baseStart_7928222 baseEnd_7928222 := by
    simpa [prefixWord, tailWord_7928222, baseEnd_7928222] using wordTrace_append hprefix tailTrace_7928222
  have hstable : (prefixWord ++ tailWord_7928222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7928222).length < 2 ^ (prefixWord ++ tailWord_7928222).sum := by decide
  have hdescent : baseEnd_7928222 < baseStart_7928222 := by decide
  rcases family_descends (prefixWord ++ tailWord_7928222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7928232 : List Nat := [2, 1, 6, 1, 1, 1, 1, 3, 3, 1, 3]
def baseStart_7928232 : Nat := 118140960795 + 7928232 * 2 ^ 59
def prefixEnd_7928232 : Nat := 4983230072969 + 3 ^ 40 * 7928232 * 2
def baseEnd_7928232 : Nat := 4070993756356929989538731

theorem tailTrace_7928232 : CollatzResearch.WordTrace tailWord_7928232 prefixEnd_7928232 4070993756356929989538731 := by
  unfold tailWord_7928232
  simp only [CollatzResearch.WordTrace]
  refine ⟨144583188506688486535269475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192777584675584648713692633 144583188506688486535269475)
  ·
    refine ⟨216874782760032729802904213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144583188506688486535269475 216874782760032729802904213)
    ·
      refine ⟨10166005441876534209511135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 216874782760032729802904213 10166005441876534209511135)
      ·
        refine ⟨15249008162814801314266703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10166005441876534209511135 15249008162814801314266703)
        ·
          refine ⟨22873512244222201971400055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15249008162814801314266703 22873512244222201971400055)
          ·
            refine ⟨34310268366333302957100083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22873512244222201971400055 34310268366333302957100083)
            ·
              refine ⟨51465402549499954435650125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34310268366333302957100083 51465402549499954435650125)
              ·
                refine ⟨19299525956062482913368797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51465402549499954435650125 19299525956062482913368797)
                ·
                  refine ⟨7237322233523431092513299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19299525956062482913368797 7237322233523431092513299)
                  ·
                    refine ⟨10855983350285146638769949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7237322233523431092513299 10855983350285146638769949)
                    ·
                      refine ⟨4070993756356929989538731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10855983350285146638769949 4070993756356929989538731)
                      ·
                        rfl

theorem cell23_7928232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 3, 3, 1, 3].length) (baseStart_7928232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7928232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7928232 prefixEnd_7928232 := by exact prefixLift 7928232
  have htrace : WordTrace (prefixWord ++ tailWord_7928232) baseStart_7928232 baseEnd_7928232 := by
    simpa [prefixWord, tailWord_7928232, baseEnd_7928232] using wordTrace_append hprefix tailTrace_7928232
  have hstable : (prefixWord ++ tailWord_7928232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7928232).length < 2 ^ (prefixWord ++ tailWord_7928232).sum := by decide
  have hdescent : baseEnd_7928232 < baseStart_7928232 := by decide
  rcases family_descends (prefixWord ++ tailWord_7928232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7928251 : List Nat := [1, 1, 1, 1, 1, 2, 2, 1, 7, 2, 4]
def baseStart_7928251 : Nat := 118140960795 + 7928251 * 2 ^ 59
def prefixEnd_7928251 : Nat := 4983230072969 + 3 ^ 40 * 7928251 * 2
def baseEnd_7928251 : Nat := 4071003512489365415201143

theorem tailTrace_7928251 : CollatzResearch.WordTrace tailWord_7928251 prefixEnd_7928251 4071003512489365415201143 := by
  unfold tailWord_7928251
  simp only [CollatzResearch.WordTrace]
  refine ⟨289167070000308139315480607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192778046666872092876987071 289167070000308139315480607)
  ·
    refine ⟨433750605000462208973220911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289167070000308139315480607 433750605000462208973220911)
    ·
      refine ⟨650625907500693313459831367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 433750605000462208973220911 650625907500693313459831367)
      ·
        refine ⟨975938861251039970189747051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 650625907500693313459831367 975938861251039970189747051)
        ·
          refine ⟨1463908291876559955284620577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 975938861251039970189747051 1463908291876559955284620577)
          ·
            refine ⟨1097931218907419966463465433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1463908291876559955284620577 1097931218907419966463465433)
            ·
              refine ⟨823448414180564974847599075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1097931218907419966463465433 823448414180564974847599075)
              ·
                refine ⟨1235172621270847462271398613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 823448414180564974847599075 1235172621270847462271398613)
                ·
                  refine ⟨28949358311035487396985905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1235172621270847462271398613 28949358311035487396985905)
                  ·
                    refine ⟨21712018733276615547739429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28949358311035487396985905 21712018733276615547739429)
                    ·
                      refine ⟨4071003512489365415201143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21712018733276615547739429 4071003512489365415201143)
                      ·
                        rfl

theorem cell23_7928251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 7, 2, 4].length) (baseStart_7928251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7928251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7928251 prefixEnd_7928251 := by exact prefixLift 7928251
  have htrace : WordTrace (prefixWord ++ tailWord_7928251) baseStart_7928251 baseEnd_7928251 := by
    simpa [prefixWord, tailWord_7928251, baseEnd_7928251] using wordTrace_append hprefix tailTrace_7928251
  have hstable : (prefixWord ++ tailWord_7928251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7928251).length < 2 ^ (prefixWord ++ tailWord_7928251).sum := by decide
  have hdescent : baseEnd_7928251 < baseStart_7928251 := by decide
  rcases family_descends (prefixWord ++ tailWord_7928251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7928326 : List Nat := [6, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5]
def baseStart_7928326 : Nat := 118140960795 + 7928326 * 2 ^ 59
def prefixEnd_7928326 : Nat := 4983230072969 + 3 ^ 40 * 7928326 * 2
def baseEnd_7928326 : Nat := 4071042023538452621763299

theorem tailTrace_7928326 : CollatzResearch.WordTrace tailWord_7928326 prefixEnd_7928326 4071042023538452621763299 := by
  unfold tailWord_7928326
  simp only [CollatzResearch.WordTrace]
  refine ⟨9036556421094888347639401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 192779870316690951416307221 9036556421094888347639401)
  ·
    refine ⟨6777417315821166260729551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9036556421094888347639401 6777417315821166260729551)
    ·
      refine ⟨10166125973731749391094327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6777417315821166260729551 10166125973731749391094327)
      ·
        refine ⟨15249188960597624086641491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10166125973731749391094327 15249188960597624086641491)
        ·
          refine ⟨22873783440896436129962237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15249188960597624086641491 22873783440896436129962237)
          ·
            refine ⟨8577668790336163548735839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22873783440896436129962237 8577668790336163548735839)
            ·
              refine ⟨12866503185504245323103759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8577668790336163548735839 12866503185504245323103759)
              ·
                refine ⟨19299754778256367984655639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12866503185504245323103759 19299754778256367984655639)
                ·
                  refine ⟨28949632167384551976983459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19299754778256367984655639 28949632167384551976983459)
                  ·
                    refine ⟨43424448251076827965475189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28949632167384551976983459 43424448251076827965475189)
                    ·
                      refine ⟨4071042023538452621763299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43424448251076827965475189 4071042023538452621763299)
                      ·
                        rfl

theorem cell23_7928326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5].length) (baseStart_7928326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7928326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7928326 prefixEnd_7928326 := by exact prefixLift 7928326
  have htrace : WordTrace (prefixWord ++ tailWord_7928326) baseStart_7928326 baseEnd_7928326 := by
    simpa [prefixWord, tailWord_7928326, baseEnd_7928326] using wordTrace_append hprefix tailTrace_7928326
  have hstable : (prefixWord ++ tailWord_7928326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7928326).length < 2 ^ (prefixWord ++ tailWord_7928326).sum := by decide
  have hdescent : baseEnd_7928326 < baseStart_7928326 := by decide
  rcases family_descends (prefixWord ++ tailWord_7928326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7928340 : List Nat := [2, 4, 3, 1, 1, 3, 2, 2, 1, 2, 2]
def baseStart_7928340 : Nat := 118140960795 + 7928340 * 2 ^ 59
def prefixEnd_7928340 : Nat := 4983230072969 + 3 ^ 40 * 7928340 * 2
def baseEnd_7928340 : Nat := 4071049212267615566988235

theorem tailTrace_7928340 : CollatzResearch.WordTrace tailWord_7928340 prefixEnd_7928340 4071049212267615566988235 := by
  unfold tailWord_7928340
  simp only [CollatzResearch.WordTrace]
  refine ⟨144585158048492853757735237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192780210731323805010313649 144585158048492853757735237)
  ·
    refine ⟨27109717134092410079575357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 144585158048492853757735237 27109717134092410079575357)
    ·
      refine ⟨10166143925284653779840759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27109717134092410079575357 10166143925284653779840759)
      ·
        refine ⟨15249215887926980669761139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10166143925284653779840759 15249215887926980669761139)
        ·
          refine ⟨22873823831890471004641709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15249215887926980669761139 22873823831890471004641709)
          ·
            refine ⟨8577683936958926626740641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22873823831890471004641709 8577683936958926626740641)
            ·
              refine ⟨6433262952719194970055481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8577683936958926626740641 6433262952719194970055481)
              ·
                refine ⟨4824947214539396227541611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6433262952719194970055481 4824947214539396227541611)
                ·
                  refine ⟨7237420821809094341312417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4824947214539396227541611 7237420821809094341312417)
                  ·
                    refine ⟨5428065616356820755984313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7237420821809094341312417 5428065616356820755984313)
                    ·
                      refine ⟨4071049212267615566988235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5428065616356820755984313 4071049212267615566988235)
                      ·
                        rfl

theorem cell23_7928340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 3, 2, 2, 1, 2, 2].length) (baseStart_7928340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7928340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7928340 prefixEnd_7928340 := by exact prefixLift 7928340
  have htrace : WordTrace (prefixWord ++ tailWord_7928340) baseStart_7928340 baseEnd_7928340 := by
    simpa [prefixWord, tailWord_7928340, baseEnd_7928340] using wordTrace_append hprefix tailTrace_7928340
  have hstable : (prefixWord ++ tailWord_7928340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7928340).length < 2 ^ (prefixWord ++ tailWord_7928340).sum := by decide
  have hdescent : baseEnd_7928340 < baseStart_7928340 := by decide
  rcases family_descends (prefixWord ++ tailWord_7928340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7928362 : List Nat := [3, 1, 4, 1, 1, 2, 1, 3, 1, 4, 2]
def baseStart_7928362 : Nat := 118140960795 + 7928362 * 2 ^ 59
def prefixEnd_7928362 : Nat := 4983230072969 + 3 ^ 40 * 7928362 * 2
def baseEnd_7928362 : Nat := 4071060508842014480913133

theorem tailTrace_7928362 : CollatzResearch.WordTrace tailWord_7928362 prefixEnd_7928362 4071060508842014480913133 := by
  unfold tailWord_7928362
  simp only [CollatzResearch.WordTrace]
  refine ⟨72292779625726501318192835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192780745668604003515180893 72292779625726501318192835)
  ·
    refine ⟨108439169438589751977289253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72292779625726501318192835 108439169438589751977289253)
    ·
      refine ⟨20332344269735578495741735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 108439169438589751977289253 20332344269735578495741735)
      ·
        refine ⟨30498516404603367743612603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20332344269735578495741735 30498516404603367743612603)
        ·
          refine ⟨45747774606905051615418905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30498516404603367743612603 45747774606905051615418905)
          ·
            refine ⟨34310830955178788711564179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45747774606905051615418905 34310830955178788711564179)
            ·
              refine ⟨51466246432768183067346269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34310830955178788711564179 51466246432768183067346269)
              ·
                refine ⟨19299842412288068650254851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51466246432768183067346269 19299842412288068650254851)
                ·
                  refine ⟨28949763618432102975382277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19299842412288068650254851 28949763618432102975382277)
                  ·
                    refine ⟨5428080678456019307884177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28949763618432102975382277 5428080678456019307884177)
                    ·
                      refine ⟨4071060508842014480913133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5428080678456019307884177 4071060508842014480913133)
                      ·
                        rfl

theorem cell23_7928362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 3, 1, 4, 2].length) (baseStart_7928362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7928362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7928362 prefixEnd_7928362 := by exact prefixLift 7928362
  have htrace : WordTrace (prefixWord ++ tailWord_7928362) baseStart_7928362 baseEnd_7928362 := by
    simpa [prefixWord, tailWord_7928362, baseEnd_7928362] using wordTrace_append hprefix tailTrace_7928362
  have hstable : (prefixWord ++ tailWord_7928362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7928362).length < 2 ^ (prefixWord ++ tailWord_7928362).sum := by decide
  have hdescent : baseEnd_7928362 < baseStart_7928362 := by decide
  rcases family_descends (prefixWord ++ tailWord_7928362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7928405 : List Nat := [1, 3, 2, 2, 1, 1, 2, 1, 1, 7, 2]
def baseStart_7928405 : Nat := 118140960795 + 7928405 * 2 ^ 59
def prefixEnd_7928405 : Nat := 4983230072969 + 3 ^ 40 * 7928405 * 2
def baseEnd_7928405 : Nat := 4071082588510157812675435

theorem tailTrace_7928405 : CollatzResearch.WordTrace tailWord_7928405 prefixEnd_7928405 4071082588510157812675435 := by
  unfold tailWord_7928405
  simp only [CollatzResearch.WordTrace]
  refine ⟨289172686841750223616586669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192781791227833482411057779 289172686841750223616586669)
  ·
    refine ⟨108439757565656333856220001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 289172686841750223616586669 108439757565656333856220001)
    ·
      refine ⟨81329818174242250392165001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108439757565656333856220001 81329818174242250392165001)
      ·
        refine ⟨60997363630681687794123751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81329818174242250392165001 60997363630681687794123751)
        ·
          refine ⟨91496045446022531691185627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60997363630681687794123751 91496045446022531691185627)
          ·
            refine ⟨137244068169033797536778441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91496045446022531691185627 137244068169033797536778441)
            ·
              refine ⟨102933051126775348152583831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137244068169033797536778441 102933051126775348152583831)
              ·
                refine ⟨154399576690163022228875747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102933051126775348152583831 154399576690163022228875747)
                ·
                  refine ⟨231599365035244533343313621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 154399576690163022228875747 231599365035244533343313621)
                  ·
                    refine ⟨5428110118013543750233913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 231599365035244533343313621 5428110118013543750233913)
                    ·
                      refine ⟨4071082588510157812675435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5428110118013543750233913 4071082588510157812675435)
                      ·
                        rfl

theorem cell23_7928405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 1, 1, 7, 2].length) (baseStart_7928405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7928405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7928405 prefixEnd_7928405 := by exact prefixLift 7928405
  have htrace : WordTrace (prefixWord ++ tailWord_7928405) baseStart_7928405 baseEnd_7928405 := by
    simpa [prefixWord, tailWord_7928405, baseEnd_7928405] using wordTrace_append hprefix tailTrace_7928405
  have hstable : (prefixWord ++ tailWord_7928405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7928405).length < 2 ^ (prefixWord ++ tailWord_7928405).sum := by decide
  have hdescent : baseEnd_7928405 < baseStart_7928405 := by decide
  rcases family_descends (prefixWord ++ tailWord_7928405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7928408 : List Nat := [2, 1, 2, 2, 1, 2, 2, 3, 1, 2, 5]
def baseStart_7928408 : Nat := 118140960795 + 7928408 * 2 ^ 59
def prefixEnd_7928408 : Nat := 4983230072969 + 3 ^ 40 * 7928408 * 2
def baseEnd_7928408 : Nat := 4071084128952121300937921

theorem tailTrace_7928408 : CollatzResearch.WordTrace tailWord_7928408 prefixEnd_7928408 4071084128952121300937921 := by
  unfold tailWord_7928408
  simp only [CollatzResearch.WordTrace]
  refine ⟨144586398130369677564472939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192781864173826236752630585 144586398130369677564472939)
  ·
    refine ⟨216879597195554516346709409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144586398130369677564472939 216879597195554516346709409)
    ·
      refine ⟨162659697896665887260032057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216879597195554516346709409 162659697896665887260032057)
      ·
        refine ⟨121994773422499415445024043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162659697896665887260032057 121994773422499415445024043)
        ·
          refine ⟨182992160133749123167536065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121994773422499415445024043 182992160133749123167536065)
          ·
            refine ⟨137244120100311842375652049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 182992160133749123167536065 137244120100311842375652049)
            ·
              refine ⟨102933090075233881781739037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137244120100311842375652049 102933090075233881781739037)
              ·
                refine ⟨38599908778212705668152139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 102933090075233881781739037 38599908778212705668152139)
                ·
                  refine ⟨57899863167319058502228209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38599908778212705668152139 57899863167319058502228209)
                  ·
                    refine ⟨43424897375489293876671157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 57899863167319058502228209 43424897375489293876671157)
                    ·
                      refine ⟨4071084128952121300937921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43424897375489293876671157 4071084128952121300937921)
                      ·
                        rfl

theorem cell23_7928408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 3, 1, 2, 5].length) (baseStart_7928408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7928408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7928408 prefixEnd_7928408 := by exact prefixLift 7928408
  have htrace : WordTrace (prefixWord ++ tailWord_7928408) baseStart_7928408 baseEnd_7928408 := by
    simpa [prefixWord, tailWord_7928408, baseEnd_7928408] using wordTrace_append hprefix tailTrace_7928408
  have hstable : (prefixWord ++ tailWord_7928408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7928408).length < 2 ^ (prefixWord ++ tailWord_7928408).sum := by decide
  have hdescent : baseEnd_7928408 < baseStart_7928408 := by decide
  rcases family_descends (prefixWord ++ tailWord_7928408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7928435 : List Nat := [1, 1, 1, 2, 2, 1, 1, 4, 4, 4, 2]
def baseStart_7928435 : Nat := 118140960795 + 7928435 * 2 ^ 59
def prefixEnd_7928435 : Nat := 4983230072969 + 3 ^ 40 * 7928435 * 2
def baseEnd_7928435 : Nat := 4071097992929792695300297

theorem tailTrace_7928435 : CollatzResearch.WordTrace tailWord_7928435 prefixEnd_7928435 4071097992929792695300297 := by
  unfold tailWord_7928435
  simp only [CollatzResearch.WordTrace]
  refine ⟨289173781031641538740178759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192782520687761025826785839 289173781031641538740178759)
  ·
    refine ⟨433760671547462308110268139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289173781031641538740178759 433760671547462308110268139)
    ·
      refine ⟨650641007321193462165402209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 433760671547462308110268139 650641007321193462165402209)
      ·
        refine ⟨487980755490895096624051657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 650641007321193462165402209 487980755490895096624051657)
        ·
          refine ⟨365985566618171322468038743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 487980755490895096624051657 365985566618171322468038743)
          ·
            refine ⟨548978349927256983702058115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 365985566618171322468038743 548978349927256983702058115)
            ·
              refine ⟨823467524890885475553087173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 548978349927256983702058115 823467524890885475553087173)
              ·
                refine ⟨154400160917041026666203845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 823467524890885475553087173 154400160917041026666203845)
                ·
                  refine ⟨28950030171945192499913221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 154400160917041026666203845 28950030171945192499913221)
                  ·
                    refine ⟨5428130657239723593733729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28950030171945192499913221 5428130657239723593733729)
                    ·
                      refine ⟨4071097992929792695300297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5428130657239723593733729 4071097992929792695300297)
                      ·
                        rfl

theorem cell23_7928435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 4, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 4, 4, 4, 2].length) (baseStart_7928435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7928435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7928435 prefixEnd_7928435 := by exact prefixLift 7928435
  have htrace : WordTrace (prefixWord ++ tailWord_7928435) baseStart_7928435 baseEnd_7928435 := by
    simpa [prefixWord, tailWord_7928435, baseEnd_7928435] using wordTrace_append hprefix tailTrace_7928435
  have hstable : (prefixWord ++ tailWord_7928435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7928435).length < 2 ^ (prefixWord ++ tailWord_7928435).sum := by decide
  have hdescent : baseEnd_7928435 < baseStart_7928435 := by decide
  rcases family_descends (prefixWord ++ tailWord_7928435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7928452 : List Nat := [2, 3, 2, 1, 3, 2, 1, 2, 2, 1, 4]
def baseStart_7928452 : Nat := 118140960795 + 7928452 * 2 ^ 59
def prefixEnd_7928452 : Nat := 4983230072969 + 3 ^ 40 * 7928452 * 2
def baseEnd_7928452 : Nat := 4071106722100919128787719

theorem tailTrace_7928452 : CollatzResearch.WordTrace tailWord_7928452 prefixEnd_7928452 4071106722100919128787719 := by
  unfold tailWord_7928452
  simp only [CollatzResearch.WordTrace]
  refine ⟨144587200536289975321773805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192782934048386633762365073 144587200536289975321773805)
  ·
    refine ⟨54220200201108740745665177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144587200536289975321773805 54220200201108740745665177)
    ·
      refine ⟨40665150150831555559248883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54220200201108740745665177 40665150150831555559248883)
      ·
        refine ⟨60997725226247333338873325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40665150150831555559248883 60997725226247333338873325)
        ·
          refine ⟨22874146959842750002077497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60997725226247333338873325 22874146959842750002077497)
          ·
            refine ⟨17155610219882062501558123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22874146959842750002077497 17155610219882062501558123)
            ·
              refine ⟨25733415329823093752337185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17155610219882062501558123 25733415329823093752337185)
              ·
                refine ⟨19300061497367320314252889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25733415329823093752337185 19300061497367320314252889)
                ·
                  refine ⟨14475046123025490235689667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19300061497367320314252889 14475046123025490235689667)
                  ·
                    refine ⟨21712569184538235353534501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14475046123025490235689667 21712569184538235353534501)
                    ·
                      refine ⟨4071106722100919128787719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21712569184538235353534501 4071106722100919128787719)
                      ·
                        rfl

theorem cell23_7928452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 1, 2, 2, 1, 4].length) (baseStart_7928452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7928452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7928452 prefixEnd_7928452 := by exact prefixLift 7928452
  have htrace : WordTrace (prefixWord ++ tailWord_7928452) baseStart_7928452 baseEnd_7928452 := by
    simpa [prefixWord, tailWord_7928452, baseEnd_7928452] using wordTrace_append hprefix tailTrace_7928452
  have hstable : (prefixWord ++ tailWord_7928452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7928452).length < 2 ^ (prefixWord ++ tailWord_7928452).sum := by decide
  have hdescent : baseEnd_7928452 < baseStart_7928452 := by decide
  rcases family_descends (prefixWord ++ tailWord_7928452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7928513 : List Nat := [1, 2, 6, 2, 1, 1, 1, 4, 1, 4]
def baseStart_7928513 : Nat := 118140960795 + 7928513 * 2 ^ 59
def prefixEnd_7928513 : Nat := 4983230072969 + 3 ^ 40 * 7928513 * 2
def baseEnd_7928513 : Nat := 1357046014806947796708313

theorem tailTrace_7928513 : CollatzResearch.WordTrace tailWord_7928513 prefixEnd_7928513 1357046014806947796708313 := by
  unfold tailWord_7928513
  simp only [CollatzResearch.WordTrace]
  refine ⟨289176625925358958061518193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192784417283572638707678795 289176625925358958061518193)
  ·
    refine ⟨216882469444019218546138645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 289176625925358958061518193 216882469444019218546138645)
    ·
      refine ⟨10166365755188400869350249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 216882469444019218546138645 10166365755188400869350249)
      ·
        refine ⟨7624774316391300652012687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10166365755188400869350249 7624774316391300652012687)
        ·
          refine ⟨11437161474586950978019031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7624774316391300652012687 11437161474586950978019031)
          ·
            refine ⟨17155742211880426467028547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11437161474586950978019031 17155742211880426467028547)
            ·
              refine ⟨25733613317820639700542821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17155742211880426467028547 25733613317820639700542821)
              ·
                refine ⟨4825052497091369943851779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25733613317820639700542821 4825052497091369943851779)
                ·
                  refine ⟨7237578745637054915777669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4825052497091369943851779 7237578745637054915777669)
                  ·
                    refine ⟨1357046014806947796708313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7237578745637054915777669 1357046014806947796708313)
                    ·
                      rfl

theorem cell23_7928513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 1, 4, 1, 4].length) (baseStart_7928513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7928513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7928513 prefixEnd_7928513 := by exact prefixLift 7928513
  have htrace : WordTrace (prefixWord ++ tailWord_7928513) baseStart_7928513 baseEnd_7928513 := by
    simpa [prefixWord, tailWord_7928513, baseEnd_7928513] using wordTrace_append hprefix tailTrace_7928513
  have hstable : (prefixWord ++ tailWord_7928513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7928513).length < 2 ^ (prefixWord ++ tailWord_7928513).sum := by decide
  have hdescent : baseEnd_7928513 < baseStart_7928513 := by decide
  rcases family_descends (prefixWord ++ tailWord_7928513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7928535 : List Nat := [1, 1, 3, 2, 1, 4, 1, 3, 1, 6]
def baseStart_7928535 : Nat := 118140960795 + 7928535 * 2 ^ 59
def prefixEnd_7928535 : Nat := 4983230072969 + 3 ^ 40 * 7928535 * 2
def baseEnd_7928535 : Nat := 1357049780331747434683279

theorem tailTrace_7928535 : CollatzResearch.WordTrace tailWord_7928535 prefixEnd_7928535 1357049780331747434683279 := by
  unfold tailWord_7928535
  simp only [CollatzResearch.WordTrace]
  refine ⟨289177428331279255818819059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192784952220852837212546039 289177428331279255818819059)
  ·
    refine ⟨433766142496918883728228589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289177428331279255818819059 433766142496918883728228589)
    ·
      refine ⟨162662303436344581398085721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 433766142496918883728228589 162662303436344581398085721)
      ·
        refine ⟨121996727577258436048564291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162662303436344581398085721 121996727577258436048564291)
        ·
          refine ⟨182995091365887654072846437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121996727577258436048564291 182995091365887654072846437)
          ·
            refine ⟨34311579631103935138658707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 182995091365887654072846437 34311579631103935138658707)
            ·
              refine ⟨51467369446655902707988061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34311579631103935138658707 51467369446655902707988061)
              ·
                refine ⟨19300263542495963515495523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51467369446655902707988061 19300263542495963515495523)
                ·
                  refine ⟨28950395313743945273243285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19300263542495963515495523 28950395313743945273243285)
                  ·
                    refine ⟨1357049780331747434683279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28950395313743945273243285 1357049780331747434683279)
                    ·
                      rfl

theorem cell23_7928535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 3, 1, 6].length) (baseStart_7928535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7928535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7928535 prefixEnd_7928535 := by exact prefixLift 7928535
  have htrace : WordTrace (prefixWord ++ tailWord_7928535) baseStart_7928535 baseEnd_7928535 := by
    simpa [prefixWord, tailWord_7928535, baseEnd_7928535] using wordTrace_append hprefix tailTrace_7928535
  have hstable : (prefixWord ++ tailWord_7928535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7928535).length < 2 ^ (prefixWord ++ tailWord_7928535).sum := by decide
  have hdescent : baseEnd_7928535 < baseStart_7928535 := by decide
  rcases family_descends (prefixWord ++ tailWord_7928535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7928559 : List Nat := [1, 1, 2, 1, 5, 2, 4, 1, 1, 1, 4]
def baseStart_7928559 : Nat := 118140960795 + 7928559 * 2 ^ 59
def prefixEnd_7928559 : Nat := 4983230072969 + 3 ^ 40 * 7928559 * 2
def baseEnd_7928559 : Nat := 4071161664530950210149727

theorem tailTrace_7928559 : CollatzResearch.WordTrace tailWord_7928559 prefixEnd_7928559 4071161664530950210149727 := by
  unfold tailWord_7928559
  simp only [CollatzResearch.WordTrace]
  refine ⟨289178303683192307917692731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192785535788794871945128487 289178303683192307917692731)
  ·
    refine ⟨433767455524788461876539097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289178303683192307917692731 433767455524788461876539097)
    ·
      refine ⟨325325591643591346407404323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 433767455524788461876539097 325325591643591346407404323)
      ·
        refine ⟨487988387465387019611106485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 325325591643591346407404323 487988387465387019611106485)
        ·
          refine ⟨45748911324880033088541233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 487988387465387019611106485 45748911324880033088541233)
          ·
            refine ⟨34311683493660024816405925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45748911324880033088541233 34311683493660024816405925)
            ·
              refine ⟨6433440655061254653076111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34311683493660024816405925 6433440655061254653076111)
              ·
                refine ⟨9650160982591881979614167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6433440655061254653076111 9650160982591881979614167)
                ·
                  refine ⟨14475241473887822969421251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9650160982591881979614167 14475241473887822969421251)
                  ·
                    refine ⟨21712862210831734454131877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14475241473887822969421251 21712862210831734454131877)
                    ·
                      refine ⟨4071161664530950210149727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21712862210831734454131877 4071161664530950210149727)
                      ·
                        rfl

theorem cell23_7928559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 4, 1, 1, 1, 4].length) (baseStart_7928559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7928559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7928559 prefixEnd_7928559 := by exact prefixLift 7928559
  have htrace : WordTrace (prefixWord ++ tailWord_7928559) baseStart_7928559 baseEnd_7928559 := by
    simpa [prefixWord, tailWord_7928559, baseEnd_7928559] using wordTrace_append hprefix tailTrace_7928559
  have hstable : (prefixWord ++ tailWord_7928559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7928559).length < 2 ^ (prefixWord ++ tailWord_7928559).sum := by decide
  have hdescent : baseEnd_7928559 < baseStart_7928559 := by decide
  rcases family_descends (prefixWord ++ tailWord_7928559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7928599 : List Nat := [1, 1, 3, 4, 3, 2, 2, 7]
def baseStart_7928599 : Nat := 118140960795 + 7928599 * 2 ^ 59
def prefixEnd_7928599 : Nat := 4983230072969 + 3 ^ 40 * 7928599 * 2
def baseEnd_7928599 : Nat := 150784526065078890875909

theorem tailTrace_7928599 : CollatzResearch.WordTrace tailWord_7928599 prefixEnd_7928599 150784526065078890875909 := by
  unfold tailWord_7928599
  simp only [CollatzResearch.WordTrace]
  refine ⟨289179762603047394749148851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192786508402031596499432567 289179762603047394749148851)
  ·
    refine ⟨433769643904571092123723277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289179762603047394749148851 433769643904571092123723277)
    ·
      refine ⟨162663616464214159546396229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 433769643904571092123723277 162663616464214159546396229)
      ·
        refine ⟨30499428087040154914949293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 162663616464214159546396229 30499428087040154914949293)
        ·
          refine ⟨11437285532640058093105985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30499428087040154914949293 11437285532640058093105985)
          ·
            refine ⟨8577964149480043569829489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11437285532640058093105985 8577964149480043569829489)
            ·
              refine ⟨6433473112110032677372117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8577964149480043569829489 6433473112110032677372117)
              ·
                refine ⟨150784526065078890875909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6433473112110032677372117 150784526065078890875909)
                ·
                  rfl

theorem cell23_7928599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 2, 2, 7].length) (baseStart_7928599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7928599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7928599 prefixEnd_7928599 := by exact prefixLift 7928599
  have htrace : WordTrace (prefixWord ++ tailWord_7928599) baseStart_7928599 baseEnd_7928599 := by
    simpa [prefixWord, tailWord_7928599, baseEnd_7928599] using wordTrace_append hprefix tailTrace_7928599
  have hstable : (prefixWord ++ tailWord_7928599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7928599).length < 2 ^ (prefixWord ++ tailWord_7928599).sum := by decide
  have hdescent : baseEnd_7928599 < baseStart_7928599 := by decide
  rcases family_descends (prefixWord ++ tailWord_7928599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7928610 : List Nat := [3, 3, 1, 1, 2, 4, 1, 3, 1, 2, 2]
def baseStart_7928610 : Nat := 118140960795 + 7928610 * 2 ^ 59
def prefixEnd_7928610 : Nat := 4983230072969 + 3 ^ 40 * 7928610 * 2
def baseEnd_7928610 : Nat := 4071187852044329510611993

theorem tailTrace_7928610 : CollatzResearch.WordTrace tailWord_7928610 prefixEnd_7928610 4071187852044329510611993 := by
  unfold tailWord_7928610
  simp only [CollatzResearch.WordTrace]
  refine ⟨72295040951501885906949821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192786775870671695751866189 72295040951501885906949821)
  ·
    refine ⟨27110640356813207215106183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72295040951501885906949821 27110640356813207215106183)
    ·
      refine ⟨40665960535219810822659275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27110640356813207215106183 40665960535219810822659275)
      ·
        refine ⟨60998940802829716233988913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40665960535219810822659275 60998940802829716233988913)
        ·
          refine ⟨45749205602122287175491685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60998940802829716233988913 45749205602122287175491685)
          ·
            refine ⟨8577976050397928845404691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45749205602122287175491685 8577976050397928845404691)
            ·
              refine ⟨12866964075596893268107037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8577976050397928845404691 12866964075596893268107037)
              ·
                refine ⟨4825111528348834975540139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12866964075596893268107037 4825111528348834975540139)
                ·
                  refine ⟨7237667292523252463310209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4825111528348834975540139 7237667292523252463310209)
                  ·
                    refine ⟨5428250469392439347482657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7237667292523252463310209 5428250469392439347482657)
                    ·
                      refine ⟨4071187852044329510611993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5428250469392439347482657 4071187852044329510611993)
                      ·
                        rfl

theorem cell23_7928610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 4, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 4, 1, 3, 1, 2, 2].length) (baseStart_7928610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7928610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7928610 prefixEnd_7928610 := by exact prefixLift 7928610
  have htrace : WordTrace (prefixWord ++ tailWord_7928610) baseStart_7928610 baseEnd_7928610 := by
    simpa [prefixWord, tailWord_7928610, baseEnd_7928610] using wordTrace_append hprefix tailTrace_7928610
  have hstable : (prefixWord ++ tailWord_7928610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7928610).length < 2 ^ (prefixWord ++ tailWord_7928610).sum := by decide
  have hdescent : baseEnd_7928610 < baseStart_7928610 := by decide
  rcases family_descends (prefixWord ++ tailWord_7928610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7928652 : List Nat := [2, 2, 1, 3, 3, 1, 1, 2, 2, 1, 5]
def baseStart_7928652 : Nat := 118140960795 + 7928652 * 2 ^ 59
def prefixEnd_7928652 : Nat := 4983230072969 + 3 ^ 40 * 7928652 * 2
def baseEnd_7928652 : Nat := 4071209418231818346286799

theorem tailTrace_7928652 : CollatzResearch.WordTrace tailWord_7928652 prefixEnd_7928652 4071209418231818346286799 := by
  unfold tailWord_7928652
  simp only [CollatzResearch.WordTrace]
  refine ⟨144590847835927692400414105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192787797114570256533885473 144590847835927692400414105)
  ·
    refine ⟨108443135876945769300310579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144590847835927692400414105 108443135876945769300310579)
    ·
      refine ⟨162664703815418653950465869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108443135876945769300310579 162664703815418653950465869)
      ·
        refine ⟨60999263930781995231424701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 162664703815418653950465869 60999263930781995231424701)
        ·
          refine ⟨22874723974043248211784263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60999263930781995231424701 22874723974043248211784263)
          ·
            refine ⟨34312085961064872317676395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22874723974043248211784263 34312085961064872317676395)
            ·
              refine ⟨51468128941597308476514593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34312085961064872317676395 51468128941597308476514593)
              ·
                refine ⟨38601096706197981357385945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51468128941597308476514593 38601096706197981357385945)
                ·
                  refine ⟨28950822529648486018039459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38601096706197981357385945 28950822529648486018039459)
                  ·
                    refine ⟨43426233794472729027059189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28950822529648486018039459 43426233794472729027059189)
                    ·
                      refine ⟨4071209418231818346286799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43426233794472729027059189 4071209418231818346286799)
                      ·
                        rfl

theorem cell23_7928652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 2, 2, 1, 5].length) (baseStart_7928652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7928652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7928652 prefixEnd_7928652 := by exact prefixLift 7928652
  have htrace : WordTrace (prefixWord ++ tailWord_7928652) baseStart_7928652 baseEnd_7928652 := by
    simpa [prefixWord, tailWord_7928652, baseEnd_7928652] using wordTrace_append hprefix tailTrace_7928652
  have hstable : (prefixWord ++ tailWord_7928652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7928652).length < 2 ^ (prefixWord ++ tailWord_7928652).sum := by decide
  have hdescent : baseEnd_7928652 < baseStart_7928652 := by decide
  rcases family_descends (prefixWord ++ tailWord_7928652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7928653 : List Nat := [1, 6, 1, 2, 2, 1, 1, 1, 3, 3, 2]
def baseStart_7928653 : Nat := 118140960795 + 7928653 * 2 ^ 59
def prefixEnd_7928653 : Nat := 4983230072969 + 3 ^ 40 * 7928653 * 2
def baseEnd_7928653 : Nat := 4071209931712472842374295

theorem tailTrace_7928653 : CollatzResearch.WordTrace tailWord_7928653 prefixEnd_7928653 4071209931712472842374295 := by
  unfold tailWord_7928653
  simp only [CollatzResearch.WordTrace]
  refine ⟨289181732144851761971614613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192787821429901174647743075 289181732144851761971614613)
  ·
    refine ⟨13555393694289926342419435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 289181732144851761971614613 13555393694289926342419435)
    ·
      refine ⟨20333090541434889513629153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13555393694289926342419435 20333090541434889513629153)
      ·
        refine ⟨15249817906076167135221865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20333090541434889513629153 15249817906076167135221865)
        ·
          refine ⟨11437363429557125351416399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15249817906076167135221865 11437363429557125351416399)
          ·
            refine ⟨17156045144335688027124599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11437363429557125351416399 17156045144335688027124599)
            ·
              refine ⟨25734067716503532040686899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17156045144335688027124599 25734067716503532040686899)
              ·
                refine ⟨38601101574755298061030349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25734067716503532040686899 38601101574755298061030349)
                ·
                  refine ⟨14475413090533236772886381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38601101574755298061030349 14475413090533236772886381)
                  ·
                    refine ⟨5428279908949963789832393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14475413090533236772886381 5428279908949963789832393)
                    ·
                      refine ⟨4071209931712472842374295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5428279908949963789832393 4071209931712472842374295)
                      ·
                        rfl

theorem cell23_7928653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 1, 1, 3, 3, 2].length) (baseStart_7928653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7928653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7928653 prefixEnd_7928653 := by exact prefixLift 7928653
  have htrace : WordTrace (prefixWord ++ tailWord_7928653) baseStart_7928653 baseEnd_7928653 := by
    simpa [prefixWord, tailWord_7928653, baseEnd_7928653] using wordTrace_append hprefix tailTrace_7928653
  have hstable : (prefixWord ++ tailWord_7928653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7928653).length < 2 ^ (prefixWord ++ tailWord_7928653).sum := by decide
  have hdescent : baseEnd_7928653 < baseStart_7928653 := by decide
  rcases family_descends (prefixWord ++ tailWord_7928653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7928689 : List Nat := [1, 2, 2, 2, 1, 5, 1, 4, 5]
def baseStart_7928689 : Nat := 118140960795 + 7928689 * 2 ^ 59
def prefixEnd_7928689 : Nat := 4983230072969 + 3 ^ 40 * 7928689 * 2
def baseEnd_7928689 : Nat := 452358713001781633502681

theorem tailTrace_7928689 : CollatzResearch.WordTrace tailWord_7928689 prefixEnd_7928689 452358713001781633502681 := by
  unfold tailWord_7928689
  simp only [CollatzResearch.WordTrace]
  refine ⟨289183045172721340119925121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192788696781814226746616747 289183045172721340119925121)
  ·
    refine ⟨216887283879541005089943841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 289183045172721340119925121 216887283879541005089943841)
    ·
      refine ⟨162665462909655753817457881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216887283879541005089943841 162665462909655753817457881)
      ·
        refine ⟨121999097182241815363093411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162665462909655753817457881 121999097182241815363093411)
        ·
          refine ⟨182998645773362723044640117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121999097182241815363093411 182998645773362723044640117)
          ·
            refine ⟨17156123041252755285435011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 182998645773362723044640117 17156123041252755285435011)
            ·
              refine ⟨25734184561879132928152517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17156123041252755285435011 25734184561879132928152517)
              ·
                refine ⟨4825159605352337424028597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25734184561879132928152517 4825159605352337424028597)
                ·
                  refine ⟨452358713001781633502681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4825159605352337424028597 452358713001781633502681)
                  ·
                    rfl

theorem cell23_7928689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 1, 4, 5].length) (baseStart_7928689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7928689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7928689 prefixEnd_7928689 := by exact prefixLift 7928689
  have htrace : WordTrace (prefixWord ++ tailWord_7928689) baseStart_7928689 baseEnd_7928689 := by
    simpa [prefixWord, tailWord_7928689, baseEnd_7928689] using wordTrace_append hprefix tailTrace_7928689
  have hstable : (prefixWord ++ tailWord_7928689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7928689).length < 2 ^ (prefixWord ++ tailWord_7928689).sum := by decide
  have hdescent : baseEnd_7928689 < baseStart_7928689 := by decide
  rcases family_descends (prefixWord ++ tailWord_7928689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7928739 : List Nat := [1, 1, 1, 4, 1, 2, 3, 2, 2, 4, 2]
def baseStart_7928739 : Nat := 118140960795 + 7928739 * 2 ^ 59
def prefixEnd_7928739 : Nat := 4983230072969 + 3 ^ 40 * 7928739 * 2
def baseEnd_7928739 : Nat := 4071254091048759505898899

theorem tailTrace_7928739 : CollatzResearch.WordTrace tailWord_7928739 prefixEnd_7928739 4071254091048759505898899 := by
  unfold tailWord_7928739
  simp only [CollatzResearch.WordTrace]
  refine ⟨289184868822540198659245271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192789912548360132439496847 289184868822540198659245271)
  ·
    refine ⟨433777303233810297988867907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289184868822540198659245271 433777303233810297988867907)
    ·
      refine ⟨650665954850715446983301861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 433777303233810297988867907 650665954850715446983301861)
      ·
        refine ⟨121999866534509146309369099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 650665954850715446983301861 121999866534509146309369099)
        ·
          refine ⟨182999799801763719464053649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121999866534509146309369099 182999799801763719464053649)
          ·
            refine ⟨137249849851322789598040237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 182999799801763719464053649 137249849851322789598040237)
            ·
              refine ⟨51468693694246046099265089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 137249849851322789598040237 51468693694246046099265089)
              ·
                refine ⟨38601520270684534574448817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51468693694246046099265089 38601520270684534574448817)
                ·
                  refine ⟨28951140203013400930836613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38601520270684534574448817 28951140203013400930836613)
                  ·
                    refine ⟨5428338788065012674531865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28951140203013400930836613 5428338788065012674531865)
                    ·
                      refine ⟨4071254091048759505898899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5428338788065012674531865 4071254091048759505898899)
                      ·
                        rfl

theorem cell23_7928739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 2, 2, 4, 2].length) (baseStart_7928739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7928739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7928739 prefixEnd_7928739 := by exact prefixLift 7928739
  have htrace : WordTrace (prefixWord ++ tailWord_7928739) baseStart_7928739 baseEnd_7928739 := by
    simpa [prefixWord, tailWord_7928739, baseEnd_7928739] using wordTrace_append hprefix tailTrace_7928739
  have hstable : (prefixWord ++ tailWord_7928739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7928739).length < 2 ^ (prefixWord ++ tailWord_7928739).sum := by decide
  have hdescent : baseEnd_7928739 < baseStart_7928739 := by decide
  rcases family_descends (prefixWord ++ tailWord_7928739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7928756 : List Nat := [2, 5, 2, 1, 1, 1, 1, 2, 1, 3, 4]
def baseStart_7928756 : Nat := 118140960795 + 7928756 * 2 ^ 59
def prefixEnd_7928756 : Nat := 4983230072969 + 3 ^ 40 * 7928756 * 2
def baseEnd_7928756 : Nat := 4071262820219885939386321

theorem tailTrace_7928756 : CollatzResearch.WordTrace tailWord_7928756 prefixEnd_7928756 4071262820219885939386321 := by
  unfold tailWord_7928756
  simp only [CollatzResearch.WordTrace]
  refine ⟨144592744431739305281307061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192790325908985740375076081 144592744431739305281307061)
  ·
    refine ⟨13555569790475559870122537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 144592744431739305281307061 13555569790475559870122537)
    ·
      refine ⟨10166677342856669902591903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13555569790475559870122537 10166677342856669902591903)
      ·
        refine ⟨15250016014285004853887855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10166677342856669902591903 15250016014285004853887855)
        ·
          refine ⟨22875024021427507280831783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15250016014285004853887855 22875024021427507280831783)
          ·
            refine ⟨34312536032141260921247675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22875024021427507280831783 34312536032141260921247675)
            ·
              refine ⟨51468804048211891381871513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34312536032141260921247675 51468804048211891381871513)
              ·
                refine ⟨38601603036158918536403635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51468804048211891381871513 38601603036158918536403635)
                ·
                  refine ⟨57902404554238377804605453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38601603036158918536403635 57902404554238377804605453)
                  ·
                    refine ⟨21713401707839391676727045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 57902404554238377804605453 21713401707839391676727045)
                    ·
                      refine ⟨4071262820219885939386321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21713401707839391676727045 4071262820219885939386321)
                      ·
                        rfl

theorem cell23_7928756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 2, 1, 3, 4].length) (baseStart_7928756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7928756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7928756 prefixEnd_7928756 := by exact prefixLift 7928756
  have htrace : WordTrace (prefixWord ++ tailWord_7928756) baseStart_7928756 baseEnd_7928756 := by
    simpa [prefixWord, tailWord_7928756, baseEnd_7928756] using wordTrace_append hprefix tailTrace_7928756
  have hstable : (prefixWord ++ tailWord_7928756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7928756).length < 2 ^ (prefixWord ++ tailWord_7928756).sum := by decide
  have hdescent : baseEnd_7928756 < baseStart_7928756 := by decide
  rcases family_descends (prefixWord ++ tailWord_7928756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7928774 : List Nat := [6, 1, 3, 1, 1, 2, 1, 3, 5]
def baseStart_7928774 : Nat := 118140960795 + 7928774 * 2 ^ 59
def prefixEnd_7928774 : Nat := 4983230072969 + 3 ^ 40 * 7928774 * 2
def baseEnd_7928774 : Nat := 452363562541296318773471

theorem tailTrace_7928774 : CollatzResearch.WordTrace tailWord_7928774 prefixEnd_7928774 452363562541296318773471 := by
  unfold tailWord_7928774
  simp only [CollatzResearch.WordTrace]
  refine ⟨9037067043044168738649043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 192790763584942266424512917 9037067043044168738649043)
  ·
    refine ⟨13555600564566253107973565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9037067043044168738649043 13555600564566253107973565)
    ·
      refine ⟨5083350211712344915490087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13555600564566253107973565 5083350211712344915490087)
      ·
        refine ⟨7625025317568517373235131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5083350211712344915490087 7625025317568517373235131)
        ·
          refine ⟨11437537976352776059852697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7625025317568517373235131 11437537976352776059852697)
          ·
            refine ⟨8578153482264582044889523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11437537976352776059852697 8578153482264582044889523)
            ·
              refine ⟨12867230223396873067334285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8578153482264582044889523 12867230223396873067334285)
              ·
                refine ⟨4825211333773827400250357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12867230223396873067334285 4825211333773827400250357)
                ·
                  refine ⟨452363562541296318773471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4825211333773827400250357 452363562541296318773471)
                  ·
                    rfl

theorem cell23_7928774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 2, 1, 3, 5].length) (baseStart_7928774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7928774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7928774 prefixEnd_7928774 := by exact prefixLift 7928774
  have htrace : WordTrace (prefixWord ++ tailWord_7928774) baseStart_7928774 baseEnd_7928774 := by
    simpa [prefixWord, tailWord_7928774, baseEnd_7928774] using wordTrace_append hprefix tailTrace_7928774
  have hstable : (prefixWord ++ tailWord_7928774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7928774).length < 2 ^ (prefixWord ++ tailWord_7928774).sum := by decide
  have hdescent : baseEnd_7928774 < baseStart_7928774 := by decide
  rcases family_descends (prefixWord ++ tailWord_7928774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7928783 : List Nat := [1, 1, 2, 1, 1, 8, 1, 3, 1, 4]
def baseStart_7928783 : Nat := 118140960795 + 7928783 * 2 ^ 59
def prefixEnd_7928783 : Nat := 4983230072969 + 3 ^ 40 * 7928783 * 2
def baseEnd_7928783 : Nat := 1357092228065852444582899

theorem tailTrace_7928783 : CollatzResearch.WordTrace tailWord_7928783 prefixEnd_7928783 1357092228065852444582899 := by
  unfold tailWord_7928783
  simp only [CollatzResearch.WordTrace]
  refine ⟨289186473634380794173847003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192790982422920529449231335 289186473634380794173847003)
  ·
    refine ⟨433779710451571191260770505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289186473634380794173847003 433779710451571191260770505)
    ·
      refine ⟨325334782838678393445577879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 433779710451571191260770505 325334782838678393445577879)
      ·
        refine ⟨488002174258017590168366819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 325334782838678393445577879 488002174258017590168366819)
        ·
          refine ⟨732003261387026385252550229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 488002174258017590168366819 732003261387026385252550229)
          ·
            refine ⟨8578163219379215452178323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 732003261387026385252550229 8578163219379215452178323)
            ·
              refine ⟨12867244829068823178267485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8578163219379215452178323 12867244829068823178267485)
              ·
                refine ⟨4825216810900808691850307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12867244829068823178267485 4825216810900808691850307)
                ·
                  refine ⟨7237825216351213037775461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4825216810900808691850307 7237825216351213037775461)
                  ·
                    refine ⟨1357092228065852444582899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7237825216351213037775461 1357092228065852444582899)
                    ·
                      rfl

theorem cell23_7928783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 8, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 8, 1, 3, 1, 4].length) (baseStart_7928783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7928783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7928783 prefixEnd_7928783 := by exact prefixLift 7928783
  have htrace : WordTrace (prefixWord ++ tailWord_7928783) baseStart_7928783 baseEnd_7928783 := by
    simpa [prefixWord, tailWord_7928783, baseEnd_7928783] using wordTrace_append hprefix tailTrace_7928783
  have hstable : (prefixWord ++ tailWord_7928783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7928783).length < 2 ^ (prefixWord ++ tailWord_7928783).sum := by decide
  have hdescent : baseEnd_7928783 < baseStart_7928783 := by decide
  rcases family_descends (prefixWord ++ tailWord_7928783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7928812 : List Nat := [2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 4]
def baseStart_7928812 : Nat := 118140960795 + 7928812 * 2 ^ 59
def prefixEnd_7928812 : Nat := 4983230072969 + 3 ^ 40 * 7928812 * 2
def baseEnd_7928812 : Nat := 4071291575136537720286063

theorem tailTrace_7928812 : CollatzResearch.WordTrace tailWord_7928812 prefixEnd_7928812 4071291575136537720286063 := by
  unfold tailWord_7928812
  simp only [CollatzResearch.WordTrace]
  refine ⟨144593765675637866063326345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192791687567517154751101793 144593765675637866063326345)
  ·
    refine ⟨108445324256728399547494759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144593765675637866063326345 108445324256728399547494759)
    ·
      refine ⟨162667986385092599321242139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108445324256728399547494759 162667986385092599321242139)
      ·
        refine ⟨244001979577638898981863209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162667986385092599321242139 244001979577638898981863209)
        ·
          refine ⟨183001484683229174236397407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 244001979577638898981863209 183001484683229174236397407)
          ·
            refine ⟨274502227024843761354596111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183001484683229174236397407 274502227024843761354596111)
            ·
              refine ⟨411753340537265642031894167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 274502227024843761354596111 411753340537265642031894167)
              ·
                refine ⟨617630010805898463047841251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 411753340537265642031894167 617630010805898463047841251)
                ·
                  refine ⟨926445016208847694571761877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 617630010805898463047841251 926445016208847694571761877)
                  ·
                    refine ⟨21713555067394867841525669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 926445016208847694571761877 21713555067394867841525669)
                    ·
                      refine ⟨4071291575136537720286063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21713555067394867841525669 4071291575136537720286063)
                      ·
                        rfl

theorem cell23_7928812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 4].length) (baseStart_7928812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7928812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7928812 prefixEnd_7928812 := by exact prefixLift 7928812
  have htrace : WordTrace (prefixWord ++ tailWord_7928812) baseStart_7928812 baseEnd_7928812 := by
    simpa [prefixWord, tailWord_7928812, baseEnd_7928812] using wordTrace_append hprefix tailTrace_7928812
  have hstable : (prefixWord ++ tailWord_7928812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7928812).length < 2 ^ (prefixWord ++ tailWord_7928812).sum := by decide
  have hdescent : baseEnd_7928812 < baseStart_7928812 := by decide
  rcases family_descends (prefixWord ++ tailWord_7928812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7928833 : List Nat := [1, 2, 4, 1, 2, 3, 2, 1, 2, 3, 2]
def baseStart_7928833 : Nat := 118140960795 + 7928833 * 2 ^ 59
def prefixEnd_7928833 : Nat := 4983230072969 + 3 ^ 40 * 7928833 * 2
def baseEnd_7928833 : Nat := 4071302358230282138123467

theorem tailTrace_7928833 : CollatzResearch.WordTrace tailWord_7928833 prefixEnd_7928833 4071302358230282138123467 := by
  unfold tailWord_7928833
  simp only [CollatzResearch.WordTrace]
  refine ⟨289188297284199652713167153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192792198189466435142111435 289188297284199652713167153)
  ·
    refine ⟨216891222963149739534875365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 289188297284199652713167153 216891222963149739534875365)
    ·
      refine ⟨40667104305590576162789131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 216891222963149739534875365 40667104305590576162789131)
      ·
        refine ⟨61000656458385864244183697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40667104305590576162789131 61000656458385864244183697)
        ·
          refine ⟨45750492343789398183137773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61000656458385864244183697 45750492343789398183137773)
          ·
            refine ⟨17156434628921024318676665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45750492343789398183137773 17156434628921024318676665)
            ·
              refine ⟨12867325971690768239007499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17156434628921024318676665 12867325971690768239007499)
              ·
                refine ⟨19300988957536152358511249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12867325971690768239007499 19300988957536152358511249)
                ·
                  refine ⟨14475741718152114268883437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19300988957536152358511249 14475741718152114268883437)
                  ·
                    refine ⟨5428403144307042850831289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14475741718152114268883437 5428403144307042850831289)
                    ·
                      refine ⟨4071302358230282138123467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5428403144307042850831289 4071302358230282138123467)
                      ·
                        rfl

theorem cell23_7928833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 2, 1, 2, 3, 2].length) (baseStart_7928833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7928833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7928833 prefixEnd_7928833 := by exact prefixLift 7928833
  have htrace : WordTrace (prefixWord ++ tailWord_7928833) baseStart_7928833 baseEnd_7928833 := by
    simpa [prefixWord, tailWord_7928833, baseEnd_7928833] using wordTrace_append hprefix tailTrace_7928833
  have hstable : (prefixWord ++ tailWord_7928833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7928833).length < 2 ^ (prefixWord ++ tailWord_7928833).sum := by decide
  have hdescent : baseEnd_7928833 < baseStart_7928833 := by decide
  rcases family_descends (prefixWord ++ tailWord_7928833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7928839 : List Nat := [1, 1, 4, 3, 1, 1, 3, 2, 1, 6]
def baseStart_7928839 : Nat := 118140960795 + 7928839 * 2 ^ 59
def prefixEnd_7928839 : Nat := 4983230072969 + 3 ^ 40 * 7928839 * 2
def baseEnd_7928839 : Nat := 1357101813038069704882813

theorem tailTrace_7928839 : CollatzResearch.WordTrace tailWord_7928839 prefixEnd_7928839 1357101813038069704882813 := by
  unfold tailWord_7928839
  simp only [CollatzResearch.WordTrace]
  refine ⟨289188516122177915737885571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192792344081451943825257047 289188516122177915737885571)
  ·
    refine ⟨433782774183266873606828357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289188516122177915737885571 433782774183266873606828357)
    ·
      refine ⟨81334270159362538801280317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 433782774183266873606828357 81334270159362538801280317)
      ·
        refine ⟨30500351309760952050480119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81334270159362538801280317 30500351309760952050480119)
        ·
          refine ⟨45750526964641428075720179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30500351309760952050480119 45750526964641428075720179)
          ·
            refine ⟨68625790446962142113580269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45750526964641428075720179 68625790446962142113580269)
            ·
              refine ⟨25734671417610803292592601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68625790446962142113580269 25734671417610803292592601)
              ·
                refine ⟨19301003563208102469444451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25734671417610803292592601 19301003563208102469444451)
                ·
                  refine ⟨28951505344812153704166677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19301003563208102469444451 28951505344812153704166677)
                  ·
                    refine ⟨1357101813038069704882813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28951505344812153704166677 1357101813038069704882813)
                    ·
                      rfl

theorem cell23_7928839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 3, 2, 1, 6].length) (baseStart_7928839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7928839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7928839 prefixEnd_7928839 := by exact prefixLift 7928839
  have htrace : WordTrace (prefixWord ++ tailWord_7928839) baseStart_7928839 baseEnd_7928839 := by
    simpa [prefixWord, tailWord_7928839, baseEnd_7928839] using wordTrace_append hprefix tailTrace_7928839
  have hstable : (prefixWord ++ tailWord_7928839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7928839).length < 2 ^ (prefixWord ++ tailWord_7928839).sum := by decide
  have hdescent : baseEnd_7928839 < baseStart_7928839 := by decide
  rcases family_descends (prefixWord ++ tailWord_7928839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7928856 : List Nat := [2, 1, 2, 3, 2, 2, 1, 4, 2, 4]
def baseStart_7928856 : Nat := 118140960795 + 7928856 * 2 ^ 59
def prefixEnd_7928856 : Nat := 4983230072969 + 3 ^ 40 * 7928856 * 2
def baseEnd_7928856 : Nat := 1357104722761778516045287

theorem tailTrace_7928856 : CollatzResearch.WordTrace tailWord_7928856 prefixEnd_7928856 1357104722761778516045287 := by
  unfold tailWord_7928856
  simp only [CollatzResearch.WordTrace]
  refine ⟨144594568081558163820627211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192792757442077551760836281 144594568081558163820627211)
  ·
    refine ⟨216891852122337245730940817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144594568081558163820627211 216891852122337245730940817)
    ·
      refine ⟨162668889091752934298205613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216891852122337245730940817 162668889091752934298205613)
      ·
        refine ⟨61000833409407350361827105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 162668889091752934298205613 61000833409407350361827105)
        ·
          refine ⟨45750625057055512771370329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61000833409407350361827105 45750625057055512771370329)
          ·
            refine ⟨34312968792791634578527747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45750625057055512771370329 34312968792791634578527747)
            ·
              refine ⟨51469453189187451867791621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34312968792791634578527747 51469453189187451867791621)
              ·
                refine ⟨9650522472972647225210929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51469453189187451867791621 9650522472972647225210929)
                ·
                  refine ⟨7237891854729485418908197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9650522472972647225210929 7237891854729485418908197)
                  ·
                    refine ⟨1357104722761778516045287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7237891854729485418908197 1357104722761778516045287)
                    ·
                      rfl

theorem cell23_7928856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 4, 2, 4].length) (baseStart_7928856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7928856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7928856 prefixEnd_7928856 := by exact prefixLift 7928856
  have htrace : WordTrace (prefixWord ++ tailWord_7928856) baseStart_7928856 baseEnd_7928856 := by
    simpa [prefixWord, tailWord_7928856, baseEnd_7928856] using wordTrace_append hprefix tailTrace_7928856
  have hstable : (prefixWord ++ tailWord_7928856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7928856).length < 2 ^ (prefixWord ++ tailWord_7928856).sum := by decide
  have hdescent : baseEnd_7928856 < baseStart_7928856 := by decide
  rcases family_descends (prefixWord ++ tailWord_7928856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7928866 : List Nat := [3, 3, 1, 1, 1, 3, 1, 2, 3, 2, 3]
def baseStart_7928866 : Nat := 118140960795 + 7928866 * 2 ^ 59
def prefixEnd_7928866 : Nat := 4983230072969 + 3 ^ 40 * 7928866 * 2
def baseEnd_7928866 : Nat := 4071319303091880509010815

theorem tailTrace_7928866 : CollatzResearch.WordTrace tailWord_7928866 prefixEnd_7928866 4071319303091880509010815 := by
  unfold tailWord_7928866
  simp only [CollatzResearch.WordTrace]
  refine ⟨72297375223270024837279613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192793000595386732899412301 72297375223270024837279613)
  ·
    refine ⟨27111515708726259313979855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72297375223270024837279613 27111515708726259313979855)
    ·
      refine ⟨40667273563089388970969783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27111515708726259313979855 40667273563089388970969783)
      ·
        refine ⟨61000910344634083456454675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40667273563089388970969783 61000910344634083456454675)
        ·
          refine ⟨91501365516951125184682013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61000910344634083456454675 91501365516951125184682013)
          ·
            refine ⟨34313012068856671944255755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91501365516951125184682013 34313012068856671944255755)
            ·
              refine ⟨51469518103285007916383633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34313012068856671944255755 51469518103285007916383633)
              ·
                refine ⟨38602138577463755937287725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51469518103285007916383633 38602138577463755937287725)
                ·
                  refine ⟨14475801966548908476482897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38602138577463755937287725 14475801966548908476482897)
                  ·
                    refine ⟨10856851474911681357362173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14475801966548908476482897 10856851474911681357362173)
                    ·
                      refine ⟨4071319303091880509010815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10856851474911681357362173 4071319303091880509010815)
                      ·
                        rfl

theorem cell23_7928866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 2, 3, 2, 3].length) (baseStart_7928866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7928866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7928866 prefixEnd_7928866 := by exact prefixLift 7928866
  have htrace : WordTrace (prefixWord ++ tailWord_7928866) baseStart_7928866 baseEnd_7928866 := by
    simpa [prefixWord, tailWord_7928866, baseEnd_7928866] using wordTrace_append hprefix tailTrace_7928866
  have hstable : (prefixWord ++ tailWord_7928866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7928866).length < 2 ^ (prefixWord ++ tailWord_7928866).sum := by decide
  have hdescent : baseEnd_7928866 < baseStart_7928866 := by decide
  rcases family_descends (prefixWord ++ tailWord_7928866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7928896 : List Nat := [2, 1, 1, 2, 2, 3, 2, 2, 4, 1, 3]
def baseStart_7928896 : Nat := 118140960795 + 7928896 * 2 ^ 59
def prefixEnd_7928896 : Nat := 4983230072969 + 3 ^ 40 * 7928896 * 2
def baseEnd_7928896 : Nat := 4071334707511515391635677

theorem tailTrace_7928896 : CollatzResearch.WordTrace tailWord_7928896 prefixEnd_7928896 4071334707511515391635677 := by
  unfold tailWord_7928896
  simp only [CollatzResearch.WordTrace]
  refine ⟨144595297541485707236355271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192793730055314276315140361 144595297541485707236355271)
  ·
    refine ⟨216892946312228560854532907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144595297541485707236355271 216892946312228560854532907)
    ·
      refine ⟨325339419468342841281799361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216892946312228560854532907 325339419468342841281799361)
      ·
        refine ⟨244004564601257130961349521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 325339419468342841281799361 244004564601257130961349521)
        ·
          refine ⟨183003423450942848221012141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 244004564601257130961349521 183003423450942848221012141)
          ·
            refine ⟨68626283794103568082879553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 183003423450942848221012141 68626283794103568082879553)
            ·
              refine ⟨51469712845577676062159665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68626283794103568082879553 51469712845577676062159665)
              ·
                refine ⟨38602284634183257046619749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51469712845577676062159665 38602284634183257046619749)
                ·
                  refine ⟨7237928368909360696241203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38602284634183257046619749 7237928368909360696241203)
                  ·
                    refine ⟨10856892553364041044361805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7237928368909360696241203 10856892553364041044361805)
                    ·
                      refine ⟨4071334707511515391635677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10856892553364041044361805 4071334707511515391635677)
                      ·
                        rfl

theorem cell23_7928896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 2, 4, 1, 3].length) (baseStart_7928896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7928896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7928896 prefixEnd_7928896 := by exact prefixLift 7928896
  have htrace : WordTrace (prefixWord ++ tailWord_7928896) baseStart_7928896 baseEnd_7928896 := by
    simpa [prefixWord, tailWord_7928896, baseEnd_7928896] using wordTrace_append hprefix tailTrace_7928896
  have hstable : (prefixWord ++ tailWord_7928896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7928896).length < 2 ^ (prefixWord ++ tailWord_7928896).sum := by decide
  have hdescent : baseEnd_7928896 < baseStart_7928896 := by decide
  rcases family_descends (prefixWord ++ tailWord_7928896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7928897 : List Nat := [1, 2, 5, 1, 4, 1, 2, 1, 1, 1, 4]
def baseStart_7928897 : Nat := 118140960795 + 7928897 * 2 ^ 59
def prefixEnd_7928897 : Nat := 4983230072969 + 3 ^ 40 * 7928897 * 2
def baseEnd_7928897 : Nat := 4071335220992169887723173

theorem tailTrace_7928897 : CollatzResearch.WordTrace tailWord_7928897 prefixEnd_7928897 4071335220992169887723173 := by
  unfold tailWord_7928897
  simp only [CollatzResearch.WordTrace]
  refine ⟨289190631555967791643496945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192793754370645194428997963 289190631555967791643496945)
  ·
    refine ⟨216892973666975843732622709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 289190631555967791643496945 216892973666975843732622709)
    ·
      refine ⟨20333716281278985349933379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 216892973666975843732622709 20333716281278985349933379)
      ·
        refine ⟨30500574421918478024900069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20333716281278985349933379 30500574421918478024900069)
        ·
          refine ⟨5718857704109714629668763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30500574421918478024900069 5718857704109714629668763)
          ·
            refine ⟨8578286556164571944503145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5718857704109714629668763 8578286556164571944503145)
            ·
              refine ⟨6433714917123428958377359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8578286556164571944503145 6433714917123428958377359)
              ·
                refine ⟨9650572375685143437566039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6433714917123428958377359 9650572375685143437566039)
                ·
                  refine ⟨14475858563527715156349059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9650572375685143437566039 14475858563527715156349059)
                  ·
                    refine ⟨21713787845291572734523589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14475858563527715156349059 21713787845291572734523589)
                    ·
                      refine ⟨4071335220992169887723173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21713787845291572734523589 4071335220992169887723173)
                      ·
                        rfl

theorem cell23_7928897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 1, 2, 1, 1, 1, 4].length) (baseStart_7928897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7928897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7928897 prefixEnd_7928897 := by exact prefixLift 7928897
  have htrace : WordTrace (prefixWord ++ tailWord_7928897) baseStart_7928897 baseEnd_7928897 := by
    simpa [prefixWord, tailWord_7928897, baseEnd_7928897] using wordTrace_append hprefix tailTrace_7928897
  have hstable : (prefixWord ++ tailWord_7928897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7928897).length < 2 ^ (prefixWord ++ tailWord_7928897).sum := by decide
  have hdescent : baseEnd_7928897 < baseStart_7928897 := by decide
  rcases family_descends (prefixWord ++ tailWord_7928897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7928913 : List Nat := [1, 2, 2, 1, 3, 1, 5, 2, 2, 1, 3]
def baseStart_7928913 : Nat := 118140960795 + 7928913 * 2 ^ 59
def prefixEnd_7928913 : Nat := 4983230072969 + 3 ^ 40 * 7928913 * 2
def baseEnd_7928913 : Nat := 4071343436682641825123099

theorem tailTrace_7928913 : CollatzResearch.WordTrace tailWord_7928913 prefixEnd_7928913 4071343436682641825123099 := by
  unfold tailWord_7928913
  simp only [CollatzResearch.WordTrace]
  refine ⟨289191215123909826376079393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192794143415939884250719595 289191215123909826376079393)
  ·
    refine ⟨216893411342932369782059545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 289191215123909826376079393 216893411342932369782059545)
    ·
      refine ⟨162670058507199277336544659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216893411342932369782059545 162670058507199277336544659)
      ·
        refine ⟨244005087760798916004816989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162670058507199277336544659 244005087760798916004816989)
        ·
          refine ⟨91501907910299593501806371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 244005087760798916004816989 91501907910299593501806371)
          ·
            refine ⟨137252861865449390252709557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91501907910299593501806371 137252861865449390252709557)
            ·
              refine ⟨12867455799885880336191521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 137252861865449390252709557 12867455799885880336191521)
              ·
                refine ⟨9650591849914410252143641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12867455799885880336191521 9650591849914410252143641)
                ·
                  refine ⟨7237943887435807689107731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9650591849914410252143641 7237943887435807689107731)
                  ·
                    refine ⟨10856915831153711533661597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7237943887435807689107731 10856915831153711533661597)
                    ·
                      refine ⟨4071343436682641825123099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10856915831153711533661597 4071343436682641825123099)
                      ·
                        rfl

theorem cell23_7928913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 5, 2, 2, 1, 3].length) (baseStart_7928913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7928913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7928913 prefixEnd_7928913 := by exact prefixLift 7928913
  have htrace : WordTrace (prefixWord ++ tailWord_7928913) baseStart_7928913 baseEnd_7928913 := by
    simpa [prefixWord, tailWord_7928913, baseEnd_7928913] using wordTrace_append hprefix tailTrace_7928913
  have hstable : (prefixWord ++ tailWord_7928913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7928913).length < 2 ^ (prefixWord ++ tailWord_7928913).sum := by decide
  have hdescent : baseEnd_7928913 < baseStart_7928913 := by decide
  rcases family_descends (prefixWord ++ tailWord_7928913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7928929 : List Nat := [1, 2, 3, 1, 1, 2, 4, 1, 2, 6]
def baseStart_7928929 : Nat := 118140960795 + 7928929 * 2 ^ 59
def prefixEnd_7928929 : Nat := 4983230072969 + 3 ^ 40 * 7928929 * 2
def baseEnd_7928929 : Nat := 1357117217457704587507675

theorem tailTrace_7928929 : CollatzResearch.WordTrace tailWord_7928929 prefixEnd_7928929 1357117217457704587507675 := by
  unfold tailWord_7928929
  simp only [CollatzResearch.WordTrace]
  refine ⟨289191798691851861108661841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192794532461234574072441227 289191798691851861108661841)
  ·
    refine ⟨216893849018888895831496381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 289191798691851861108661841 216893849018888895831496381)
    ·
      refine ⟨81335193382083335936811143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 216893849018888895831496381 81335193382083335936811143)
      ·
        refine ⟨122002790073125003905216715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81335193382083335936811143 122002790073125003905216715)
        ·
          refine ⟨183004185109687505857825073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122002790073125003905216715 183004185109687505857825073)
          ·
            refine ⟨137253138832265629393368805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 183004185109687505857825073 137253138832265629393368805)
            ·
              refine ⟨25734963531049805511256651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 137253138832265629393368805 25734963531049805511256651)
              ·
                refine ⟨38602445296574708266884977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25734963531049805511256651 38602445296574708266884977)
                ·
                  refine ⟨28951833972431031200163733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38602445296574708266884977 28951833972431031200163733)
                  ·
                    refine ⟨1357117217457704587507675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28951833972431031200163733 1357117217457704587507675)
                    ·
                      rfl

theorem cell23_7928929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 4, 1, 2, 6].length) (baseStart_7928929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7928929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7928929 prefixEnd_7928929 := by exact prefixLift 7928929
  have htrace : WordTrace (prefixWord ++ tailWord_7928929) baseStart_7928929 baseEnd_7928929 := by
    simpa [prefixWord, tailWord_7928929, baseEnd_7928929] using wordTrace_append hprefix tailTrace_7928929
  have hstable : (prefixWord ++ tailWord_7928929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7928929).length < 2 ^ (prefixWord ++ tailWord_7928929).sum := by decide
  have hdescent : baseEnd_7928929 < baseStart_7928929 := by decide
  rcases family_descends (prefixWord ++ tailWord_7928929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7928930 : List Nat := [3, 3, 2, 2, 1, 3, 1, 1, 1, 3, 3]
def baseStart_7928930 : Nat := 118140960795 + 7928930 * 2 ^ 59
def prefixEnd_7928930 : Nat := 4983230072969 + 3 ^ 40 * 7928930 * 2
def baseEnd_7928930 : Nat := 4071352165853768258610521

theorem tailTrace_7928930 : CollatzResearch.WordTrace tailWord_7928930 prefixEnd_7928930 4071352165853768258610521 := by
  unfold tailWord_7928930
  simp only [CollatzResearch.WordTrace]
  refine ⟨72297958791212059569862061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192794556776565492186298829 72297958791212059569862061)
  ·
    refine ⟨27111734546704522338698273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72297958791212059569862061 27111734546704522338698273)
    ·
      refine ⟨20333800910028391754023705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27111734546704522338698273 20333800910028391754023705)
      ·
        refine ⟨15250350682521293815517779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20333800910028391754023705 15250350682521293815517779)
        ·
          refine ⟨22875526023781940723276669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15250350682521293815517779 22875526023781940723276669)
          ·
            refine ⟨8578322258918227771228751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22875526023781940723276669 8578322258918227771228751)
            ·
              refine ⟨12867483388377341656843127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8578322258918227771228751 12867483388377341656843127)
              ·
                refine ⟨19301225082566012485264691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12867483388377341656843127 19301225082566012485264691)
                ·
                  refine ⟨28951837623849018727897037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19301225082566012485264691 28951837623849018727897037)
                  ·
                    refine ⟨10856939108943382022961389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28951837623849018727897037 10856939108943382022961389)
                    ·
                      refine ⟨4071352165853768258610521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10856939108943382022961389 4071352165853768258610521)
                      ·
                        rfl

theorem cell23_7928930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 3, 1, 1, 1, 3, 3].length) (baseStart_7928930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7928930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7928930 prefixEnd_7928930 := by exact prefixLift 7928930
  have htrace : WordTrace (prefixWord ++ tailWord_7928930) baseStart_7928930 baseEnd_7928930 := by
    simpa [prefixWord, tailWord_7928930, baseEnd_7928930] using wordTrace_append hprefix tailTrace_7928930
  have hstable : (prefixWord ++ tailWord_7928930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7928930).length < 2 ^ (prefixWord ++ tailWord_7928930).sum := by decide
  have hdescent : baseEnd_7928930 < baseStart_7928930 := by decide
  rcases family_descends (prefixWord ++ tailWord_7928930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7928970 : List Nat := [3, 1, 2, 3, 1, 1, 2, 4, 2, 2, 2]
def baseStart_7928970 : Nat := 118140960795 + 7928970 * 2 ^ 59
def prefixEnd_7928970 : Nat := 4983230072969 + 3 ^ 40 * 7928970 * 2
def baseEnd_7928970 : Nat := 4071372705079948102110337

theorem tailTrace_7928970 : CollatzResearch.WordTrace tailWord_7928970 prefixEnd_7928970 4071372705079948102110337 := by
  unfold tailWord_7928970
  simp only [CollatzResearch.WordTrace]
  refine ⟨72298323521175831277726091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192795529389802216740602909 72298323521175831277726091)
  ·
    refine ⟨108447485281763746916589137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72298323521175831277726091 108447485281763746916589137)
    ·
      refine ⟨81335613961322810187441853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108447485281763746916589137 81335613961322810187441853)
      ·
        refine ⟨30500855235496053820290695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81335613961322810187441853 30500855235496053820290695)
        ·
          refine ⟨45751282853244080730436043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30500855235496053820290695 45751282853244080730436043)
          ·
            refine ⟨68626924279866121095654065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45751282853244080730436043 68626924279866121095654065)
            ·
              refine ⟨51470193209899590821740549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68626924279866121095654065 51470193209899590821740549)
              ·
                refine ⟨9650661226856173279076353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51470193209899590821740549 9650661226856173279076353)
                ·
                  refine ⟨7237995920142129959307265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9650661226856173279076353 7237995920142129959307265)
                  ·
                    refine ⟨5428496940106597469480449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7237995920142129959307265 5428496940106597469480449)
                    ·
                      refine ⟨4071372705079948102110337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5428496940106597469480449 4071372705079948102110337)
                      ·
                        rfl

theorem cell23_7928970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 4, 2, 2, 2].length) (baseStart_7928970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7928970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7928970 prefixEnd_7928970 := by exact prefixLift 7928970
  have htrace : WordTrace (prefixWord ++ tailWord_7928970) baseStart_7928970 baseEnd_7928970 := by
    simpa [prefixWord, tailWord_7928970, baseEnd_7928970] using wordTrace_append hprefix tailTrace_7928970
  have hstable : (prefixWord ++ tailWord_7928970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7928970).length < 2 ^ (prefixWord ++ tailWord_7928970).sum := by decide
  have hdescent : baseEnd_7928970 < baseStart_7928970 := by decide
  rcases family_descends (prefixWord ++ tailWord_7928970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7929029 : List Nat := [1, 3, 1, 1, 1, 1, 3, 1, 1, 5, 5]
def baseStart_7929029 : Nat := 118140960795 + 7929029 * 2 ^ 59
def prefixEnd_7929029 : Nat := 4983230072969 + 3 ^ 40 * 7929029 * 2
def baseEnd_7929029 : Nat := 4071403000438563371272565

theorem tailTrace_7929029 : CollatzResearch.WordTrace tailWord_7929029 prefixEnd_7929029 4071403000438563371272565 := by
  unfold tailWord_7929029
  simp only [CollatzResearch.WordTrace]
  refine ⟨289195445991489578187302141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192796963994326385458201427 289195445991489578187302141)
  ·
    refine ⟨108448292246808591820238303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 289195445991489578187302141 108448292246808591820238303)
    ·
      refine ⟨162672438370212887730357455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108448292246808591820238303 162672438370212887730357455)
      ·
        refine ⟨244008657555319331595536183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162672438370212887730357455 244008657555319331595536183)
        ·
          refine ⟨366012986332978997393304275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 244008657555319331595536183 366012986332978997393304275)
          ·
            refine ⟨549019479499468496089956413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 366012986332978997393304275 549019479499468496089956413)
            ·
              refine ⟨205882304812300686033733655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 549019479499468496089956413 205882304812300686033733655)
              ·
                refine ⟨308823457218451029050600483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 205882304812300686033733655 308823457218451029050600483)
                ·
                  refine ⟨463235185827676543575900725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 308823457218451029050600483 463235185827676543575900725)
                  ·
                    refine ⟨43428298671344675960240693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 463235185827676543575900725 43428298671344675960240693)
                    ·
                      refine ⟨4071403000438563371272565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43428298671344675960240693 4071403000438563371272565)
                      ·
                        rfl

theorem cell23_7929029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 1, 1, 5, 5].length) (baseStart_7929029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7929029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7929029 prefixEnd_7929029 := by exact prefixLift 7929029
  have htrace : WordTrace (prefixWord ++ tailWord_7929029) baseStart_7929029 baseEnd_7929029 := by
    simpa [prefixWord, tailWord_7929029, baseEnd_7929029] using wordTrace_append hprefix tailTrace_7929029
  have hstable : (prefixWord ++ tailWord_7929029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7929029).length < 2 ^ (prefixWord ++ tailWord_7929029).sum := by decide
  have hdescent : baseEnd_7929029 < baseStart_7929029 := by decide
  rcases family_descends (prefixWord ++ tailWord_7929029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7929037 : List Nat := [1, 6, 2, 2, 1, 1, 1, 1, 2, 3, 3]
def baseStart_7929037 : Nat := 118140960795 + 7929037 * 2 ^ 59
def prefixEnd_7929037 : Nat := 4983230072969 + 3 ^ 40 * 7929037 * 2
def baseEnd_7929037 : Nat := 4071407108283799339972529

theorem tailTrace_7929037 : CollatzResearch.WordTrace tailWord_7929037 prefixEnd_7929037 4071407108283799339972529 := by
  unfold tailWord_7929037
  simp only [CollatzResearch.WordTrace]
  refine ⟨289195737775460595553593365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192797158516973730369062243 289195737775460595553593365)
  ·
    refine ⟨13556050208224715416574689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 289195737775460595553593365 13556050208224715416574689)
    ·
      refine ⟨10167037656168536562431017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13556050208224715416574689 10167037656168536562431017)
      ·
        refine ⟨7625278242126402421823263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10167037656168536562431017 7625278242126402421823263)
        ·
          refine ⟨11437917363189603632734895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7625278242126402421823263 11437917363189603632734895)
          ·
            refine ⟨17156876044784405449102343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11437917363189603632734895 17156876044784405449102343)
            ·
              refine ⟨25735314067176608173653515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17156876044784405449102343 25735314067176608173653515)
              ·
                refine ⟨38602971100764912260480273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25735314067176608173653515 38602971100764912260480273)
                ·
                  refine ⟨28952228325573684195360205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38602971100764912260480273 28952228325573684195360205)
                  ·
                    refine ⟨10857085622090131573260077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28952228325573684195360205 10857085622090131573260077)
                    ·
                      refine ⟨4071407108283799339972529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10857085622090131573260077 4071407108283799339972529)
                      ·
                        rfl

theorem cell23_7929037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 1, 1, 2, 3, 3].length) (baseStart_7929037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7929037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7929037 prefixEnd_7929037 := by exact prefixLift 7929037
  have htrace : WordTrace (prefixWord ++ tailWord_7929037) baseStart_7929037 baseEnd_7929037 := by
    simpa [prefixWord, tailWord_7929037, baseEnd_7929037] using wordTrace_append hprefix tailTrace_7929037
  have hstable : (prefixWord ++ tailWord_7929037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7929037).length < 2 ^ (prefixWord ++ tailWord_7929037).sum := by decide
  have hdescent : baseEnd_7929037 < baseStart_7929037 := by decide
  rcases family_descends (prefixWord ++ tailWord_7929037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7929039 : List Nat := [1, 1, 2, 1, 1, 3, 2, 1, 4, 1, 6]
def baseStart_7929039 : Nat := 118140960795 + 7929039 * 2 ^ 59
def prefixEnd_7929039 : Nat := 4983230072969 + 3 ^ 40 * 7929039 * 2
def baseEnd_7929039 : Nat := 4071408135245108332147519

theorem tailTrace_7929039 : CollatzResearch.WordTrace tailWord_7929039 prefixEnd_7929039 4071408135245108332147519 := by
  unfold tailWord_7929039
  simp only [CollatzResearch.WordTrace]
  refine ⟨289195810721453349895166171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192797207147635566596777447 289195810721453349895166171)
  ·
    refine ⟨433793716082180024842749257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289195810721453349895166171 433793716082180024842749257)
    ·
      refine ⟨325345287061635018632061943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 433793716082180024842749257 325345287061635018632061943)
      ·
        refine ⟨488017930592452527948092915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 325345287061635018632061943 488017930592452527948092915)
        ·
          refine ⟨732026895888678791922139373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 488017930592452527948092915 732026895888678791922139373)
          ·
            refine ⟨274510085958254546970802265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 732026895888678791922139373 274510085958254546970802265)
            ·
              refine ⟨205882564468690910228101699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 274510085958254546970802265 205882564468690910228101699)
              ·
                refine ⟨308823846703036365342152549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 205882564468690910228101699 308823846703036365342152549)
                ·
                  refine ⟨57904471256819318501653603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 308823846703036365342152549 57904471256819318501653603)
                  ·
                    refine ⟨86856706885228977752480405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 57904471256819318501653603 86856706885228977752480405)
                    ·
                      refine ⟨4071408135245108332147519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 86856706885228977752480405 4071408135245108332147519)
                      ·
                        rfl

theorem cell23_7929039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 1, 4, 1, 6].length) (baseStart_7929039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7929039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7929039 prefixEnd_7929039 := by exact prefixLift 7929039
  have htrace : WordTrace (prefixWord ++ tailWord_7929039) baseStart_7929039 baseEnd_7929039 := by
    simpa [prefixWord, tailWord_7929039, baseEnd_7929039] using wordTrace_append hprefix tailTrace_7929039
  have hstable : (prefixWord ++ tailWord_7929039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7929039).length < 2 ^ (prefixWord ++ tailWord_7929039).sum := by decide
  have hdescent : baseEnd_7929039 < baseStart_7929039 := by decide
  rcases family_descends (prefixWord ++ tailWord_7929039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7929049 : List Nat := [1, 2, 1, 2, 3, 1, 1, 2, 10]
def baseStart_7929049 : Nat := 118140960795 + 7929049 * 2 ^ 59
def prefixEnd_7929049 : Nat := 4983230072969 + 3 ^ 40 * 7929049 * 2
def baseEnd_7929049 : Nat := 452379252227961477002497

theorem tailTrace_7929049 : CollatzResearch.WordTrace tailWord_7929049 prefixEnd_7929049 452379252227961477002497 := by
  unfold tailWord_7929049
  simp only [CollatzResearch.WordTrace]
  refine ⟨289196175451417121603030201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192797450300944747735353467 289196175451417121603030201)
  ·
    refine ⟨216897131588562841202272651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 289196175451417121603030201 216897131588562841202272651)
    ·
      refine ⟨325345697382844261803408977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216897131588562841202272651 325345697382844261803408977)
      ·
        refine ⟨244009273037133196352556733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 325345697382844261803408977 244009273037133196352556733)
        ·
          refine ⟨91503477388924948632208775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 244009273037133196352556733 91503477388924948632208775)
          ·
            refine ⟨137255216083387422948313163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91503477388924948632208775 137255216083387422948313163)
            ·
              refine ⟨205882824125081134422469745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137255216083387422948313163 205882824125081134422469745)
              ·
                refine ⟨154412118093810850816852309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 205882824125081134422469745 154412118093810850816852309)
                ·
                  refine ⟨452379252227961477002497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 154412118093810850816852309 452379252227961477002497)
                  ·
                    rfl

theorem cell23_7929049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 2, 10].length) (baseStart_7929049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7929049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7929049 prefixEnd_7929049 := by exact prefixLift 7929049
  have htrace : WordTrace (prefixWord ++ tailWord_7929049) baseStart_7929049 baseEnd_7929049 := by
    simpa [prefixWord, tailWord_7929049, baseEnd_7929049] using wordTrace_append hprefix tailTrace_7929049
  have hstable : (prefixWord ++ tailWord_7929049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7929049).length < 2 ^ (prefixWord ++ tailWord_7929049).sum := by decide
  have hdescent : baseEnd_7929049 < baseStart_7929049 := by decide
  rcases family_descends (prefixWord ++ tailWord_7929049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7929070 : List Nat := [4, 1, 2, 1, 1, 1, 3, 5, 1, 4]
def baseStart_7929070 : Nat := 118140960795 + 7929070 * 2 ^ 59
def prefixEnd_7929070 : Nat := 4983230072969 + 3 ^ 40 * 7929070 * 2
def baseEnd_7929070 : Nat := 1357141351048465903619959

theorem tailTrace_7929070 : CollatzResearch.WordTrace tailWord_7929070 prefixEnd_7929070 1357141351048465903619959 := by
  unfold tailWord_7929070
  simp only [CollatzResearch.WordTrace]
  refine ⟨36149617673042630273693083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 192797960922894028126363109 36149617673042630273693083)
  ·
    refine ⟨54224426509563945410539625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36149617673042630273693083 54224426509563945410539625)
    ·
      refine ⟨40668319882172959057904719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54224426509563945410539625 40668319882172959057904719)
      ·
        refine ⟨61002479823259438586857079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40668319882172959057904719 61002479823259438586857079)
        ·
          refine ⟨91503719734889157880285619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61002479823259438586857079 91503719734889157880285619)
          ·
            refine ⟨137255579602333736820428429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91503719734889157880285619 137255579602333736820428429)
            ·
              refine ⟨51470842350875151307660661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 137255579602333736820428429 51470842350875151307660661)
              ·
                refine ⟨4825391470394545435093187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 51470842350875151307660661 4825391470394545435093187)
                ·
                  refine ⟨7238087205591818152639781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4825391470394545435093187 7238087205591818152639781)
                  ·
                    refine ⟨1357141351048465903619959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7238087205591818152639781 1357141351048465903619959)
                    ·
                      rfl

theorem cell23_7929070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 5, 1, 4].length) (baseStart_7929070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7929070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7929070 prefixEnd_7929070 := by exact prefixLift 7929070
  have htrace : WordTrace (prefixWord ++ tailWord_7929070) baseStart_7929070 baseEnd_7929070 := by
    simpa [prefixWord, tailWord_7929070, baseEnd_7929070] using wordTrace_append hprefix tailTrace_7929070
  have hstable : (prefixWord ++ tailWord_7929070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7929070).length < 2 ^ (prefixWord ++ tailWord_7929070).sum := by decide
  have hdescent : baseEnd_7929070 < baseStart_7929070 := by decide
  rcases family_descends (prefixWord ++ tailWord_7929070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7929130 : List Nat := [3, 1, 4, 2, 1, 1, 2, 3, 1, 5]
def baseStart_7929130 : Nat := 118140960795 + 7929130 * 2 ^ 59
def prefixEnd_7929130 : Nat := 4983230072969 + 3 ^ 40 * 7929130 * 2
def baseEnd_7929130 : Nat := 1357151620661555825369867

theorem tailTrace_7929130 : CollatzResearch.WordTrace tailWord_7929130 prefixEnd_7929130 1357151620661555825369867 := by
  unfold tailWord_7929130
  simp only [CollatzResearch.WordTrace]
  refine ⟨72299782441030918109182211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192799419842749114957819229 72299782441030918109182211)
  ·
    refine ⟨108449673661546377163773317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72299782441030918109182211 108449673661546377163773317)
    ·
      refine ⟨20334313811539945718207497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 108449673661546377163773317 20334313811539945718207497)
      ·
        refine ⟨15250735358654959288655623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20334313811539945718207497 15250735358654959288655623)
        ·
          refine ⟨22876103037982438932983435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15250735358654959288655623 22876103037982438932983435)
          ·
            refine ⟨34314154556973658399475153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22876103037982438932983435 34314154556973658399475153)
            ·
              refine ⟨25735615917730243799606365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34314154556973658399475153 25735615917730243799606365)
              ·
                refine ⟨9650855969148841424852387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25735615917730243799606365 9650855969148841424852387)
                ·
                  refine ⟨14476283953723262137278581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9650855969148841424852387 14476283953723262137278581)
                  ·
                    refine ⟨1357151620661555825369867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14476283953723262137278581 1357151620661555825369867)
                    ·
                      rfl

theorem cell23_7929130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 2, 3, 1, 5].length) (baseStart_7929130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7929130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7929130 prefixEnd_7929130 := by exact prefixLift 7929130
  have htrace : WordTrace (prefixWord ++ tailWord_7929130) baseStart_7929130 baseEnd_7929130 := by
    simpa [prefixWord, tailWord_7929130, baseEnd_7929130] using wordTrace_append hprefix tailTrace_7929130
  have hstable : (prefixWord ++ tailWord_7929130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7929130).length < 2 ^ (prefixWord ++ tailWord_7929130).sum := by decide
  have hdescent : baseEnd_7929130 < baseStart_7929130 := by decide
  rcases family_descends (prefixWord ++ tailWord_7929130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7929146 : List Nat := [3, 1, 1, 1, 4, 1, 1, 1, 3, 1, 6]
def baseStart_7929146 : Nat := 118140960795 + 7929146 * 2 ^ 59
def prefixEnd_7929146 : Nat := 4983230072969 + 3 ^ 40 * 7929146 * 2
def baseEnd_7929146 : Nat := 4071463077675139413509527

theorem tailTrace_7929146 : CollatzResearch.WordTrace tailWord_7929146 prefixEnd_7929146 4071463077675139413509527 := by
  unfold tailWord_7929146
  simp only [CollatzResearch.WordTrace]
  refine ⟨72299928333016426792327823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192799808888043804779540861 72299928333016426792327823)
  ·
    refine ⟨108449892499524640188491735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72299928333016426792327823 108449892499524640188491735)
    ·
      refine ⟨162674838749286960282737603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108449892499524640188491735 162674838749286960282737603)
      ·
        refine ⟨244012258123930440424106405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162674838749286960282737603 244012258123930440424106405)
        ·
          refine ⟨45752298398236957579519951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 244012258123930440424106405 45752298398236957579519951)
          ·
            refine ⟨68628447597355436369279927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45752298398236957579519951 68628447597355436369279927)
            ·
              refine ⟨102942671396033154553919891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68628447597355436369279927 102942671396033154553919891)
              ·
                refine ⟨154414007094049731830879837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102942671396033154553919891 154414007094049731830879837)
                ·
                  refine ⟨57905252660268649436579939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 154414007094049731830879837 57905252660268649436579939)
                  ·
                    refine ⟨86857878990402974154869909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 57905252660268649436579939 86857878990402974154869909)
                    ·
                      refine ⟨4071463077675139413509527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 86857878990402974154869909 4071463077675139413509527)
                      ·
                        rfl

theorem cell23_7929146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 1, 3, 1, 6].length) (baseStart_7929146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7929146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7929146 prefixEnd_7929146 := by exact prefixLift 7929146
  have htrace : WordTrace (prefixWord ++ tailWord_7929146) baseStart_7929146 baseEnd_7929146 := by
    simpa [prefixWord, tailWord_7929146, baseEnd_7929146] using wordTrace_append hprefix tailTrace_7929146
  have hstable : (prefixWord ++ tailWord_7929146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7929146).length < 2 ^ (prefixWord ++ tailWord_7929146).sum := by decide
  have hdescent : baseEnd_7929146 < baseStart_7929146 := by decide
  rcases family_descends (prefixWord ++ tailWord_7929146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7929181 : List Nat := [1, 4, 5, 1, 1, 1, 3, 1, 1, 5]
def baseStart_7929181 : Nat := 118140960795 + 7929181 * 2 ^ 59
def prefixEnd_7929181 : Nat := 4983230072969 + 3 ^ 40 * 7929181 * 2
def baseEnd_7929181 : Nat := 1357160349832682258857289

theorem tailTrace_7929181 : CollatzResearch.WordTrace tailWord_7929181 prefixEnd_7929181 1357160349832682258857289 := by
  unfold tailWord_7929181
  simp only [CollatzResearch.WordTrace]
  refine ⟨289200989886938908146835397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192800659924625938764556931 289200989886938908146835397)
  ·
    refine ⟨54225185603801045277531637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 289200989886938908146835397 54225185603801045277531637)
    ·
      refine ⟨5083611150356347994768591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 54225185603801045277531637 5083611150356347994768591)
      ·
        refine ⟨7625416725534521992152887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5083611150356347994768591 7625416725534521992152887)
        ·
          refine ⟨11438125088301782988229331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7625416725534521992152887 11438125088301782988229331)
          ·
            refine ⟨17157187632452674482343997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11438125088301782988229331 17157187632452674482343997)
            ·
              refine ⟨6433945362169752930878999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17157187632452674482343997 6433945362169752930878999)
              ·
                refine ⟨9650918043254629396318499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6433945362169752930878999 9650918043254629396318499)
                ·
                  refine ⟨14476377064881944094477749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9650918043254629396318499 14476377064881944094477749)
                  ·
                    refine ⟨1357160349832682258857289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14476377064881944094477749 1357160349832682258857289)
                    ·
                      rfl

theorem cell23_7929181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 3, 1, 1, 5].length) (baseStart_7929181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7929181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7929181 prefixEnd_7929181 := by exact prefixLift 7929181
  have htrace : WordTrace (prefixWord ++ tailWord_7929181) baseStart_7929181 baseEnd_7929181 := by
    simpa [prefixWord, tailWord_7929181, baseEnd_7929181] using wordTrace_append hprefix tailTrace_7929181
  have hstable : (prefixWord ++ tailWord_7929181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7929181).length < 2 ^ (prefixWord ++ tailWord_7929181).sum := by decide
  have hdescent : baseEnd_7929181 < baseStart_7929181 := by decide
  rcases family_descends (prefixWord ++ tailWord_7929181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7929187 : List Nat := [1, 1, 1, 5, 2, 3, 3, 1, 1, 2, 3]
def baseStart_7929187 : Nat := 118140960795 + 7929187 * 2 ^ 59
def prefixEnd_7929187 : Nat := 4983230072969 + 3 ^ 40 * 7929187 * 2
def baseEnd_7929187 : Nat := 4071484130381973753096839

theorem tailTrace_7929187 : CollatzResearch.WordTrace tailWord_7929187 prefixEnd_7929187 4071484130381973753096839 := by
  unfold tailWord_7929187
  simp only [CollatzResearch.WordTrace]
  refine ⟨289201208724917171171553815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192800805816611447447702543 289201208724917171171553815)
  ·
    refine ⟨433801813087375756757330723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289201208724917171171553815 433801813087375756757330723)
    ·
      refine ⟨650702719631063635135996085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 433801813087375756757330723 650702719631063635135996085)
      ·
        refine ⟨61003379965412215793999633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 650702719631063635135996085 61003379965412215793999633)
        ·
          refine ⟨45752534974059161845499725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61003379965412215793999633 45752534974059161845499725)
          ·
            refine ⟨17157200615272185692062397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45752534974059161845499725 17157200615272185692062397)
            ·
              refine ⟨6433950230727069634523399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17157200615272185692062397 6433950230727069634523399)
              ·
                refine ⟨9650925346090604451785099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6433950230727069634523399 9650925346090604451785099)
                ·
                  refine ⟨14476388019135906677677649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9650925346090604451785099 14476388019135906677677649)
                  ·
                    refine ⟨10857291014351930008258237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14476388019135906677677649 10857291014351930008258237)
                    ·
                      refine ⟨4071484130381973753096839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10857291014351930008258237 4071484130381973753096839)
                      ·
                        rfl

theorem cell23_7929187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 3, 1, 1, 2, 3].length) (baseStart_7929187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7929187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7929187 prefixEnd_7929187 := by exact prefixLift 7929187
  have htrace : WordTrace (prefixWord ++ tailWord_7929187) baseStart_7929187 baseEnd_7929187 := by
    simpa [prefixWord, tailWord_7929187, baseEnd_7929187] using wordTrace_append hprefix tailTrace_7929187
  have hstable : (prefixWord ++ tailWord_7929187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7929187).length < 2 ^ (prefixWord ++ tailWord_7929187).sum := by decide
  have hdescent : baseEnd_7929187 < baseStart_7929187 := by decide
  rcases family_descends (prefixWord ++ tailWord_7929187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7929214 : List Nat := [4, 2, 3, 2, 1, 1, 2, 1, 1, 2, 4]
def baseStart_7929214 : Nat := 118140960795 + 7929214 * 2 ^ 59
def prefixEnd_7929214 : Nat := 4983230072969 + 3 ^ 40 * 7929214 * 2
def baseEnd_7929214 : Nat := 4071497994359645147459215

theorem tailTrace_7929214 : CollatzResearch.WordTrace tailWord_7929214 prefixEnd_7929214 4071497994359645147459215 := by
  unfold tailWord_7929214
  simp only [CollatzResearch.WordTrace]
  refine ⟨36150274186977419347848337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 192801462330546236521857797 36150274186977419347848337)
  ·
    refine ⟨27112705640233064510886253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36150274186977419347848337 27112705640233064510886253)
    ·
      refine ⟨10167264615087399191582345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27112705640233064510886253 10167264615087399191582345)
      ·
        refine ⟨7625448461315549393686759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10167264615087399191582345 7625448461315549393686759)
        ·
          refine ⟨11438172691973324090530139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7625448461315549393686759 11438172691973324090530139)
          ·
            refine ⟨17157259037959986135795209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11438172691973324090530139 17157259037959986135795209)
            ·
              refine ⟨12867944278469989601846407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17157259037959986135795209 12867944278469989601846407)
              ·
                refine ⟨19301916417704984402769611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12867944278469989601846407 19301916417704984402769611)
                ·
                  refine ⟨28952874626557476604154417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19301916417704984402769611 28952874626557476604154417)
                  ·
                    refine ⟨21714655969918107453115813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28952874626557476604154417 21714655969918107453115813)
                    ·
                      refine ⟨4071497994359645147459215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21714655969918107453115813 4071497994359645147459215)
                      ·
                        rfl

theorem cell23_7929214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 2, 1, 1, 2, 4].length) (baseStart_7929214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7929214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7929214 prefixEnd_7929214 := by exact prefixLift 7929214
  have htrace : WordTrace (prefixWord ++ tailWord_7929214) baseStart_7929214 baseEnd_7929214 := by
    simpa [prefixWord, tailWord_7929214, baseEnd_7929214] using wordTrace_append hprefix tailTrace_7929214
  have hstable : (prefixWord ++ tailWord_7929214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7929214).length < 2 ^ (prefixWord ++ tailWord_7929214).sum := by decide
  have hdescent : baseEnd_7929214 < baseStart_7929214 := by decide
  rcases family_descends (prefixWord ++ tailWord_7929214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7929217 : List Nat := [1, 2, 4, 3, 2, 1, 2, 1, 1, 3, 3]
def baseStart_7929217 : Nat := 118140960795 + 7929217 * 2 ^ 59
def prefixEnd_7929217 : Nat := 4983230072969 + 3 ^ 40 * 7929217 * 2
def baseEnd_7929217 : Nat := 4071499534801608635721701

theorem tailTrace_7929217 : CollatzResearch.WordTrace tailWord_7929217 prefixEnd_7929217 4071499534801608635721701 := by
  unfold tailWord_7929217
  simp only [CollatzResearch.WordTrace]
  refine ⟨289202302914808486295145905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192801535276538990863430603 289202302914808486295145905)
  ·
    refine ⟨216901727186106364721359429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 289202302914808486295145905 216901727186106364721359429)
    ·
      refine ⟨40669073847394943385254893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 216901727186106364721359429 40669073847394943385254893)
      ·
        refine ⟨15250902692773103769470585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40669073847394943385254893 15250902692773103769470585)
        ·
          refine ⟨11438177019579827827102939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15250902692773103769470585 11438177019579827827102939)
          ·
            refine ⟨17157265529369741740654409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11438177019579827827102939 17157265529369741740654409)
            ·
              refine ⟨12867949147027306305490807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17157265529369741740654409 12867949147027306305490807)
              ·
                refine ⟨19301923720540959458236211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12867949147027306305490807 19301923720540959458236211)
                ·
                  refine ⟨28952885580811439187354317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19301923720540959458236211 28952885580811439187354317)
                  ·
                    refine ⟨10857332092804289695257869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28952885580811439187354317 10857332092804289695257869)
                    ·
                      refine ⟨4071499534801608635721701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10857332092804289695257869 4071499534801608635721701)
                      ·
                        rfl

theorem cell23_7929217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 2, 1, 1, 3, 3].length) (baseStart_7929217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7929217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7929217 prefixEnd_7929217 := by exact prefixLift 7929217
  have htrace : WordTrace (prefixWord ++ tailWord_7929217) baseStart_7929217 baseEnd_7929217 := by
    simpa [prefixWord, tailWord_7929217, baseEnd_7929217] using wordTrace_append hprefix tailTrace_7929217
  have hstable : (prefixWord ++ tailWord_7929217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7929217).length < 2 ^ (prefixWord ++ tailWord_7929217).sum := by decide
  have hdescent : baseEnd_7929217 < baseStart_7929217 := by decide
  rcases family_descends (prefixWord ++ tailWord_7929217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7929325 : List Nat := [1, 5, 1, 3, 3, 1, 2, 1, 2, 2, 2]
def baseStart_7929325 : Nat := 118140960795 + 7929325 * 2 ^ 59
def prefixEnd_7929325 : Nat := 4983230072969 + 3 ^ 40 * 7929325 * 2
def baseEnd_7929325 : Nat := 4071554990712294213171205

theorem tailTrace_7929325 : CollatzResearch.WordTrace tailWord_7929325 prefixEnd_7929325 4071554990712294213171205 := by
  unfold tailWord_7929325
  simp only [CollatzResearch.WordTrace]
  refine ⟨289206241998417220740077429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192804161332278147160051619 289206241998417220740077429)
  ·
    refine ⟨27113085187351614444382259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 289206241998417220740077429 27113085187351614444382259)
    ·
      refine ⟨40669627781027421666573389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27113085187351614444382259 40669627781027421666573389)
      ·
        refine ⟨15251110417885283124965021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40669627781027421666573389 15251110417885283124965021)
        ·
          refine ⟨5719166406706981171861883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15251110417885283124965021 5719166406706981171861883)
          ·
            refine ⟨8578749610060471757792825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5719166406706981171861883 8578749610060471757792825)
            ·
              refine ⟨6434062207545353818344619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8578749610060471757792825 6434062207545353818344619)
              ·
                refine ⟨9651093311318030727516929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6434062207545353818344619 9651093311318030727516929)
                ·
                  refine ⟨7238319983488523045637697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9651093311318030727516929 7238319983488523045637697)
                  ·
                    refine ⟨5428739987616392284228273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7238319983488523045637697 5428739987616392284228273)
                    ·
                      refine ⟨4071554990712294213171205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5428739987616392284228273 4071554990712294213171205)
                      ·
                        rfl

theorem cell23_7929325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 1, 2, 1, 2, 2, 2].length) (baseStart_7929325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7929325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7929325 prefixEnd_7929325 := by exact prefixLift 7929325
  have htrace : WordTrace (prefixWord ++ tailWord_7929325) baseStart_7929325 baseEnd_7929325 := by
    simpa [prefixWord, tailWord_7929325, baseEnd_7929325] using wordTrace_append hprefix tailTrace_7929325
  have hstable : (prefixWord ++ tailWord_7929325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7929325).length < 2 ^ (prefixWord ++ tailWord_7929325).sum := by decide
  have hdescent : baseEnd_7929325 < baseStart_7929325 := by decide
  rcases family_descends (prefixWord ++ tailWord_7929325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7929340 : List Nat := [2, 2, 2, 1, 2, 1, 2, 4, 3, 4]
def baseStart_7929340 : Nat := 118140960795 + 7929340 * 2 ^ 59
def prefixEnd_7929340 : Nat := 4983230072969 + 3 ^ 40 * 7929340 * 2
def baseEnd_7929340 : Nat := 1357187564307370551494545

theorem tailTrace_7929340 : CollatzResearch.WordTrace tailWord_7929340 prefixEnd_7929340 1357187564307370551494545 := by
  unfold tailWord_7929340
  simp only [CollatzResearch.WordTrace]
  refine ⟨144603394546681439150936737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192804526062241918867915649 144603394546681439150936737)
  ·
    refine ⟨108452545910011079363202553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144603394546681439150936737 108452545910011079363202553)
    ·
      refine ⟨81339409432508309522401915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108452545910011079363202553 81339409432508309522401915)
      ·
        refine ⟨122009114148762464283602873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81339409432508309522401915 122009114148762464283602873)
        ·
          refine ⟨91506835611571848212702155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122009114148762464283602873 91506835611571848212702155)
          ·
            refine ⟨137260253417357772319053233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91506835611571848212702155 137260253417357772319053233)
            ·
              refine ⟨102945190063018329239289925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137260253417357772319053233 102945190063018329239289925)
              ·
                refine ⟨19302223136815936732366861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 102945190063018329239289925 19302223136815936732366861)
                ·
                  refine ⟨7238333676305976274637573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19302223136815936732366861 7238333676305976274637573)
                  ·
                    refine ⟨1357187564307370551494545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7238333676305976274637573 1357187564307370551494545)
                    ·
                      rfl

theorem cell23_7929340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 4, 3, 4].length) (baseStart_7929340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7929340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7929340 prefixEnd_7929340 := by exact prefixLift 7929340
  have htrace : WordTrace (prefixWord ++ tailWord_7929340) baseStart_7929340 baseEnd_7929340 := by
    simpa [prefixWord, tailWord_7929340, baseEnd_7929340] using wordTrace_append hprefix tailTrace_7929340
  have hstable : (prefixWord ++ tailWord_7929340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7929340).length < 2 ^ (prefixWord ++ tailWord_7929340).sum := by decide
  have hdescent : baseEnd_7929340 < baseStart_7929340 := by decide
  rcases family_descends (prefixWord ++ tailWord_7929340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7929393 : List Nat := [1, 2, 2, 3, 1, 1, 1, 1, 1, 3, 7]
def baseStart_7929393 : Nat := 118140960795 + 7929393 * 2 ^ 59
def prefixEnd_7929393 : Nat := 4983230072969 + 3 ^ 40 * 7929393 * 2
def baseEnd_7929393 : Nat := 4071589907396799947120891

theorem tailTrace_7929393 : CollatzResearch.WordTrace tailWord_7929393 prefixEnd_7929393 4071589907396799947120891 := by
  unfold tailWord_7929393
  simp only [CollatzResearch.WordTrace]
  refine ⟨289208722162170868353552833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192805814774780578902368555 289208722162170868353552833)
  ·
    refine ⟨216906541621628151265164625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 289208722162170868353552833 216906541621628151265164625)
    ·
      refine ⟨162679906216221113448873469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216906541621628151265164625 162679906216221113448873469)
      ·
        refine ⟨61004964831082917543327551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 162679906216221113448873469 61004964831082917543327551)
        ·
          refine ⟨91507447246624376314991327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61004964831082917543327551 91507447246624376314991327)
          ·
            refine ⟨137261170869936564472486991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91507447246624376314991327 137261170869936564472486991)
            ·
              refine ⟨205891756304904846708730487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137261170869936564472486991 205891756304904846708730487)
              ·
                refine ⟨308837634457357270063095731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 205891756304904846708730487 308837634457357270063095731)
                ·
                  refine ⟨463256451686035905094643597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 308837634457357270063095731 463256451686035905094643597)
                  ·
                    refine ⟨173721169382263464410491349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 463256451686035905094643597 173721169382263464410491349)
                    ·
                      refine ⟨4071589907396799947120891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 173721169382263464410491349 4071589907396799947120891)
                      ·
                        rfl

theorem cell23_7929393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 1, 1, 3, 7].length) (baseStart_7929393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7929393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7929393 prefixEnd_7929393 := by exact prefixLift 7929393
  have htrace : WordTrace (prefixWord ++ tailWord_7929393) baseStart_7929393 baseEnd_7929393 := by
    simpa [prefixWord, tailWord_7929393, baseEnd_7929393] using wordTrace_append hprefix tailTrace_7929393
  have hstable : (prefixWord ++ tailWord_7929393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7929393).length < 2 ^ (prefixWord ++ tailWord_7929393).sum := by decide
  have hdescent : baseEnd_7929393 < baseStart_7929393 := by decide
  rcases family_descends (prefixWord ++ tailWord_7929393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7929397 : List Nat := [1, 3, 3, 1, 1, 3, 1, 1, 5, 1, 3]
def baseStart_7929397 : Nat := 118140960795 + 7929397 * 2 ^ 59
def prefixEnd_7929397 : Nat := 4983230072969 + 3 ^ 40 * 7929397 * 2
def baseEnd_7929397 : Nat := 4071591961319417931470873

theorem tailTrace_7929397 : CollatzResearch.WordTrace tailWord_7929397 prefixEnd_7929397 4071591961319417931470873 := by
  unfold tailWord_7929397
  simp only [CollatzResearch.WordTrace]
  refine ⟨289208868054156377036698445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192805912036104251357798963 289208868054156377036698445)
  ·
    refine ⟨108453325520308641388761917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 289208868054156377036698445 108453325520308641388761917)
    ·
      refine ⟨40669997070115740520785719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108453325520308641388761917 40669997070115740520785719)
      ·
        refine ⟨61004995605173610781178579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40669997070115740520785719 61004995605173610781178579)
        ·
          refine ⟨91507493407760416171767869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61004995605173610781178579 91507493407760416171767869)
          ·
            refine ⟨34315310027910156064412951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91507493407760416171767869 34315310027910156064412951)
            ·
              refine ⟨51472965041865234096619427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34315310027910156064412951 51472965041865234096619427)
              ·
                refine ⟨77209447562797851144929141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51472965041865234096619427 77209447562797851144929141)
                ·
                  refine ⟨7238385709012298544837107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 77209447562797851144929141 7238385709012298544837107)
                  ·
                    refine ⟨10857578563518447817255661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7238385709012298544837107 10857578563518447817255661)
                    ·
                      refine ⟨4071591961319417931470873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10857578563518447817255661 4071591961319417931470873)
                      ·
                        rfl

theorem cell23_7929397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 1, 5, 1, 3].length) (baseStart_7929397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7929397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7929397 prefixEnd_7929397 := by exact prefixLift 7929397
  have htrace : WordTrace (prefixWord ++ tailWord_7929397) baseStart_7929397 baseEnd_7929397 := by
    simpa [prefixWord, tailWord_7929397, baseEnd_7929397] using wordTrace_append hprefix tailTrace_7929397
  have hstable : (prefixWord ++ tailWord_7929397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7929397).length < 2 ^ (prefixWord ++ tailWord_7929397).sum := by decide
  have hdescent : baseEnd_7929397 < baseStart_7929397 := by decide
  rcases family_descends (prefixWord ++ tailWord_7929397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7929400 : List Nat := [2, 1, 2, 1, 4, 2, 2, 1, 3, 5]
def baseStart_7929400 : Nat := 118140960795 + 7929400 * 2 ^ 59
def prefixEnd_7929400 : Nat := 4983230072969 + 3 ^ 40 * 7929400 * 2
def baseEnd_7929400 : Nat := 1357197833920460473244453

theorem tailTrace_7929400 : CollatzResearch.WordTrace tailWord_7929400 prefixEnd_7929400 1357197833920460473244453 := by
  unfold tailWord_7929400
  simp only [CollatzResearch.WordTrace]
  refine ⟨144604488736572754274528827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192805984982097005699371769 144604488736572754274528827)
  ·
    refine ⟨216906733104859131411793241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144604488736572754274528827 216906733104859131411793241)
    ·
      refine ⟨162680049828644348558844931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216906733104859131411793241 162680049828644348558844931)
      ·
        refine ⟨244020074742966522838267397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162680049828644348558844931 244020074742966522838267397)
        ·
          refine ⟨45753764014306223032175137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 244020074742966522838267397 45753764014306223032175137)
          ·
            refine ⟨34315323010729667274131353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45753764014306223032175137 34315323010729667274131353)
            ·
              refine ⟨25736492258047250455598515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34315323010729667274131353 25736492258047250455598515)
              ·
                refine ⟨38604738387070875683397773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25736492258047250455598515 38604738387070875683397773)
                ·
                  refine ⟨14476776895151578381274165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38604738387070875683397773 14476776895151578381274165)
                  ·
                    refine ⟨1357197833920460473244453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14476776895151578381274165 1357197833920460473244453)
                    ·
                      rfl

theorem cell23_7929400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 1, 3, 5].length) (baseStart_7929400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7929400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7929400 prefixEnd_7929400 := by exact prefixLift 7929400
  have htrace : WordTrace (prefixWord ++ tailWord_7929400) baseStart_7929400 baseEnd_7929400 := by
    simpa [prefixWord, tailWord_7929400, baseEnd_7929400] using wordTrace_append hprefix tailTrace_7929400
  have hstable : (prefixWord ++ tailWord_7929400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7929400).length < 2 ^ (prefixWord ++ tailWord_7929400).sum := by decide
  have hdescent : baseEnd_7929400 < baseStart_7929400 := by decide
  rcases family_descends (prefixWord ++ tailWord_7929400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7929407 : List Nat := [1, 1, 2, 2, 3, 4, 1, 1, 1, 5, 2]
def baseStart_7929407 : Nat := 118140960795 + 7929407 * 2 ^ 59
def prefixEnd_7929407 : Nat := 4983230072969 + 3 ^ 40 * 7929407 * 2
def baseEnd_7929407 : Nat := 4071597096125962892345827

theorem tailTrace_7929407 : CollatzResearch.WordTrace tailWord_7929407 prefixEnd_7929407 4071597096125962892345827 := by
  unfold tailWord_7929407
  simp only [CollatzResearch.WordTrace]
  refine ⟨289209232784120148744562475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192806155189413432496374983 289209232784120148744562475)
  ·
    refine ⟨433813849176180223116843713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289209232784120148744562475 433813849176180223116843713)
    ·
      refine ⟨325360386882135167337632785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 433813849176180223116843713 325360386882135167337632785)
      ·
        refine ⟨244020290161601375503224589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 325360386882135167337632785 244020290161601375503224589)
        ·
          refine ⟨91507608810600515813709221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 244020290161601375503224589 91507608810600515813709221)
          ·
            refine ⟨17157676651987596715070479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 91507608810600515813709221 17157676651987596715070479)
            ·
              refine ⟨25736514977981395072605719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17157676651987596715070479 25736514977981395072605719)
              ·
                refine ⟨38604772466972092608908579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25736514977981395072605719 38604772466972092608908579)
                ·
                  refine ⟨57907158700458138913362869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38604772466972092608908579 57907158700458138913362869)
                  ·
                    refine ⟨5428796128167950523127769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 57907158700458138913362869 5428796128167950523127769)
                    ·
                      refine ⟨4071597096125962892345827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5428796128167950523127769 4071597096125962892345827)
                      ·
                        rfl

theorem cell23_7929407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 1, 1, 1, 5, 2].length) (baseStart_7929407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7929407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7929407 prefixEnd_7929407 := by exact prefixLift 7929407
  have htrace : WordTrace (prefixWord ++ tailWord_7929407) baseStart_7929407 baseEnd_7929407 := by
    simpa [prefixWord, tailWord_7929407, baseEnd_7929407] using wordTrace_append hprefix tailTrace_7929407
  have hstable : (prefixWord ++ tailWord_7929407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7929407).length < 2 ^ (prefixWord ++ tailWord_7929407).sum := by decide
  have hdescent : baseEnd_7929407 < baseStart_7929407 := by decide
  rcases family_descends (prefixWord ++ tailWord_7929407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7929421 : List Nat := [1, 6, 1, 1, 4, 1, 1, 2, 6]
def baseStart_7929421 : Nat := 118140960795 + 7929421 * 2 ^ 59
def prefixEnd_7929421 : Nat := 4983230072969 + 3 ^ 40 * 7929421 * 2
def baseEnd_7929421 : Nat := 452400476095013981952307

theorem tailTrace_7929421 : CollatzResearch.WordTrace tailWord_7929421 prefixEnd_7929421 452400476095013981952307 := by
  unfold tailWord_7929421
  simp only [CollatzResearch.WordTrace]
  refine ⟨289209743406069429135572117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192806495604046286090381411 289209743406069429135572117)
  ·
    refine ⟨13556706722159504490729943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 289209743406069429135572117 13556706722159504490729943)
    ·
      refine ⟨20335060083239256736094915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13556706722159504490729943 20335060083239256736094915)
      ·
        refine ⟨30502590124858885104142373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20335060083239256736094915 30502590124858885104142373)
        ·
          refine ⟨5719235648411040957026695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30502590124858885104142373 5719235648411040957026695)
          ·
            refine ⟨8578853472616561435540043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5719235648411040957026695 8578853472616561435540043)
            ·
              refine ⟨12868280208924842153310065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8578853472616561435540043 12868280208924842153310065)
              ·
                refine ⟨9651210156693631614982549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12868280208924842153310065 9651210156693631614982549)
                ·
                  refine ⟨452400476095013981952307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9651210156693631614982549 452400476095013981952307)
                  ·
                    rfl

theorem cell23_7929421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 1, 1, 2, 6].length) (baseStart_7929421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7929421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7929421 prefixEnd_7929421 := by exact prefixLift 7929421
  have htrace : WordTrace (prefixWord ++ tailWord_7929421) baseStart_7929421 baseEnd_7929421 := by
    simpa [prefixWord, tailWord_7929421, baseEnd_7929421] using wordTrace_append hprefix tailTrace_7929421
  have hstable : (prefixWord ++ tailWord_7929421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7929421).length < 2 ^ (prefixWord ++ tailWord_7929421).sum := by decide
  have hdescent : baseEnd_7929421 < baseStart_7929421 := by decide
  rcases family_descends (prefixWord ++ tailWord_7929421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7929447 : List Nat := [1, 1, 5, 1, 1, 1, 2, 5, 2, 4]
def baseStart_7929447 : Nat := 118140960795 + 7929447 * 2 ^ 59
def prefixEnd_7929447 : Nat := 4983230072969 + 3 ^ 40 * 7929447 * 2
def baseEnd_7929447 : Nat := 1357205878450714245281881

theorem tailTrace_7929447 : CollatzResearch.WordTrace tailWord_7929447 prefixEnd_7929447 1357205878450714245281881 := by
  unfold tailWord_7929447
  simp only [CollatzResearch.WordTrace]
  refine ⟨289210691703975235576018595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192807127802650157050679063 289210691703975235576018595)
  ·
    refine ⟨433816037555962853364027893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289210691703975235576018595 433816037555962853364027893)
    ·
      refine ⟨40670253520871517502877615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 433816037555962853364027893 40670253520871517502877615)
      ·
        refine ⟨61005380281307276254316423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40670253520871517502877615 61005380281307276254316423)
        ·
          refine ⟨91508070421960914381474635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61005380281307276254316423 91508070421960914381474635)
          ·
            refine ⟨137262105632941371572211953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91508070421960914381474635 137262105632941371572211953)
            ·
              refine ⟨102946579224706028679158965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137262105632941371572211953 102946579224706028679158965)
              ·
                refine ⟨9651241802316190188671153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 102946579224706028679158965 9651241802316190188671153)
                ·
                  refine ⟨7238431351737142641503365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9651241802316190188671153 7238431351737142641503365)
                  ·
                    refine ⟨1357205878450714245281881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7238431351737142641503365 1357205878450714245281881)
                    ·
                      rfl

theorem cell23_7929447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 5, 2, 4].length) (baseStart_7929447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7929447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7929447 prefixEnd_7929447 := by exact prefixLift 7929447
  have htrace : WordTrace (prefixWord ++ tailWord_7929447) baseStart_7929447 baseEnd_7929447 := by
    simpa [prefixWord, tailWord_7929447, baseEnd_7929447] using wordTrace_append hprefix tailTrace_7929447
  have hstable : (prefixWord ++ tailWord_7929447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7929447).length < 2 ^ (prefixWord ++ tailWord_7929447).sum := by decide
  have hdescent : baseEnd_7929447 < baseStart_7929447 := by decide
  rcases family_descends (prefixWord ++ tailWord_7929447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7929561 : List Nat := [1, 2, 1, 2, 3, 3, 2, 3, 2, 2, 2]
def baseStart_7929561 : Nat := 118140960795 + 7929561 * 2 ^ 59
def prefixEnd_7929561 : Nat := 4983230072969 + 3 ^ 40 * 7929561 * 2
def baseEnd_7929561 : Nat := 4071676172146755289820119

theorem tailTrace_7929561 : CollatzResearch.WordTrace tailWord_7929561 prefixEnd_7929561 4071676172146755289820119 := by
  unfold tailWord_7929561
  simp only [CollatzResearch.WordTrace]
  refine ⟨289214849625562233045668537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192809899750374822030445691 289214849625562233045668537)
  ·
    refine ⟨216911137219171674784251403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 289214849625562233045668537 216911137219171674784251403)
    ·
      refine ⟨325366705828757512176377105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216911137219171674784251403 325366705828757512176377105)
      ·
        refine ⟨244025029371568134132282829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 325366705828757512176377105 244025029371568134132282829)
        ·
          refine ⟨91509386014338050299606061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 244025029371568134132282829 91509386014338050299606061)
          ·
            refine ⟨34316019755376768862352273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91509386014338050299606061 34316019755376768862352273)
            ·
              refine ⟨25737014816532576646764205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34316019755376768862352273 25737014816532576646764205)
              ·
                refine ⟨9651380556199716242536577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25737014816532576646764205 9651380556199716242536577)
                ·
                  refine ⟨7238535417149787181902433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9651380556199716242536577 7238535417149787181902433)
                  ·
                    refine ⟨5428901562862340386426825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7238535417149787181902433 5428901562862340386426825)
                    ·
                      refine ⟨4071676172146755289820119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5428901562862340386426825 4071676172146755289820119)
                      ·
                        rfl

theorem cell23_7929561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 2, 3, 2, 2, 2].length) (baseStart_7929561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7929561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7929561 prefixEnd_7929561 := by exact prefixLift 7929561
  have htrace : WordTrace (prefixWord ++ tailWord_7929561) baseStart_7929561 baseEnd_7929561 := by
    simpa [prefixWord, tailWord_7929561, baseEnd_7929561] using wordTrace_append hprefix tailTrace_7929561
  have hstable : (prefixWord ++ tailWord_7929561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7929561).length < 2 ^ (prefixWord ++ tailWord_7929561).sum := by decide
  have hdescent : baseEnd_7929561 < baseStart_7929561 := by decide
  rcases family_descends (prefixWord ++ tailWord_7929561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7929606 : List Nat := [6, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3]
def baseStart_7929606 : Nat := 118140960795 + 7929606 * 2 ^ 59
def prefixEnd_7929606 : Nat := 4983230072969 + 3 ^ 40 * 7929606 * 2
def baseEnd_7929606 : Nat := 4071699278776207613757413

theorem tailTrace_7929606 : CollatzResearch.WordTrace tailWord_7929606 prefixEnd_7929606 4071699278776207613757413 := by
  unfold tailWord_7929606
  simp only [CollatzResearch.WordTrace]
  refine ⟨9038015340949975179095521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 192810993940266137154037781 9038015340949975179095521)
  ·
    refine ⟨6778511505712481384321641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9038015340949975179095521 6778511505712481384321641)
    ·
      refine ⟨5083883629284361038241231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6778511505712481384321641 5083883629284361038241231)
      ·
        refine ⟨7625825443926541557361847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5083883629284361038241231 7625825443926541557361847)
        ·
          refine ⟨11438738165889812336042771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7625825443926541557361847 11438738165889812336042771)
          ·
            refine ⟨17158107248834718504064157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11438738165889812336042771 17158107248834718504064157)
            ·
              refine ⟨6434290218313019439024059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17158107248834718504064157 6434290218313019439024059)
              ·
                refine ⟨9651435327469529158536089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6434290218313019439024059 9651435327469529158536089)
                ·
                  refine ⟨7238576495602146868902067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9651435327469529158536089 7238576495602146868902067)
                  ·
                    refine ⟨10857864743403220303353101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7238576495602146868902067 10857864743403220303353101)
                    ·
                      refine ⟨4071699278776207613757413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10857864743403220303353101 4071699278776207613757413)
                      ·
                        rfl

theorem cell23_7929606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3].length) (baseStart_7929606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7929606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7929606 prefixEnd_7929606 := by exact prefixLift 7929606
  have htrace : WordTrace (prefixWord ++ tailWord_7929606) baseStart_7929606 baseEnd_7929606 := by
    simpa [prefixWord, tailWord_7929606, baseEnd_7929606] using wordTrace_append hprefix tailTrace_7929606
  have hstable : (prefixWord ++ tailWord_7929606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7929606).length < 2 ^ (prefixWord ++ tailWord_7929606).sum := by decide
  have hdescent : baseEnd_7929606 < baseStart_7929606 := by decide
  rcases family_descends (prefixWord ++ tailWord_7929606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7929634 : List Nat := [3, 3, 1, 1, 2, 1, 2, 3, 2, 1, 4]
def baseStart_7929634 : Nat := 118140960795 + 7929634 * 2 ^ 59
def prefixEnd_7929634 : Nat := 4983230072969 + 3 ^ 40 * 7929634 * 2
def baseEnd_7929634 : Nat := 4071713656234533504207283

theorem tailTrace_7929634 : CollatzResearch.WordTrace tailWord_7929634 prefixEnd_7929634 4071713656234533504207283 := by
  unfold tailWord_7929634
  simp only [CollatzResearch.WordTrace]
  refine ⟨72304378038574441628268989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192811674769531844342050637 72304378038574441628268989)
  ·
    refine ⟨27114141764465415610600871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72304378038574441628268989 27114141764465415610600871)
    ·
      refine ⟨40671212646698123415901307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27114141764465415610600871 40671212646698123415901307)
      ·
        refine ⟨61006818970047185123851961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40671212646698123415901307 61006818970047185123851961)
        ·
          refine ⟨45755114227535388842888971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61006818970047185123851961 45755114227535388842888971)
          ·
            refine ⟨68632671341303083264333457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45755114227535388842888971 68632671341303083264333457)
            ·
              refine ⟨51474503505977312448250093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68632671341303083264333457 51474503505977312448250093)
              ·
                refine ⟨19302938814741492168093785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51474503505977312448250093 19302938814741492168093785)
                ·
                  refine ⟨14477204111056119126070339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19302938814741492168093785 14477204111056119126070339)
                  ·
                    refine ⟨21715806166584178689105509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14477204111056119126070339 21715806166584178689105509)
                    ·
                      refine ⟨4071713656234533504207283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21715806166584178689105509 4071713656234533504207283)
                      ·
                        rfl

theorem cell23_7929634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 3, 2, 1, 4].length) (baseStart_7929634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7929634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7929634 prefixEnd_7929634 := by exact prefixLift 7929634
  have htrace : WordTrace (prefixWord ++ tailWord_7929634) baseStart_7929634 baseEnd_7929634 := by
    simpa [prefixWord, tailWord_7929634, baseEnd_7929634] using wordTrace_append hprefix tailTrace_7929634
  have hstable : (prefixWord ++ tailWord_7929634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7929634).length < 2 ^ (prefixWord ++ tailWord_7929634).sum := by decide
  have hdescent : baseEnd_7929634 < baseStart_7929634 := by decide
  rcases family_descends (prefixWord ++ tailWord_7929634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7929661 : List Nat := [1, 4, 1, 4, 1, 1, 3, 1, 3, 4]
def baseStart_7929661 : Nat := 118140960795 + 7929661 * 2 ^ 59
def prefixEnd_7929661 : Nat := 4983230072969 + 3 ^ 40 * 7929661 * 2
def baseEnd_7929661 : Nat := 1357242506737401632856553

theorem tailTrace_7929661 : CollatzResearch.WordTrace tailWord_7929661 prefixEnd_7929661 1357242506737401632856553 := by
  unfold tailWord_7929661
  simp only [CollatzResearch.WordTrace]
  refine ⟨289218496925199950124308837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192812331283466633416205891 289218496925199950124308837)
  ·
    refine ⟨54228468173474990648307907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 289218496925199950124308837 54228468173474990648307907)
    ·
      refine ⟨81342702260212485972461861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54228468173474990648307907 81342702260212485972461861)
      ·
        refine ⟨15251756673789841119836599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81342702260212485972461861 15251756673789841119836599)
        ·
          refine ⟨22877635010684761679754899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15251756673789841119836599 22877635010684761679754899)
          ·
            refine ⟨34316452516027142519632349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22877635010684761679754899 34316452516027142519632349)
            ·
              refine ⟨12868669693510178444862131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34316452516027142519632349 12868669693510178444862131)
              ·
                refine ⟨19303004540265267667293197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12868669693510178444862131 19303004540265267667293197)
                ·
                  refine ⟨7238626702599475375234949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19303004540265267667293197 7238626702599475375234949)
                  ·
                    refine ⟨1357242506737401632856553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7238626702599475375234949 1357242506737401632856553)
                    ·
                      rfl

theorem cell23_7929661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 3, 1, 3, 4].length) (baseStart_7929661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7929661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7929661 prefixEnd_7929661 := by exact prefixLift 7929661
  have htrace : WordTrace (prefixWord ++ tailWord_7929661) baseStart_7929661 baseEnd_7929661 := by
    simpa [prefixWord, tailWord_7929661, baseEnd_7929661] using wordTrace_append hprefix tailTrace_7929661
  have hstable : (prefixWord ++ tailWord_7929661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7929661).length < 2 ^ (prefixWord ++ tailWord_7929661).sum := by decide
  have hdescent : baseEnd_7929661 < baseStart_7929661 := by decide
  rcases family_descends (prefixWord ++ tailWord_7929661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7929724 : List Nat := [2, 2, 2, 1, 1, 1, 1, 1, 4, 6, 2]
def baseStart_7929724 : Nat := 118140960795 + 7929724 * 2 ^ 59
def prefixEnd_7929724 : Nat := 4983230072969 + 3 ^ 40 * 7929724 * 2
def baseEnd_7929724 : Nat := 4071759869493438152081869

theorem tailTrace_7929724 : CollatzResearch.WordTrace tailWord_7929724 prefixEnd_7929724 4071759869493438152081869 := by
  unfold tailWord_7929724
  simp only [CollatzResearch.WordTrace]
  refine ⟨144610397361985855941926113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192813863149314474589234817 144610397361985855941926113)
  ·
    refine ⟨108457798021489391956444585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144610397361985855941926113 108457798021489391956444585)
    ·
      refine ⟨81343348516117043967333439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108457798021489391956444585 81343348516117043967333439)
      ·
        refine ⟨122015022774175565951000159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81343348516117043967333439 122015022774175565951000159)
        ·
          refine ⟨183022534161263348926500239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122015022774175565951000159 183022534161263348926500239)
          ·
            refine ⟨274533801241895023389750359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183022534161263348926500239 274533801241895023389750359)
            ·
              refine ⟨411800701862842535084625539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 274533801241895023389750359 411800701862842535084625539)
              ·
                refine ⟨617701052794263802626938309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 411800701862842535084625539 617701052794263802626938309)
                ·
                  refine ⟨115818947398924462992550933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 617701052794263802626938309 115818947398924462992550933)
                  ·
                    refine ⟨5429013159324584202775825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 115818947398924462992550933 5429013159324584202775825)
                    ·
                      refine ⟨4071759869493438152081869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5429013159324584202775825 4071759869493438152081869)
                      ·
                        rfl

theorem cell23_7929724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 4, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 4, 6, 2].length) (baseStart_7929724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7929724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7929724 prefixEnd_7929724 := by exact prefixLift 7929724
  have htrace : WordTrace (prefixWord ++ tailWord_7929724) baseStart_7929724 baseEnd_7929724 := by
    simpa [prefixWord, tailWord_7929724, baseEnd_7929724] using wordTrace_append hprefix tailTrace_7929724
  have hstable : (prefixWord ++ tailWord_7929724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7929724).length < 2 ^ (prefixWord ++ tailWord_7929724).sum := by decide
  have hdescent : baseEnd_7929724 < baseStart_7929724 := by decide
  rcases family_descends (prefixWord ++ tailWord_7929724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7929727 : List Nat := [1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 5]
def baseStart_7929727 : Nat := 118140960795 + 7929727 * 2 ^ 59
def prefixEnd_7929727 : Nat := 4983230072969 + 3 ^ 40 * 7929727 * 2
def baseEnd_7929727 : Nat := 4071761409935401640344355

theorem tailTrace_7929727 : CollatzResearch.WordTrace tailWord_7929727 prefixEnd_7929727 4071761409935401640344355 := by
  unfold tailWord_7929727
  simp only [CollatzResearch.WordTrace]
  refine ⟨289220904142960843396211435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192813936095307228930807623 289220904142960843396211435)
  ·
    refine ⟨433831356214441265094317153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289220904142960843396211435 433831356214441265094317153)
    ·
      refine ⟨325373517160830948820737865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 433831356214441265094317153 325373517160830948820737865)
      ·
        refine ⟨244030137870623211615553399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 325373517160830948820737865 244030137870623211615553399)
        ·
          refine ⟨366045206805934817423330099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 244030137870623211615553399 366045206805934817423330099)
          ·
            refine ⟨549067810208902226134995149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 366045206805934817423330099 549067810208902226134995149)
            ·
              refine ⟨205900428828338334800623181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 549067810208902226134995149 205900428828338334800623181)
              ·
                refine ⟨77212660810626875550233693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 205900428828338334800623181 77212660810626875550233693)
                ·
                  refine ⟨28954747803985078331337635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77212660810626875550233693 28954747803985078331337635)
                  ·
                    refine ⟨43432121705977617497006453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28954747803985078331337635 43432121705977617497006453)
                    ·
                      refine ⟨4071761409935401640344355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43432121705977617497006453 4071761409935401640344355)
                      ·
                        rfl

theorem cell23_7929727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 5].length) (baseStart_7929727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7929727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7929727 prefixEnd_7929727 := by exact prefixLift 7929727
  have htrace : WordTrace (prefixWord ++ tailWord_7929727) baseStart_7929727 baseEnd_7929727 := by
    simpa [prefixWord, tailWord_7929727, baseEnd_7929727] using wordTrace_append hprefix tailTrace_7929727
  have hstable : (prefixWord ++ tailWord_7929727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7929727).length < 2 ^ (prefixWord ++ tailWord_7929727).sum := by decide
  have hdescent : baseEnd_7929727 < baseStart_7929727 := by decide
  rcases family_descends (prefixWord ++ tailWord_7929727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7929752 : List Nat := [2, 1, 2, 6, 1, 1, 2, 3, 1, 1, 3]
def baseStart_7929752 : Nat := 118140960795 + 7929752 * 2 ^ 59
def prefixEnd_7929752 : Nat := 4983230072969 + 3 ^ 40 * 7929752 * 2
def baseEnd_7929752 : Nat := 4071774246951764042531741

theorem tailTrace_7929752 : CollatzResearch.WordTrace tailWord_7929752 prefixEnd_7929752 4071774246951764042531741 := by
  unfold tailWord_7929752
  simp only [CollatzResearch.WordTrace]
  refine ⟨144610907983935136332935755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192814543978580181777247673 144610907983935136332935755)
  ·
    refine ⟨216916361975902704499403633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144610907983935136332935755 216916361975902704499403633)
    ·
      refine ⟨162687271481927028374552725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216916361975902704499403633 162687271481927028374552725)
      ·
        refine ⟨7625965850715329455057159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 162687271481927028374552725 7625965850715329455057159)
        ·
          refine ⟨11438948776072994182585739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7625965850715329455057159 11438948776072994182585739)
          ·
            refine ⟨17158423164109491273878609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11438948776072994182585739 17158423164109491273878609)
            ·
              refine ⟨12868817373082118455408957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17158423164109491273878609 12868817373082118455408957)
              ·
                refine ⟨4825806514905794420778359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12868817373082118455408957 4825806514905794420778359)
                ·
                  refine ⟨7238709772358691631167539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4825806514905794420778359 7238709772358691631167539)
                  ·
                    refine ⟨10858064658538037446751309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7238709772358691631167539 10858064658538037446751309)
                    ·
                      refine ⟨4071774246951764042531741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10858064658538037446751309 4071774246951764042531741)
                      ·
                        rfl

theorem cell23_7929752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 2, 3, 1, 1, 3].length) (baseStart_7929752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7929752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7929752 prefixEnd_7929752 := by exact prefixLift 7929752
  have htrace : WordTrace (prefixWord ++ tailWord_7929752) baseStart_7929752 baseEnd_7929752 := by
    simpa [prefixWord, tailWord_7929752, baseEnd_7929752] using wordTrace_append hprefix tailTrace_7929752
  have hstable : (prefixWord ++ tailWord_7929752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7929752).length < 2 ^ (prefixWord ++ tailWord_7929752).sum := by decide
  have hdescent : baseEnd_7929752 < baseStart_7929752 := by decide
  rcases family_descends (prefixWord ++ tailWord_7929752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7929787 : List Nat := [1, 1, 1, 1, 1, 2, 2, 4, 1, 4, 5]
def baseStart_7929787 : Nat := 118140960795 + 7929787 * 2 ^ 59
def prefixEnd_7929787 : Nat := 4983230072969 + 3 ^ 40 * 7929787 * 2
def baseEnd_7929787 : Nat := 4071792218774671405594079

theorem tailTrace_7929787 : CollatzResearch.WordTrace tailWord_7929787 prefixEnd_7929787 4071792218774671405594079 := by
  unfold tailWord_7929787
  simp only [CollatzResearch.WordTrace]
  refine ⟨289223092522743473643395615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192815395015162315762263743 289223092522743473643395615)
  ·
    refine ⟨433834638784115210465093423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289223092522743473643395615 433834638784115210465093423)
    ·
      refine ⟨650751958176172815697640135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 433834638784115210465093423 650751958176172815697640135)
      ·
        refine ⟨976127937264259223546460203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 650751958176172815697640135 976127937264259223546460203)
        ·
          refine ⟨1464191905896388835319690305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 976127937264259223546460203 1464191905896388835319690305)
          ·
            refine ⟨1098143929422291626489767729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1464191905896388835319690305 1098143929422291626489767729)
            ·
              refine ⟨823607947066718719867325797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1098143929422291626489767729 823607947066718719867325797)
              ·
                refine ⟨154426490075009759975123587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 823607947066718719867325797 154426490075009759975123587)
                ·
                  refine ⟨231639735112514639962685381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 154426490075009759975123587 231639735112514639962685381)
                  ·
                    refine ⟨43432450333596494993003509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 231639735112514639962685381 43432450333596494993003509)
                    ·
                      refine ⟨4071792218774671405594079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43432450333596494993003509 4071792218774671405594079)
                      ·
                        rfl

theorem cell23_7929787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4, 1, 4, 5].length) (baseStart_7929787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7929787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7929787 prefixEnd_7929787 := by exact prefixLift 7929787
  have htrace : WordTrace (prefixWord ++ tailWord_7929787) baseStart_7929787 baseEnd_7929787 := by
    simpa [prefixWord, tailWord_7929787, baseEnd_7929787] using wordTrace_append hprefix tailTrace_7929787
  have hstable : (prefixWord ++ tailWord_7929787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7929787).length < 2 ^ (prefixWord ++ tailWord_7929787).sum := by decide
  have hdescent : baseEnd_7929787 < baseStart_7929787 := by decide
  rcases family_descends (prefixWord ++ tailWord_7929787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
