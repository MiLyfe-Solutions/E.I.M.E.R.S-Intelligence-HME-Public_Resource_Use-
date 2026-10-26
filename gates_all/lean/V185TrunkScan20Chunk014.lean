import V185TrunkScan20Chunk013

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_84565 : List Nat := [1, 3, 2, 2, 1, 1, 2, 4, 4]
def baseStart_84565 : Nat := 118140960795 + 84565 * 2 ^ 59
def prefixEnd_84565 : Nat := 4983230072969 + 3 ^ 40 * 84565 * 2
def baseEnd_84565 : Nat := 38597770264503886887643

theorem tailTrace_84565 : CollatzResearch.WordTrace tailWord_84565 prefixEnd_84565 38597770264503886887643 := by
  unfold tailWord_84565
  simp only [CollatzResearch.WordTrace]
  refine ⟨3084338938642922397279149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2056225959095281598186099 3084338938642922397279149)
  ·
    refine ⟨1156627101991095898979681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3084338938642922397279149 1156627101991095898979681)
    ·
      refine ⟨867470326493321924234761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1156627101991095898979681 867470326493321924234761)
      ·
        refine ⟨650602744869991443176071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 867470326493321924234761 650602744869991443176071)
        ·
          refine ⟨975904117304987164764107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 650602744869991443176071 975904117304987164764107)
          ·
            refine ⟨1463856175957480747146161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 975904117304987164764107 1463856175957480747146161)
            ·
              refine ⟨1097892131968110560359621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1463856175957480747146161 1097892131968110560359621)
              ·
                refine ⟨205854774744020730067429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1097892131968110560359621 205854774744020730067429)
                ·
                  refine ⟨38597770264503886887643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 205854774744020730067429 38597770264503886887643)
                  ·
                    rfl

theorem cell20_84565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 4, 4].length) (baseStart_84565 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_84565 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_84565 prefixEnd_84565 := by exact prefixLift 84565
  have htrace : WordTrace (prefixWord ++ tailWord_84565) baseStart_84565 baseEnd_84565 := by
    simpa [prefixWord, tailWord_84565, baseEnd_84565] using wordTrace_append hprefix tailTrace_84565
  have hstable : (prefixWord ++ tailWord_84565).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_84565).length < 2 ^ (prefixWord ++ tailWord_84565).sum := by decide
  have hdescent : baseEnd_84565 < baseStart_84565 := by decide
  rcases family_descends (prefixWord ++ tailWord_84565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_84599 : List Nat := [1, 1, 3, 1, 1, 3, 6, 2, 2]
def baseStart_84599 : Nat := 118140960795 + 84599 * 2 ^ 59
def prefixEnd_84599 : Nat := 4983230072969 + 3 ^ 40 * 84599 * 2
def baseEnd_84599 : Nat := 38613288790950879754171

theorem tailTrace_84599 : CollatzResearch.WordTrace tailWord_84599 prefixEnd_84599 38613288790950879754171 := by
  unfold tailWord_84599
  simp only [CollatzResearch.WordTrace]
  refine ⟨3085579020519746204016851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2057052680346497469344567 3085579020519746204016851)
  ·
    refine ⟨4628368530779619306025277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3085579020519746204016851 4628368530779619306025277)
    ·
      refine ⟨1735638199042357239759479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4628368530779619306025277 1735638199042357239759479)
      ·
        refine ⟨2603457298563535859639219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1735638199042357239759479 2603457298563535859639219)
        ·
          refine ⟨3905185947845303789458829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2603457298563535859639219 3905185947845303789458829)
          ·
            refine ⟨1464444730441988921047061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3905185947845303789458829 1464444730441988921047061)
            ·
              refine ⟨68645846739468230674081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1464444730441988921047061 68645846739468230674081)
              ·
                refine ⟨51484385054601173005561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68645846739468230674081 51484385054601173005561)
                ·
                  refine ⟨38613288790950879754171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51484385054601173005561 38613288790950879754171)
                  ·
                    rfl

theorem cell20_84599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 6, 2, 2].length) (baseStart_84599 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_84599 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_84599 prefixEnd_84599 := by exact prefixLift 84599
  have htrace : WordTrace (prefixWord ++ tailWord_84599) baseStart_84599 baseEnd_84599 := by
    simpa [prefixWord, tailWord_84599, baseEnd_84599] using wordTrace_append hprefix tailTrace_84599
  have hstable : (prefixWord ++ tailWord_84599).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_84599).length < 2 ^ (prefixWord ++ tailWord_84599).sum := by decide
  have hdescent : baseEnd_84599 < baseStart_84599 := by decide
  rcases family_descends (prefixWord ++ tailWord_84599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_84617 : List Nat := [1, 2, 1, 1, 4, 1, 1, 2, 7]
def baseStart_84617 : Nat := 118140960795 + 84617 * 2 ^ 59
def prefixEnd_84617 : Nat := 4983230072969 + 3 ^ 40 * 84617 * 2
def baseEnd_84617 : Nat := 38621504481422817154097

theorem tailTrace_84617 : CollatzResearch.WordTrace tailWord_84617 prefixEnd_84617 38621504481422817154097 := by
  unfold tailWord_84617
  simp only [CollatzResearch.WordTrace]
  refine ⟨3086235534454535278172105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2057490356303023518781403 3086235534454535278172105)
  ·
    refine ⟨2314676650840901458629079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3086235534454535278172105 2314676650840901458629079)
    ·
      refine ⟨3472014976261352187943619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2314676650840901458629079 3472014976261352187943619)
      ·
        refine ⟨5208022464392028281915429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3472014976261352187943619 5208022464392028281915429)
        ·
          refine ⟨976504212073505302859143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5208022464392028281915429 976504212073505302859143)
          ·
            refine ⟨1464756318110257954288715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 976504212073505302859143 1464756318110257954288715)
            ·
              refine ⟨2197134477165386931433073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1464756318110257954288715 2197134477165386931433073)
              ·
                refine ⟨1647850857874040198574805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2197134477165386931433073 1647850857874040198574805)
                ·
                  refine ⟨38621504481422817154097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1647850857874040198574805 38621504481422817154097)
                  ·
                    rfl

theorem cell20_84617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 2, 7].length) (baseStart_84617 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_84617 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_84617 prefixEnd_84617 := by exact prefixLift 84617
  have htrace : WordTrace (prefixWord ++ tailWord_84617) baseStart_84617 baseEnd_84617 := by
    simpa [prefixWord, tailWord_84617, baseEnd_84617] using wordTrace_append hprefix tailTrace_84617
  have hstable : (prefixWord ++ tailWord_84617).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_84617).length < 2 ^ (prefixWord ++ tailWord_84617).sum := by decide
  have hdescent : baseEnd_84617 < baseStart_84617 := by decide
  rcases family_descends (prefixWord ++ tailWord_84617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_84647 : List Nat := [1, 1, 6, 3, 1, 2, 1, 2, 3]
def baseStart_84647 : Nat := 118140960795 + 84647 * 2 ^ 59
def prefixEnd_84647 : Nat := 4983230072969 + 3 ^ 40 * 84647 * 2
def baseEnd_84647 : Nat := 38635197298876046153975

theorem tailTrace_84647 : CollatzResearch.WordTrace tailWord_84647 prefixEnd_84647 38635197298876046153975 := by
  unfold tailWord_84647
  simp only [CollatzResearch.WordTrace]
  refine ⟨3087329724345850401764195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2058219816230566934509463 3087329724345850401764195)
  ·
    refine ⟨4630994586518775602646293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3087329724345850401764195 4630994586518775602646293)
    ·
      refine ⟨217077871243067606374045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 4630994586518775602646293 217077871243067606374045)
      ·
        refine ⟨81404201716150352390267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 217077871243067606374045 81404201716150352390267)
        ·
          refine ⟨122106302574225528585401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81404201716150352390267 122106302574225528585401)
          ·
            refine ⟨91579726930669146439051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 122106302574225528585401 91579726930669146439051)
            ·
              refine ⟨137369590396003719658577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91579726930669146439051 137369590396003719658577)
              ·
                refine ⟨103027192797002789743933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 137369590396003719658577 103027192797002789743933)
                ·
                  refine ⟨38635197298876046153975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 103027192797002789743933 38635197298876046153975)
                  ·
                    rfl

theorem cell20_84647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 2, 1, 2, 3].length) (baseStart_84647 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_84647 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_84647 prefixEnd_84647 := by exact prefixLift 84647
  have htrace : WordTrace (prefixWord ++ tailWord_84647) baseStart_84647 baseEnd_84647 := by
    simpa [prefixWord, tailWord_84647, baseEnd_84647] using wordTrace_append hprefix tailTrace_84647
  have hstable : (prefixWord ++ tailWord_84647).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_84647).length < 2 ^ (prefixWord ++ tailWord_84647).sum := by decide
  have hdescent : baseEnd_84647 < baseStart_84647 := by decide
  rcases family_descends (prefixWord ++ tailWord_84647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_84654 : List Nat := [4, 1, 4, 1, 1, 1, 2, 4, 2]
def baseStart_84654 : Nat := 118140960795 + 84654 * 2 ^ 59
def prefixEnd_84654 : Nat := 4983230072969 + 3 ^ 40 * 84654 * 2
def baseEnd_84654 : Nat := 38638392289615132920613

theorem tailTrace_84654 : CollatzResearch.WordTrace tailWord_84654 prefixEnd_84654 38638392289615132920613 := by
  unfold tailWord_84654
  simp only [CollatzResearch.WordTrace]
  refine ⟨385948129415061324658627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2058390023546993731512677 385948129415061324658627)
  ·
    refine ⟨578922194122591986987941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 385948129415061324658627 578922194122591986987941)
    ·
      refine ⟨108547911397985997560239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 578922194122591986987941 108547911397985997560239)
      ·
        refine ⟨162821867096978996340359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108547911397985997560239 162821867096978996340359)
        ·
          refine ⟨244232800645468494510539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 162821867096978996340359 244232800645468494510539)
          ·
            refine ⟨366349200968202741765809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 244232800645468494510539 366349200968202741765809)
            ·
              refine ⟨274761900726152056324357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 366349200968202741765809 274761900726152056324357)
              ·
                refine ⟨51517856386153510560817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 274761900726152056324357 51517856386153510560817)
                ·
                  refine ⟨38638392289615132920613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51517856386153510560817 38638392289615132920613)
                  ·
                    rfl

theorem cell20_84654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 2, 4, 2].length) (baseStart_84654 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_84654 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_84654 prefixEnd_84654 := by exact prefixLift 84654
  have htrace : WordTrace (prefixWord ++ tailWord_84654) baseStart_84654 baseEnd_84654 := by
    simpa [prefixWord, tailWord_84654, baseEnd_84654] using wordTrace_append hprefix tailTrace_84654
  have hstable : (prefixWord ++ tailWord_84654).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_84654).length < 2 ^ (prefixWord ++ tailWord_84654).sum := by decide
  have hdescent : baseEnd_84654 < baseStart_84654 := by decide
  rcases family_descends (prefixWord ++ tailWord_84654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_84682 : List Nat := [3, 1, 2, 1, 4, 3, 2, 4]
def baseStart_84682 : Nat := 118140960795 + 84682 * 2 ^ 59
def prefixEnd_84682 : Nat := 4983230072969 + 3 ^ 40 * 84682 * 2
def baseEnd_84682 : Nat := 12883724084190493329055

theorem tailTrace_84682 : CollatzResearch.WordTrace tailWord_84682 prefixEnd_84682 12883724084190493329055 := by
  unfold tailWord_84682
  simp only [CollatzResearch.WordTrace]
  refine ⟨772151569804762844822075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2059070852812700919525533 772151569804762844822075)
  ·
    refine ⟨1158227354707144267233113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 772151569804762844822075 1158227354707144267233113)
    ·
      refine ⟨868670516030358200424835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1158227354707144267233113 868670516030358200424835)
      ·
        refine ⟨1303005774045537300637253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 868670516030358200424835 1303005774045537300637253)
        ·
          refine ⟨244313582633538243869485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1303005774045537300637253 244313582633538243869485)
          ·
            refine ⟨91617593487576841451057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 244313582633538243869485 91617593487576841451057)
            ·
              refine ⟨68713195115682631088293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91617593487576841451057 68713195115682631088293)
              ·
                refine ⟨12883724084190493329055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 68713195115682631088293 12883724084190493329055)
                ·
                  rfl

theorem cell20_84682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 3, 2, 4].length) (baseStart_84682 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_84682 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_84682 prefixEnd_84682 := by exact prefixLift 84682
  have htrace : WordTrace (prefixWord ++ tailWord_84682) baseStart_84682 baseEnd_84682 := by
    simpa [prefixWord, tailWord_84682, baseEnd_84682] using wordTrace_append hprefix tailTrace_84682
  have hstable : (prefixWord ++ tailWord_84682).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_84682).length < 2 ^ (prefixWord ++ tailWord_84682).sum := by decide
  have hdescent : baseEnd_84682 < baseStart_84682 := by decide
  rcases family_descends (prefixWord ++ tailWord_84682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_84768 : List Nat := [2, 1, 1, 5, 1, 4, 2, 2, 2]
def baseStart_84768 : Nat := 118140960795 + 84768 * 2 ^ 59
def prefixEnd_84768 : Nat := 4983230072969 + 3 ^ 40 * 84768 * 2
def baseEnd_84768 : Nat := 38690424995937403120147

theorem tailTrace_84768 : CollatzResearch.WordTrace tailWord_84768 prefixEnd_84768 38690424995937403120147 := by
  unfold tailWord_84768
  simp only [CollatzResearch.WordTrace]
  refine ⟨1545871478453744033459479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2061161971271658711279305 1545871478453744033459479)
  ·
    refine ⟨2318807217680616050189219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1545871478453744033459479 2318807217680616050189219)
    ·
      refine ⟨3478210826520924075283829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2318807217680616050189219 3478210826520924075283829)
      ·
        refine ⟨326082264986336632057859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3478210826520924075283829 326082264986336632057859)
        ·
          refine ⟨489123397479504948086789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 326082264986336632057859 489123397479504948086789)
          ·
            refine ⟨91710637027407177766273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 489123397479504948086789 91710637027407177766273)
            ·
              refine ⟨68782977770555383324705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91710637027407177766273 68782977770555383324705)
              ·
                refine ⟨51587233327916537493529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68782977770555383324705 51587233327916537493529)
                ·
                  refine ⟨38690424995937403120147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51587233327916537493529 38690424995937403120147)
                  ·
                    rfl

theorem cell20_84768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 4, 2, 2, 2].length) (baseStart_84768 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_84768 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_84768 prefixEnd_84768 := by exact prefixLift 84768
  have htrace : WordTrace (prefixWord ++ tailWord_84768) baseStart_84768 baseEnd_84768 := by
    simpa [prefixWord, tailWord_84768, baseEnd_84768] using wordTrace_append hprefix tailTrace_84768
  have hstable : (prefixWord ++ tailWord_84768).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_84768).length < 2 ^ (prefixWord ++ tailWord_84768).sum := by decide
  have hdescent : baseEnd_84768 < baseStart_84768 := by decide
  rcases family_descends (prefixWord ++ tailWord_84768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_84786 : List Nat := [3, 2, 1, 1, 3, 1, 1, 5, 3]
def baseStart_84786 : Nat := 118140960795 + 84786 * 2 ^ 59
def prefixEnd_84786 : Nat := 4983230072969 + 3 ^ 40 * 84786 * 2
def baseEnd_84786 : Nat := 38698640686409340520073

theorem tailTrace_84786 : CollatzResearch.WordTrace tailWord_84786 prefixEnd_84786 38698640686409340520073 := by
  unfold tailWord_84786
  simp only [CollatzResearch.WordTrace]
  refine ⟨773099867710569285268553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2061599647228184760716141 773099867710569285268553)
  ·
    refine ⟨579824900782926963951415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 773099867710569285268553 579824900782926963951415)
    ·
      refine ⟨869737351174390445927123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 579824900782926963951415 869737351174390445927123)
      ·
        refine ⟨1304606026761585668890685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 869737351174390445927123 1304606026761585668890685)
        ·
          refine ⟨489227260035594625834007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1304606026761585668890685 489227260035594625834007)
          ·
            refine ⟨733840890053391938751011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 489227260035594625834007 733840890053391938751011)
            ·
              refine ⟨1100761335080087908126517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 733840890053391938751011 1100761335080087908126517)
              ·
                refine ⟨103196375163758241386861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1100761335080087908126517 103196375163758241386861)
                ·
                  refine ⟨38698640686409340520073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 103196375163758241386861 38698640686409340520073)
                  ·
                    rfl

theorem cell20_84786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 5, 3].length) (baseStart_84786 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_84786 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_84786 prefixEnd_84786 := by exact prefixLift 84786
  have htrace : WordTrace (prefixWord ++ tailWord_84786) baseStart_84786 baseEnd_84786 := by
    simpa [prefixWord, tailWord_84786, baseEnd_84786] using wordTrace_append hprefix tailTrace_84786
  have hstable : (prefixWord ++ tailWord_84786).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_84786).length < 2 ^ (prefixWord ++ tailWord_84786).sum := by decide
  have hdescent : baseEnd_84786 < baseStart_84786 := by decide
  rcases family_descends (prefixWord ++ tailWord_84786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_84807 : List Nat := [1, 1, 4, 1, 2, 1, 1, 4, 5]
def baseStart_84807 : Nat := 118140960795 + 84807 * 2 ^ 59
def prefixEnd_84807 : Nat := 4983230072969 + 3 ^ 40 * 84807 * 2
def baseEnd_84807 : Nat := 38708225658626600819987

theorem tailTrace_84807 : CollatzResearch.WordTrace tailWord_84807 prefixEnd_84807 38708225658626600819987 := by
  unfold tailWord_84807
  simp only [CollatzResearch.WordTrace]
  refine ⟨3093165403766197727588675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2062110269177465151725783 3093165403766197727588675)
  ·
    refine ⟨4639748105649296591383013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3093165403766197727588675 4639748105649296591383013)
    ·
      refine ⟨869952769809243110884315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4639748105649296591383013 869952769809243110884315)
      ·
        refine ⟨1304929154713864666326473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 869952769809243110884315 1304929154713864666326473)
        ·
          refine ⟨978696866035398499744855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1304929154713864666326473 978696866035398499744855)
          ·
            refine ⟨1468045299053097749617283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 978696866035398499744855 1468045299053097749617283)
            ·
              refine ⟨2202067948579646624425925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1468045299053097749617283 2202067948579646624425925)
              ·
                refine ⟨412887740358683742079861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2202067948579646624425925 412887740358683742079861)
                ·
                  refine ⟨38708225658626600819987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 412887740358683742079861 38708225658626600819987)
                  ·
                    rfl

theorem cell20_84807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 4, 5].length) (baseStart_84807 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_84807 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_84807 prefixEnd_84807 := by exact prefixLift 84807
  have htrace : WordTrace (prefixWord ++ tailWord_84807) baseStart_84807 baseEnd_84807 := by
    simpa [prefixWord, tailWord_84807, baseEnd_84807] using wordTrace_append hprefix tailTrace_84807
  have hstable : (prefixWord ++ tailWord_84807).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_84807).length < 2 ^ (prefixWord ++ tailWord_84807).sum := by decide
  have hdescent : baseEnd_84807 < baseStart_84807 := by decide
  rcases family_descends (prefixWord ++ tailWord_84807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_84820 : List Nat := [2, 4, 1, 1, 4, 2, 1, 2, 3]
def baseStart_84820 : Nat := 118140960795 + 84820 * 2 ^ 59
def prefixEnd_84820 : Nat := 4983230072969 + 3 ^ 40 * 84820 * 2
def baseEnd_84820 : Nat := 38714159212856333386601

theorem tailTrace_84820 : CollatzResearch.WordTrace tailWord_84820 prefixEnd_84820 38714159212856333386601 := by
  unfold tailWord_84820
  simp only [CollatzResearch.WordTrace]
  refine ⟨1546819776359550473905957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2062426368479400631874609 1546819776359550473905957)
  ·
    refine ⟨290028708067415713857367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1546819776359550473905957 290028708067415713857367)
    ·
      refine ⟨435043062101123570786051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 290028708067415713857367 435043062101123570786051)
      ·
        refine ⟨652564593151685356179077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 435043062101123570786051 652564593151685356179077)
        ·
          refine ⟨122355861215941004283577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 652564593151685356179077 122355861215941004283577)
          ·
            refine ⟨91766895911955753212683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 122355861215941004283577 91766895911955753212683)
            ·
              refine ⟨137650343867933629819025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91766895911955753212683 137650343867933629819025)
              ·
                refine ⟨103237757900950222364269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 137650343867933629819025 103237757900950222364269)
                ·
                  refine ⟨38714159212856333386601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 103237757900950222364269 38714159212856333386601)
                  ·
                    rfl

theorem cell20_84820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 2, 1, 2, 3].length) (baseStart_84820 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_84820 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_84820 prefixEnd_84820 := by exact prefixLift 84820
  have htrace : WordTrace (prefixWord ++ tailWord_84820) baseStart_84820 baseEnd_84820 := by
    simpa [prefixWord, tailWord_84820, baseEnd_84820] using wordTrace_append hprefix tailTrace_84820
  have hstable : (prefixWord ++ tailWord_84820).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_84820).length < 2 ^ (prefixWord ++ tailWord_84820).sum := by decide
  have hdescent : baseEnd_84820 < baseStart_84820 := by decide
  rcases family_descends (prefixWord ++ tailWord_84820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_84831 : List Nat := [1, 1, 2, 3, 1, 3, 4, 1, 4]
def baseStart_84831 : Nat := 118140960795 + 84831 * 2 ^ 59
def prefixEnd_84831 : Nat := 4983230072969 + 3 ^ 40 * 84831 * 2
def baseEnd_84831 : Nat := 38719179912589184019889

theorem tailTrace_84831 : CollatzResearch.WordTrace tailWord_84831 prefixEnd_84831 38719179912589184019889 := by
  unfold tailWord_84831
  simp only [CollatzResearch.WordTrace]
  refine ⟨3094040755679249826462347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2062693837119499884308231 3094040755679249826462347)
  ·
    refine ⟨4641061133518874739693521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3094040755679249826462347 4641061133518874739693521)
    ·
      refine ⟨3480795850139156054770141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4641061133518874739693521 3480795850139156054770141)
      ·
        refine ⟨1305298443802183520538803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3480795850139156054770141 1305298443802183520538803)
        ·
          refine ⟨1957947665703275280808205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1305298443802183520538803 1957947665703275280808205)
          ·
            refine ⟨734230374638728230303077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1957947665703275280808205 734230374638728230303077)
            ·
              refine ⟨137668195244761543181827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 734230374638728230303077 137668195244761543181827)
              ·
                refine ⟨206502292867142314772741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 137668195244761543181827 206502292867142314772741)
                ·
                  refine ⟨38719179912589184019889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 206502292867142314772741 38719179912589184019889)
                  ·
                    rfl

theorem cell20_84831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 4, 1, 4].length) (baseStart_84831 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_84831 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_84831 prefixEnd_84831 := by exact prefixLift 84831
  have htrace : WordTrace (prefixWord ++ tailWord_84831) baseStart_84831 baseEnd_84831 := by
    simpa [prefixWord, tailWord_84831, baseEnd_84831] using wordTrace_append hprefix tailTrace_84831
  have hstable : (prefixWord ++ tailWord_84831).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_84831).length < 2 ^ (prefixWord ++ tailWord_84831).sum := by decide
  have hdescent : baseEnd_84831 < baseStart_84831 := by decide
  rcases family_descends (prefixWord ++ tailWord_84831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_84882 : List Nat := [3, 2, 3, 2, 3, 1, 1, 1, 4]
def baseStart_84882 : Nat := 118140960795 + 84882 * 2 ^ 59
def prefixEnd_84882 : Nat := 4983230072969 + 3 ^ 40 * 84882 * 2
def baseEnd_84882 : Nat := 38742457702259673319681

theorem tailTrace_84882 : CollatzResearch.WordTrace tailWord_84882 prefixEnd_84882 38742457702259673319681 := by
  unfold tailWord_84882
  simp only [CollatzResearch.WordTrace]
  refine ⟨773975219623621384142225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2063933918996323691045933 773975219623621384142225)
  ·
    refine ⟨580481414717716038106669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 773975219623621384142225 580481414717716038106669)
    ·
      refine ⟨217680530519143514290001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 580481414717716038106669 217680530519143514290001)
      ·
        refine ⟨163260397889357635717501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 217680530519143514290001 163260397889357635717501)
        ·
          refine ⟨61222649208509113394063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 163260397889357635717501 61222649208509113394063)
          ·
            refine ⟨91833973812763670091095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61222649208509113394063 91833973812763670091095)
            ·
              refine ⟨137750960719145505136643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91833973812763670091095 137750960719145505136643)
              ·
                refine ⟨206626441078718257704965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 137750960719145505136643 206626441078718257704965)
                ·
                  refine ⟨38742457702259673319681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 206626441078718257704965 38742457702259673319681)
                  ·
                    rfl

theorem cell20_84882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 1, 1, 1, 4].length) (baseStart_84882 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_84882 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_84882 prefixEnd_84882 := by exact prefixLift 84882
  have htrace : WordTrace (prefixWord ++ tailWord_84882) baseStart_84882 baseEnd_84882 := by
    simpa [prefixWord, tailWord_84882, baseEnd_84882] using wordTrace_append hprefix tailTrace_84882
  have hstable : (prefixWord ++ tailWord_84882).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_84882).length < 2 ^ (prefixWord ++ tailWord_84882).sum := by decide
  have hdescent : baseEnd_84882 < baseStart_84882 := by decide
  rcases family_descends (prefixWord ++ tailWord_84882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_84900 : List Nat := [2, 3, 1, 2, 1, 2, 3, 3, 3]
def baseStart_84900 : Nat := 118140960795 + 84900 * 2 ^ 59
def prefixEnd_84900 : Nat := 4983230072969 + 3 ^ 40 * 84900 * 2
def baseEnd_84900 : Nat := 38750673392731610719607

theorem tailTrace_84900 : CollatzResearch.WordTrace tailWord_84900 prefixEnd_84900 38750673392731610719607 := by
  unfold tailWord_84900
  simp only [CollatzResearch.WordTrace]
  refine ⟨1548278696214637305362077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2064371594952849740482769 1548278696214637305362077)
  ·
    refine ⟨580604511080488989510779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1548278696214637305362077 580604511080488989510779)
    ·
      refine ⟨870906766620733484266169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 580604511080488989510779 870906766620733484266169)
      ·
        refine ⟨653180074965550113199627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 870906766620733484266169 653180074965550113199627)
        ·
          refine ⟨979770112448325169799441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 653180074965550113199627 979770112448325169799441)
          ·
            refine ⟨734827584336243877349581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 979770112448325169799441 734827584336243877349581)
            ·
              refine ⟨275560344126091454006093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 734827584336243877349581 275560344126091454006093)
              ·
                refine ⟨103335129047284295252285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 275560344126091454006093 103335129047284295252285)
                ·
                  refine ⟨38750673392731610719607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 103335129047284295252285 38750673392731610719607)
                  ·
                    rfl

theorem cell20_84900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 3, 3, 3].length) (baseStart_84900 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_84900 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_84900 prefixEnd_84900 := by exact prefixLift 84900
  have htrace : WordTrace (prefixWord ++ tailWord_84900) baseStart_84900 baseEnd_84900 := by
    simpa [prefixWord, tailWord_84900, baseEnd_84900] using wordTrace_append hprefix tailTrace_84900
  have hstable : (prefixWord ++ tailWord_84900).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_84900).length < 2 ^ (prefixWord ++ tailWord_84900).sum := by decide
  have hdescent : baseEnd_84900 < baseStart_84900 := by decide
  rcases family_descends (prefixWord ++ tailWord_84900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_84952 : List Nat := [2, 1, 2, 2, 2, 3, 3, 5]
def baseStart_84952 : Nat := 118140960795 + 84952 * 2 ^ 59
def prefixEnd_84952 : Nat := 4983230072969 + 3 ^ 40 * 84952 * 2
def baseEnd_84952 : Nat := 12924802536550180328687

theorem tailTrace_84952 : CollatzResearch.WordTrace tailWord_84952 prefixEnd_84952 12924802536550180328687 := by
  unfold tailWord_84952
  simp only [CollatzResearch.WordTrace]
  refine ⟨1549226994120443745808555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2065635992160591661078073 1549226994120443745808555)
  ·
    refine ⟨2323840491180665618712833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1549226994120443745808555 2323840491180665618712833)
    ·
      refine ⟨1742880368385499214034625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2323840491180665618712833 1742880368385499214034625)
      ·
        refine ⟨1307160276289124410525969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1742880368385499214034625 1307160276289124410525969)
        ·
          refine ⟨980370207216843307894477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1307160276289124410525969 980370207216843307894477)
          ·
            refine ⟨367638827706316240460429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 980370207216843307894477 367638827706316240460429)
            ·
              refine ⟨137864560389868590172661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 367638827706316240460429 137864560389868590172661)
              ·
                refine ⟨12924802536550180328687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 137864560389868590172661 12924802536550180328687)
                ·
                  rfl

theorem cell20_84952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 3, 5].length) (baseStart_84952 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_84952 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_84952 prefixEnd_84952 := by exact prefixLift 84952
  have htrace : WordTrace (prefixWord ++ tailWord_84952) baseStart_84952 baseEnd_84952 := by
    simpa [prefixWord, tailWord_84952, baseEnd_84952] using wordTrace_append hprefix tailTrace_84952
  have hstable : (prefixWord ++ tailWord_84952).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_84952).length < 2 ^ (prefixWord ++ tailWord_84952).sum := by decide
  have hdescent : baseEnd_84952 < baseStart_84952 := by decide
  rcases family_descends (prefixWord ++ tailWord_84952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_84962 : List Nat := [3, 3, 3, 1, 1, 1, 1, 1, 6]
def baseStart_84962 : Nat := 118140960795 + 84962 * 2 ^ 59
def prefixEnd_84962 : Nat := 4983230072969 + 3 ^ 40 * 84962 * 2
def baseEnd_84962 : Nat := 38778971882134950652687

theorem tailTrace_84962 : CollatzResearch.WordTrace tailWord_84962 prefixEnd_84962 38778971882134950652687 := by
  unfold tailWord_84962
  simp only [CollatzResearch.WordTrace]
  refine ⟨774704679551164799870285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2065879145469772799654093 774704679551164799870285)
  ·
    refine ⟨290514254831686799951357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 774704679551164799870285 290514254831686799951357)
    ·
      refine ⟨108942845561882549981759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 290514254831686799951357 108942845561882549981759)
      ·
        refine ⟨163414268342823824972639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108942845561882549981759 163414268342823824972639)
        ·
          refine ⟨245121402514235737458959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 163414268342823824972639 245121402514235737458959)
          ·
            refine ⟨367682103771353606188439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 245121402514235737458959 367682103771353606188439)
            ·
              refine ⟨551523155657030409282659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 367682103771353606188439 551523155657030409282659)
              ·
                refine ⟨827284733485545613923989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 551523155657030409282659 827284733485545613923989)
                ·
                  refine ⟨38778971882134950652687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 827284733485545613923989 38778971882134950652687)
                  ·
                    rfl

theorem cell20_84962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 1, 6].length) (baseStart_84962 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_84962 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_84962 prefixEnd_84962 := by exact prefixLift 84962
  have htrace : WordTrace (prefixWord ++ tailWord_84962) baseStart_84962 baseEnd_84962 := by
    simpa [prefixWord, tailWord_84962, baseEnd_84962] using wordTrace_append hprefix tailTrace_84962
  have hstable : (prefixWord ++ tailWord_84962).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_84962).length < 2 ^ (prefixWord ++ tailWord_84962).sum := by decide
  have hdescent : baseEnd_84962 < baseStart_84962 := by decide
  rcases family_descends (prefixWord ++ tailWord_84962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_84993 : List Nat := [1, 2, 4, 1, 2, 4, 1, 2, 3]
def baseStart_84993 : Nat := 118140960795 + 84993 * 2 ^ 59
def prefixEnd_84993 : Nat := 4983230072969 + 3 ^ 40 * 84993 * 2
def baseEnd_84993 : Nat := 38793121126836620619227

theorem tailTrace_84993 : CollatzResearch.WordTrace tailWord_84993 prefixEnd_84993 38793121126836620619227 := by
  unfold tailWord_84993
  simp only [CollatzResearch.WordTrace]
  refine ⟨3099949381092351493859633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2066632920728234329239755 3099949381092351493859633)
  ·
    refine ⟨2324962035819263620394725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3099949381092351493859633 2324962035819263620394725)
    ·
      refine ⟨435930381716111928824011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2324962035819263620394725 435930381716111928824011)
      ·
        refine ⟨653895572574167893236017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 435930381716111928824011 653895572574167893236017)
        ·
          refine ⟨490421679430625919927013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 653895572574167893236017 490421679430625919927013)
          ·
            refine ⟨91954064893242359986315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 490421679430625919927013 91954064893242359986315)
            ·
              refine ⟨137931097339863539979473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91954064893242359986315 137931097339863539979473)
              ·
                refine ⟨103448323004897654984605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 137931097339863539979473 103448323004897654984605)
                ·
                  refine ⟨38793121126836620619227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 103448323004897654984605 38793121126836620619227)
                  ·
                    rfl

theorem cell20_84993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 4, 1, 2, 3].length) (baseStart_84993 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_84993 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_84993 prefixEnd_84993 := by exact prefixLift 84993
  have htrace : WordTrace (prefixWord ++ tailWord_84993) baseStart_84993 baseEnd_84993 := by
    simpa [prefixWord, tailWord_84993, baseEnd_84993] using wordTrace_append hprefix tailTrace_84993
  have hstable : (prefixWord ++ tailWord_84993).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_84993).length < 2 ^ (prefixWord ++ tailWord_84993).sum := by decide
  have hdescent : baseEnd_84993 < baseStart_84993 := by decide
  rcases family_descends (prefixWord ++ tailWord_84993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_84997 : List Nat := [1, 3, 1, 1, 2, 3, 3, 1, 5]
def baseStart_84997 : Nat := 118140960795 + 84997 * 2 ^ 59
def prefixEnd_84997 : Nat := 4983230072969 + 3 ^ 40 * 84997 * 2
def baseEnd_84997 : Nat := 38794946835830384485877

theorem tailTrace_84997 : CollatzResearch.WordTrace tailWord_84997 prefixEnd_84997 38794946835830384485877 := by
  unfold tailWord_84997
  simp only [CollatzResearch.WordTrace]
  refine ⟨3100095273077860177005245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2066730182051906784670163 3100095273077860177005245)
  ·
    refine ⟨1162535727404197566376967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3100095273077860177005245 1162535727404197566376967)
    ·
      refine ⟨1743803591106296349565451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1162535727404197566376967 1743803591106296349565451)
      ·
        refine ⟨2615705386659444524348177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1743803591106296349565451 2615705386659444524348177)
        ·
          refine ⟨1961779039994583393261133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2615705386659444524348177 1961779039994583393261133)
          ·
            refine ⟨735667139997968772472925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1961779039994583393261133 735667139997968772472925)
            ·
              refine ⟨275875177499238289677347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 735667139997968772472925 275875177499238289677347)
              ·
                refine ⟨413812766248857434516021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 275875177499238289677347 413812766248857434516021)
                ·
                  refine ⟨38794946835830384485877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 413812766248857434516021 38794946835830384485877)
                  ·
                    rfl

theorem cell20_84997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 3, 1, 5].length) (baseStart_84997 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_84997 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_84997 prefixEnd_84997 := by exact prefixLift 84997
  have htrace : WordTrace (prefixWord ++ tailWord_84997) baseStart_84997 baseEnd_84997 := by
    simpa [prefixWord, tailWord_84997, baseEnd_84997] using wordTrace_append hprefix tailTrace_84997
  have hstable : (prefixWord ++ tailWord_84997).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_84997).length < 2 ^ (prefixWord ++ tailWord_84997).sum := by decide
  have hdescent : baseEnd_84997 < baseStart_84997 := by decide
  rcases family_descends (prefixWord ++ tailWord_84997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_85000 : List Nat := [2, 1, 3, 2, 1, 3, 2, 4, 2]
def baseStart_85000 : Nat := 118140960795 + 85000 * 2 ^ 59
def prefixEnd_85000 : Nat := 4983230072969 + 3 ^ 40 * 85000 * 2
def baseEnd_85000 : Nat := 38796316117575707385865

theorem tailTrace_85000 : CollatzResearch.WordTrace tailWord_85000 prefixEnd_85000 38796316117575707385865 := by
  unfold tailWord_85000
  simp only [CollatzResearch.WordTrace]
  refine ⟨1550102346033495844682227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2066803128044661126242969 1550102346033495844682227)
  ·
    refine ⟨2325153519050243767023341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1550102346033495844682227 2325153519050243767023341)
    ·
      refine ⟨871932569643841412633753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2325153519050243767023341 871932569643841412633753)
      ·
        refine ⟨653949427232881059475315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 871932569643841412633753 653949427232881059475315)
        ·
          refine ⟨980924140849321589212973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 653949427232881059475315 980924140849321589212973)
          ·
            refine ⟨367846552818495595954865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 980924140849321589212973 367846552818495595954865)
            ·
              refine ⟨275884914613871696966149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 367846552818495595954865 275884914613871696966149)
              ·
                refine ⟨51728421490100943181153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 275884914613871696966149 51728421490100943181153)
                ·
                  refine ⟨38796316117575707385865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51728421490100943181153 38796316117575707385865)
                  ·
                    rfl

theorem cell20_85000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 2, 4, 2].length) (baseStart_85000 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_85000 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_85000 prefixEnd_85000 := by exact prefixLift 85000
  have htrace : WordTrace (prefixWord ++ tailWord_85000) baseStart_85000 baseEnd_85000 := by
    simpa [prefixWord, tailWord_85000, baseEnd_85000] using wordTrace_append hprefix tailTrace_85000
  have hstable : (prefixWord ++ tailWord_85000).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_85000).length < 2 ^ (prefixWord ++ tailWord_85000).sum := by decide
  have hdescent : baseEnd_85000 < baseStart_85000 := by decide
  rcases family_descends (prefixWord ++ tailWord_85000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_85011 : List Nat := [1, 1, 1, 2, 1, 4, 1, 9]
def baseStart_85011 : Nat := 118140960795 + 85011 * 2 ^ 59
def prefixEnd_85011 : Nat := 4983230072969 + 3 ^ 40 * 85011 * 2
def baseEnd_85011 : Nat := 12933778939102852673051

theorem tailTrace_85011 : CollatzResearch.WordTrace tailWord_85011 prefixEnd_85011 12933778939102852673051 := by
  unfold tailWord_85011
  simp only [CollatzResearch.WordTrace]
  refine ⟨3100605895027140568014887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2067070596684760378676591 3100605895027140568014887)
  ·
    refine ⟨4650908842540710852022331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3100605895027140568014887 4650908842540710852022331)
    ·
      refine ⟨6976363263811066278033497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4650908842540710852022331 6976363263811066278033497)
      ·
        refine ⟨5232272447858299708525123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6976363263811066278033497 5232272447858299708525123)
        ·
          refine ⟨7848408671787449562787685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5232272447858299708525123 7848408671787449562787685)
          ·
            refine ⟨1471576625960146793022691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7848408671787449562787685 1471576625960146793022691)
            ·
              refine ⟨2207364938940220189534037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1471576625960146793022691 2207364938940220189534037)
              ·
                refine ⟨12933778939102852673051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 2207364938940220189534037 12933778939102852673051)
                ·
                  rfl

theorem cell20_85011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 9].length) (baseStart_85011 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_85011 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_85011 prefixEnd_85011 := by exact prefixLift 85011
  have htrace : WordTrace (prefixWord ++ tailWord_85011) baseStart_85011 baseEnd_85011 := by
    simpa [prefixWord, tailWord_85011, baseEnd_85011] using wordTrace_append hprefix tailTrace_85011
  have hstable : (prefixWord ++ tailWord_85011).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_85011).length < 2 ^ (prefixWord ++ tailWord_85011).sum := by decide
  have hdescent : baseEnd_85011 < baseStart_85011 := by decide
  rcases family_descends (prefixWord ++ tailWord_85011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_85034 : List Nat := [3, 1, 4, 1, 3, 2, 1, 3, 2]
def baseStart_85034 : Nat := 118140960795 + 85034 * 2 ^ 59
def prefixEnd_85034 : Nat := 4983230072969 + 3 ^ 40 * 85034 * 2
def baseEnd_85034 : Nat := 38811834644022700252393

theorem tailTrace_85034 : CollatzResearch.WordTrace tailWord_85034 prefixEnd_85034 38811834644022700252393 := by
  unfold tailWord_85034
  simp only [CollatzResearch.WordTrace]
  refine ⟨775361193485953874025539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2067629849295876997401437 775361193485953874025539)
  ·
    refine ⟨1163041790228930811038309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 775361193485953874025539 1163041790228930811038309)
    ·
      refine ⟨218070335667924527069683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1163041790228930811038309 218070335667924527069683)
      ·
        refine ⟨327105503501886790604525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 218070335667924527069683 327105503501886790604525)
        ·
          refine ⟨122664563813207546476697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 327105503501886790604525 122664563813207546476697)
          ·
            refine ⟨91998422859905659857523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 122664563813207546476697 91998422859905659857523)
            ·
              refine ⟨137997634289858489786285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91998422859905659857523 137997634289858489786285)
              ·
                refine ⟨51749112858696933669857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 137997634289858489786285 51749112858696933669857)
                ·
                  refine ⟨38811834644022700252393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51749112858696933669857 38811834644022700252393)
                  ·
                    rfl

theorem cell20_85034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 2, 1, 3, 2].length) (baseStart_85034 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_85034 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_85034 prefixEnd_85034 := by exact prefixLift 85034
  have htrace : WordTrace (prefixWord ++ tailWord_85034) baseStart_85034 baseEnd_85034 := by
    simpa [prefixWord, tailWord_85034, baseEnd_85034] using wordTrace_append hprefix tailTrace_85034
  have hstable : (prefixWord ++ tailWord_85034).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_85034).length < 2 ^ (prefixWord ++ tailWord_85034).sum := by decide
  have hdescent : baseEnd_85034 < baseStart_85034 := by decide
  rcases family_descends (prefixWord ++ tailWord_85034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_85062 : List Nat := [6, 1, 1, 1, 1, 3, 2, 5]
def baseStart_85062 : Nat := 118140960795 + 85062 * 2 ^ 59
def prefixEnd_85062 : Nat := 4983230072969 + 3 ^ 40 * 85062 * 2
def baseEnd_85062 : Nat := 12941538202326349106315

theorem tailTrace_85062 : CollatzResearch.WordTrace tailWord_85062 prefixEnd_85062 12941538202326349106315 := by
  unfold tailWord_85062
  simp only [CollatzResearch.WordTrace]
  refine ⟨96952063057574258691295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 2068310678561584185414293 96952063057574258691295)
  ·
    refine ⟨145428094586361388036943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96952063057574258691295 145428094586361388036943)
    ·
      refine ⟨218142141879542082055415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145428094586361388036943 218142141879542082055415)
      ·
        refine ⟨327213212819313123083123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 218142141879542082055415 327213212819313123083123)
        ·
          refine ⟨490819819228969684624685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 327213212819313123083123 490819819228969684624685)
          ·
            refine ⟨184057432210863631734257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 490819819228969684624685 184057432210863631734257)
            ·
              refine ⟨138043074158147723800693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 184057432210863631734257 138043074158147723800693)
              ·
                refine ⟨12941538202326349106315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 138043074158147723800693 12941538202326349106315)
                ·
                  rfl

theorem cell20_85062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 2, 5].length) (baseStart_85062 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_85062 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_85062 prefixEnd_85062 := by exact prefixLift 85062
  have htrace : WordTrace (prefixWord ++ tailWord_85062) baseStart_85062 baseEnd_85062 := by
    simpa [prefixWord, tailWord_85062, baseEnd_85062] using wordTrace_append hprefix tailTrace_85062
  have hstable : (prefixWord ++ tailWord_85062).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_85062).length < 2 ^ (prefixWord ++ tailWord_85062).sum := by decide
  have hdescent : baseEnd_85062 < baseStart_85062 := by decide
  rcases family_descends (prefixWord ++ tailWord_85062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_85069 : List Nat := [1, 6, 1, 1, 1, 3, 1, 3, 3]
def baseStart_85069 : Nat := 118140960795 + 85069 * 2 ^ 59
def prefixEnd_85069 : Nat := 4983230072969 + 3 ^ 40 * 85069 * 2
def baseEnd_85069 : Nat := 38827809597718134085583

theorem tailTrace_85069 : CollatzResearch.WordTrace tailWord_85069 prefixEnd_85069 38827809597718134085583 := by
  unfold tailWord_85069
  simp only [CollatzResearch.WordTrace]
  refine ⟨3102721328817016473626261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2068480885878010982417507 3102721328817016473626261)
  ·
    refine ⟨145440062288297647201231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 3102721328817016473626261 145440062288297647201231)
    ·
      refine ⟨218160093432446470801847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145440062288297647201231 218160093432446470801847)
      ·
        refine ⟨327240140148669706202771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 218160093432446470801847 327240140148669706202771)
        ·
          refine ⟨490860210223004559304157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 327240140148669706202771 490860210223004559304157)
          ·
            refine ⟨184072578833626709739059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 490860210223004559304157 184072578833626709739059)
            ·
              refine ⟨276108868250440064608589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 184072578833626709739059 276108868250440064608589)
              ·
                refine ⟨103540825593915024228221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 276108868250440064608589 103540825593915024228221)
                ·
                  refine ⟨38827809597718134085583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 103540825593915024228221 38827809597718134085583)
                  ·
                    rfl

theorem cell20_85069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 1, 3, 3].length) (baseStart_85069 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_85069 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_85069 prefixEnd_85069 := by exact prefixLift 85069
  have htrace : WordTrace (prefixWord ++ tailWord_85069) baseStart_85069 baseEnd_85069 := by
    simpa [prefixWord, tailWord_85069, baseEnd_85069] using wordTrace_append hprefix tailTrace_85069
  have hstable : (prefixWord ++ tailWord_85069).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_85069).length < 2 ^ (prefixWord ++ tailWord_85069).sum := by decide
  have hdescent : baseEnd_85069 < baseStart_85069 := by decide
  rcases family_descends (prefixWord ++ tailWord_85069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_85080 : List Nat := [2, 1, 2, 2, 1, 3, 2, 1, 6]
def baseStart_85080 : Nat := 118140960795 + 85080 * 2 ^ 59
def prefixEnd_85080 : Nat := 4983230072969 + 3 ^ 40 * 85080 * 2
def baseEnd_85080 : Nat := 38832830297450984718871

theorem tailTrace_85080 : CollatzResearch.WordTrace tailWord_85080 prefixEnd_85080 38832830297450984718871 := by
  unfold tailWord_85080
  simp only [CollatzResearch.WordTrace]
  refine ⟨1551561265888582676138347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2068748354518110234851129 1551561265888582676138347)
  ·
    refine ⟨2327341898832874014207521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1551561265888582676138347 2327341898832874014207521)
    ·
      refine ⟨1745506424124655510655641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2327341898832874014207521 1745506424124655510655641)
      ·
        refine ⟨1309129818093491632991731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1745506424124655510655641 1309129818093491632991731)
        ·
          refine ⟨1963694727140237449487597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1309129818093491632991731 1963694727140237449487597)
          ·
            refine ⟨736385522677589043557849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1963694727140237449487597 736385522677589043557849)
            ·
              refine ⟨552289142008191782668387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 736385522677589043557849 552289142008191782668387)
              ·
                refine ⟨828433713012287674002581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 552289142008191782668387 828433713012287674002581)
                ·
                  refine ⟨38832830297450984718871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 828433713012287674002581 38832830297450984718871)
                  ·
                    rfl

theorem cell20_85080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 1, 6].length) (baseStart_85080 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_85080 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_85080 prefixEnd_85080 := by exact prefixLift 85080
  have htrace : WordTrace (prefixWord ++ tailWord_85080) baseStart_85080 baseEnd_85080 := by
    simpa [prefixWord, tailWord_85080, baseEnd_85080] using wordTrace_append hprefix tailTrace_85080
  have hstable : (prefixWord ++ tailWord_85080).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_85080).length < 2 ^ (prefixWord ++ tailWord_85080).sum := by decide
  have hdescent : baseEnd_85080 < baseStart_85080 := by decide
  rcases family_descends (prefixWord ++ tailWord_85080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_85087 : List Nat := [1, 1, 2, 3, 1, 1, 3, 8]
def baseStart_85087 : Nat := 118140960795 + 85087 * 2 ^ 59
def prefixEnd_85087 : Nat := 4983230072969 + 3 ^ 40 * 85087 * 2
def baseEnd_85087 : Nat := 12945341762730023828503

theorem tailTrace_85087 : CollatzResearch.WordTrace tailWord_85087 prefixEnd_85087 12945341762730023828503 := by
  unfold tailWord_85087
  simp only [CollatzResearch.WordTrace]
  refine ⟨3103377842751805547781515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2068918561834537031854343 3103377842751805547781515)
  ·
    refine ⟨4655066764127708321672273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3103377842751805547781515 4655066764127708321672273)
    ·
      refine ⟨3491300073095781241254205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4655066764127708321672273 3491300073095781241254205)
      ·
        refine ⟨1309237527410917965470327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3491300073095781241254205 1309237527410917965470327)
        ·
          refine ⟨1963856291116376948205491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1309237527410917965470327 1963856291116376948205491)
          ·
            refine ⟨2945784436674565422308237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1963856291116376948205491 2945784436674565422308237)
            ·
              refine ⟨1104669163752962033365589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2945784436674565422308237 1104669163752962033365589)
              ·
                refine ⟨12945341762730023828503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1104669163752962033365589 12945341762730023828503)
                ·
                  rfl

theorem cell20_85087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 8].length) (baseStart_85087 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_85087 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_85087 prefixEnd_85087 := by exact prefixLift 85087
  have htrace : WordTrace (prefixWord ++ tailWord_85087) baseStart_85087 baseEnd_85087 := by
    simpa [prefixWord, tailWord_85087, baseEnd_85087] using wordTrace_append hprefix tailTrace_85087
  have hstable : (prefixWord ++ tailWord_85087).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_85087).length < 2 ^ (prefixWord ++ tailWord_85087).sum := by decide
  have hdescent : baseEnd_85087 < baseStart_85087 := by decide
  rcases family_descends (prefixWord ++ tailWord_85087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_85121 : List Nat := [1, 2, 4, 2, 2, 3, 1, 5]
def baseStart_85121 : Nat := 118140960795 + 85121 * 2 ^ 59
def prefixEnd_85121 : Nat := 4983230072969 + 3 ^ 40 * 85121 * 2
def baseEnd_85121 : Nat := 12950514604879021450679

theorem tailTrace_85121 : CollatzResearch.WordTrace tailWord_85121 prefixEnd_85121 12950514604879021450679 := by
  unfold tailWord_85121
  simp only [CollatzResearch.WordTrace]
  refine ⟨3104617924628629354519217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2069745283085752903012811 3104617924628629354519217)
  ·
    refine ⟨2328463443471472015889413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3104617924628629354519217 2328463443471472015889413)
    ·
      refine ⟨436586895650901002979265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2328463443471472015889413 436586895650901002979265)
      ·
        refine ⟨327440171738175752234449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 436586895650901002979265 327440171738175752234449)
        ·
          refine ⟨245580128803631814175837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 327440171738175752234449 245580128803631814175837)
          ·
            refine ⟨92092548301361930315939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 245580128803631814175837 92092548301361930315939)
            ·
              refine ⟨138138822452042895473909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92092548301361930315939 138138822452042895473909)
              ·
                refine ⟨12950514604879021450679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 138138822452042895473909 12950514604879021450679)
                ·
                  rfl

theorem cell20_85121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 3, 1, 5].length) (baseStart_85121 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_85121 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_85121 prefixEnd_85121 := by exact prefixLift 85121
  have htrace : WordTrace (prefixWord ++ tailWord_85121) baseStart_85121 baseEnd_85121 := by
    simpa [prefixWord, tailWord_85121, baseEnd_85121] using wordTrace_append hprefix tailTrace_85121
  have hstable : (prefixWord ++ tailWord_85121).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_85121).length < 2 ^ (prefixWord ++ tailWord_85121).sum := by decide
  have hdescent : baseEnd_85121 < baseStart_85121 := by decide
  rcases family_descends (prefixWord ++ tailWord_85121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_85149 : List Nat := [1, 4, 2, 1, 1, 2, 2, 2, 5]
def baseStart_85149 : Nat := 118140960795 + 85149 * 2 ^ 59
def prefixEnd_85149 : Nat := 4983230072969 + 3 ^ 40 * 85149 * 2
def baseEnd_85149 : Nat := 38864323777593411418589

theorem tailTrace_85149 : CollatzResearch.WordTrace tailWord_85149 prefixEnd_85149 38864323777593411418589 := by
  unfold tailWord_85149
  simp only [CollatzResearch.WordTrace]
  refine ⟨3105639168527190136538501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2070426112351460091025667 3105639168527190136538501)
  ·
    refine ⟨582307344098848150600969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3105639168527190136538501 582307344098848150600969)
    ·
      refine ⟨436730508074136112950727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 582307344098848150600969 436730508074136112950727)
      ·
        refine ⟨655095762111204169426091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 436730508074136112950727 655095762111204169426091)
        ·
          refine ⟨982643643166806254139137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 655095762111204169426091 982643643166806254139137)
          ·
            refine ⟨736982732375104690604353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 982643643166806254139137 736982732375104690604353)
            ·
              refine ⟨552737049281328517953265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 736982732375104690604353 552737049281328517953265)
              ·
                refine ⟨414552786960996388464949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 552737049281328517953265 414552786960996388464949)
                ·
                  refine ⟨38864323777593411418589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 414552786960996388464949 38864323777593411418589)
                  ·
                    rfl

theorem cell20_85149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 2, 5].length) (baseStart_85149 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_85149 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_85149 prefixEnd_85149 := by exact prefixLift 85149
  have htrace : WordTrace (prefixWord ++ tailWord_85149) baseStart_85149 baseEnd_85149 := by
    simpa [prefixWord, tailWord_85149, baseEnd_85149] using wordTrace_append hprefix tailTrace_85149
  have hstable : (prefixWord ++ tailWord_85149).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_85149).length < 2 ^ (prefixWord ++ tailWord_85149).sum := by decide
  have hdescent : baseEnd_85149 < baseStart_85149 := by decide
  rcases family_descends (prefixWord ++ tailWord_85149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_85152 : List Nat := [2, 1, 1, 4, 2, 1, 4, 3, 2]
def baseStart_85152 : Nat := 118140960795 + 85152 * 2 ^ 59
def prefixEnd_85152 : Nat := 4983230072969 + 3 ^ 40 * 85152 * 2
def baseEnd_85152 : Nat := 38865693059338734318577

theorem tailTrace_85152 : CollatzResearch.WordTrace tailWord_85152 prefixEnd_85152 38865693059338734318577 := by
  unfold tailWord_85152
  simp only [CollatzResearch.WordTrace]
  refine ⟨1552874293758160824448855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2070499058344214432598473 1552874293758160824448855)
  ·
    refine ⟨2329311440637241236673283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1552874293758160824448855 2329311440637241236673283)
    ·
      refine ⟨3493967160955861855009925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2329311440637241236673283 3493967160955861855009925)
      ·
        refine ⟨655118842679224097814361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3493967160955861855009925 655118842679224097814361)
        ·
          refine ⟨491339132009418073360771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 655118842679224097814361 491339132009418073360771)
          ·
            refine ⟨737008698014127110041157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 491339132009418073360771 737008698014127110041157)
            ·
              refine ⟨138189130877648833132717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 737008698014127110041157 138189130877648833132717)
              ·
                refine ⟨51820924079118312424769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 138189130877648833132717 51820924079118312424769)
                ·
                  refine ⟨38865693059338734318577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51820924079118312424769 38865693059338734318577)
                  ·
                    rfl

theorem cell20_85152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 4, 3, 2].length) (baseStart_85152 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_85152 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_85152 prefixEnd_85152 := by exact prefixLift 85152
  have htrace : WordTrace (prefixWord ++ tailWord_85152) baseStart_85152 baseEnd_85152 := by
    simpa [prefixWord, tailWord_85152, baseEnd_85152] using wordTrace_append hprefix tailTrace_85152
  have hstable : (prefixWord ++ tailWord_85152).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_85152).length < 2 ^ (prefixWord ++ tailWord_85152).sum := by decide
  have hdescent : baseEnd_85152 < baseStart_85152 := by decide
  rcases family_descends (prefixWord ++ tailWord_85152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_85162 : List Nat := [3, 1, 5, 1, 1, 3, 1, 2, 3]
def baseStart_85162 : Nat := 118140960795 + 85162 * 2 ^ 59
def prefixEnd_85162 : Nat := 4983230072969 + 3 ^ 40 * 85162 * 2
def baseEnd_85162 : Nat := 38870257331823143985203

theorem tailTrace_85162 : CollatzResearch.WordTrace tailWord_85162 prefixEnd_85162 38870257331823143985203 := by
  unfold tailWord_85162
  simp only [CollatzResearch.WordTrace]
  refine ⟨776528329370023339190435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2070742211653395571174493 776528329370023339190435)
  ·
    refine ⟨1164792494055035008785653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 776528329370023339190435 1164792494055035008785653)
    ·
      refine ⟨109199296317659532073655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1164792494055035008785653 109199296317659532073655)
      ·
        refine ⟨163798944476489298110483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109199296317659532073655 163798944476489298110483)
        ·
          refine ⟨245698416714733947165725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 163798944476489298110483 245698416714733947165725)
          ·
            refine ⟨92136906268025230187147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 245698416714733947165725 92136906268025230187147)
            ·
              refine ⟨138205359402037845280721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92136906268025230187147 138205359402037845280721)
              ·
                refine ⟨103654019551528383960541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 138205359402037845280721 103654019551528383960541)
                ·
                  refine ⟨38870257331823143985203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 103654019551528383960541 38870257331823143985203)
                  ·
                    rfl

theorem cell20_85162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 3, 1, 2, 3].length) (baseStart_85162 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_85162 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_85162 prefixEnd_85162 := by exact prefixLift 85162
  have htrace : WordTrace (prefixWord ++ tailWord_85162) baseStart_85162 baseEnd_85162 := by
    simpa [prefixWord, tailWord_85162, baseEnd_85162] using wordTrace_append hprefix tailTrace_85162
  have hstable : (prefixWord ++ tailWord_85162).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_85162).length < 2 ^ (prefixWord ++ tailWord_85162).sum := by decide
  have hdescent : baseEnd_85162 < baseStart_85162 := by decide
  rcases family_descends (prefixWord ++ tailWord_85162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_85283 : List Nat := [1, 1, 1, 4, 2, 5, 2, 2, 2]
def baseStart_85283 : Nat := 118140960795 + 85283 * 2 ^ 59
def prefixEnd_85283 : Nat := 4983230072969 + 3 ^ 40 * 85283 * 2
def baseEnd_85283 : Nat := 38925485028884500951375

theorem tailTrace_85283 : CollatzResearch.WordTrace tailWord_85283 prefixEnd_85283 38925485028884500951375 := by
  unfold tailWord_85283
  simp only [CollatzResearch.WordTrace]
  refine ⟨3110526550041731021916503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2073684366694487347944335 3110526550041731021916503)
  ·
    refine ⟨4665789825062596532874755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3110526550041731021916503 4665789825062596532874755)
    ·
      refine ⟨6998684737593894799312133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4665789825062596532874755 6998684737593894799312133)
      ·
        refine ⟨1312253388298855274871025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6998684737593894799312133 1312253388298855274871025)
        ·
          refine ⟨984190041224141456153269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1312253388298855274871025 984190041224141456153269)
          ·
            refine ⟨92267816364763261514369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 984190041224141456153269 92267816364763261514369)
            ·
              refine ⟨69200862273572446135777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 92267816364763261514369 69200862273572446135777)
              ·
                refine ⟨51900646705179334601833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69200862273572446135777 51900646705179334601833)
                ·
                  refine ⟨38925485028884500951375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51900646705179334601833 38925485028884500951375)
                  ·
                    rfl

theorem cell20_85283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 5, 2, 2, 2].length) (baseStart_85283 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_85283 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_85283 prefixEnd_85283 := by exact prefixLift 85283
  have htrace : WordTrace (prefixWord ++ tailWord_85283) baseStart_85283 baseEnd_85283 := by
    simpa [prefixWord, tailWord_85283, baseEnd_85283] using wordTrace_append hprefix tailTrace_85283
  have hstable : (prefixWord ++ tailWord_85283).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_85283).length < 2 ^ (prefixWord ++ tailWord_85283).sum := by decide
  have hdescent : baseEnd_85283 < baseStart_85283 := by decide
  rcases family_descends (prefixWord ++ tailWord_85283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_85308 : List Nat := [2, 2, 2, 2, 1, 3, 1, 1, 6]
def baseStart_85308 : Nat := 118140960795 + 85308 * 2 ^ 59
def prefixEnd_85308 : Nat := 4983230072969 + 3 ^ 40 * 85308 * 2
def baseEnd_85308 : Nat := 38936895710095525117939

theorem tailTrace_85308 : CollatzResearch.WordTrace tailWord_85308 prefixEnd_85308 38936895710095525117939 := by
  unfold tailWord_85308
  simp only [CollatzResearch.WordTrace]
  refine ⟨1555719187475580145788289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2074292249967440194384385 1555719187475580145788289)
  ·
    refine ⟨1166789390606685109341217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1555719187475580145788289 1166789390606685109341217)
    ·
      refine ⟨875092042955013832005913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1166789390606685109341217 875092042955013832005913)
      ·
        refine ⟨656319032216260374004435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 875092042955013832005913 656319032216260374004435)
        ·
          refine ⟨984478548324390561006653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 656319032216260374004435 984478548324390561006653)
          ·
            refine ⟨369179455621646460377495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 984478548324390561006653 369179455621646460377495)
            ·
              refine ⟨553769183432469690566243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 369179455621646460377495 553769183432469690566243)
              ·
                refine ⟨830653775148704535849365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 553769183432469690566243 830653775148704535849365)
                ·
                  refine ⟨38936895710095525117939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 830653775148704535849365 38936895710095525117939)
                  ·
                    rfl

theorem cell20_85308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 1, 6].length) (baseStart_85308 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_85308 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_85308 prefixEnd_85308 := by exact prefixLift 85308
  have htrace : WordTrace (prefixWord ++ tailWord_85308) baseStart_85308 baseEnd_85308 := by
    simpa [prefixWord, tailWord_85308, baseEnd_85308] using wordTrace_append hprefix tailTrace_85308
  have hstable : (prefixWord ++ tailWord_85308).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_85308).length < 2 ^ (prefixWord ++ tailWord_85308).sum := by decide
  have hdescent : baseEnd_85308 < baseStart_85308 := by decide
  rcases family_descends (prefixWord ++ tailWord_85308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_85380 : List Nat := [2, 3, 2, 1, 1, 3, 3, 3, 2]
def baseStart_85380 : Nat := 118140960795 + 85380 * 2 ^ 59
def prefixEnd_85380 : Nat := 4983230072969 + 3 ^ 40 * 85380 * 2
def baseEnd_85380 : Nat := 38969758471983274717645

theorem tailTrace_85380 : CollatzResearch.WordTrace tailWord_85380 prefixEnd_85380 38969758471983274717645 := by
  unfold tailWord_85380
  simp only [CollatzResearch.WordTrace]
  refine ⟨1557032215345158294098797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2076042953793544392131729 1557032215345158294098797)
  ·
    refine ⟨583887080754434360287049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1557032215345158294098797 583887080754434360287049)
    ·
      refine ⟨437915310565825770215287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 583887080754434360287049 437915310565825770215287)
      ·
        refine ⟨656872965848738655322931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 437915310565825770215287 656872965848738655322931)
        ·
          refine ⟨985309448773107982984397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 656872965848738655322931 985309448773107982984397)
          ·
            refine ⟨369491043289915493619149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 985309448773107982984397 369491043289915493619149)
            ·
              refine ⟨138559141233718310107181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 369491043289915493619149 138559141233718310107181)
              ·
                refine ⟨51959677962644366290193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 138559141233718310107181 51959677962644366290193)
                ·
                  refine ⟨38969758471983274717645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51959677962644366290193 38969758471983274717645)
                  ·
                    rfl

theorem cell20_85380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 3, 3, 2].length) (baseStart_85380 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_85380 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_85380 prefixEnd_85380 := by exact prefixLift 85380
  have htrace : WordTrace (prefixWord ++ tailWord_85380) baseStart_85380 baseEnd_85380 := by
    simpa [prefixWord, tailWord_85380, baseEnd_85380] using wordTrace_append hprefix tailTrace_85380
  have hstable : (prefixWord ++ tailWord_85380).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_85380).length < 2 ^ (prefixWord ++ tailWord_85380).sum := by decide
  have hdescent : baseEnd_85380 < baseStart_85380 := by decide
  rcases family_descends (prefixWord ++ tailWord_85380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_85401 : List Nat := [1, 2, 1, 2, 1, 7, 1, 1, 4]
def baseStart_85401 : Nat := 118140960795 + 85401 * 2 ^ 59
def prefixEnd_85401 : Nat := 4983230072969 + 3 ^ 40 * 85401 * 2
def baseEnd_85401 : Nat := 38979343444200535017559

theorem tailTrace_85401 : CollatzResearch.WordTrace tailWord_85401 prefixEnd_85401 38979343444200535017559 := by
  unfold tailWord_85401
  simp only [CollatzResearch.WordTrace]
  refine ⟨3114830363614237174712057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2076553575742824783141371 3114830363614237174712057)
  ·
    refine ⟨2336122772710677881034043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3114830363614237174712057 2336122772710677881034043)
    ·
      refine ⟨3504184159066016821551065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2336122772710677881034043 3504184159066016821551065)
      ·
        refine ⟨2628138119299512616163299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3504184159066016821551065 2628138119299512616163299)
        ·
          refine ⟨3942207178949268924244949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2628138119299512616163299 3942207178949268924244949)
          ·
            refine ⟨92395480756623490411991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 3942207178949268924244949 92395480756623490411991)
            ·
              refine ⟨138593221134935235617987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92395480756623490411991 138593221134935235617987)
              ·
                refine ⟨207889831702402853426981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 138593221134935235617987 207889831702402853426981)
                ·
                  refine ⟨38979343444200535017559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 207889831702402853426981 38979343444200535017559)
                  ·
                    rfl

theorem cell20_85401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 7, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 7, 1, 1, 4].length) (baseStart_85401 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_85401 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_85401 prefixEnd_85401 := by exact prefixLift 85401
  have htrace : WordTrace (prefixWord ++ tailWord_85401) baseStart_85401 baseEnd_85401 := by
    simpa [prefixWord, tailWord_85401, baseEnd_85401] using wordTrace_append hprefix tailTrace_85401
  have hstable : (prefixWord ++ tailWord_85401).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_85401).length < 2 ^ (prefixWord ++ tailWord_85401).sum := by decide
  have hdescent : baseEnd_85401 < baseStart_85401 := by decide
  rcases family_descends (prefixWord ++ tailWord_85401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_85442 : List Nat := [3, 5, 2, 1, 9]
def baseStart_85442 : Nat := 118140960795 + 85442 * 2 ^ 59
def prefixEnd_85442 : Nat := 4983230072969 + 3 ^ 40 * 85442 * 2
def baseEnd_85442 : Nat := 481457493350452032725

theorem tailTrace_85442 : CollatzResearch.WordTrace tailWord_85442 prefixEnd_85442 481457493350452032725 := by
  unfold tailWord_85442
  simp only [CollatzResearch.WordTrace]
  refine ⟨779081439116425294238645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2077550504310467451303053 779081439116425294238645)
  ·
    refine ⟨73038884917164871334873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 779081439116425294238645 73038884917164871334873)
    ·
      refine ⟨54779163687873653501155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73038884917164871334873 54779163687873653501155)
      ·
        refine ⟨82168745531810480251733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54779163687873653501155 82168745531810480251733)
        ·
          refine ⟨481457493350452032725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 82168745531810480251733 481457493350452032725)
          ·
            rfl

theorem cell20_85442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 9].length) (baseStart_85442 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_85442 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_85442 prefixEnd_85442 := by exact prefixLift 85442
  have htrace : WordTrace (prefixWord ++ tailWord_85442) baseStart_85442 baseEnd_85442 := by
    simpa [prefixWord, tailWord_85442, baseEnd_85442] using wordTrace_append hprefix tailTrace_85442
  have hstable : (prefixWord ++ tailWord_85442).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_85442).length < 2 ^ (prefixWord ++ tailWord_85442).sum := by decide
  have hdescent : baseEnd_85442 < baseStart_85442 := by decide
  rcases family_descends (prefixWord ++ tailWord_85442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_85477 : List Nat := [1, 3, 1, 5, 1, 2, 1, 2, 4]
def baseStart_85477 : Nat := 118140960795 + 85477 * 2 ^ 59
def prefixEnd_85477 : Nat := 4983230072969 + 3 ^ 40 * 85477 * 2
def baseEnd_85477 : Nat := 39014031915082048483915

theorem tailTrace_85477 : CollatzResearch.WordTrace tailWord_85477 prefixEnd_85477 39014031915082048483915 := by
  unfold tailWord_85477
  simp only [CollatzResearch.WordTrace]
  refine ⟨3117602311338902154478685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2078401540892601436319123 3117602311338902154478685)
  ·
    refine ⟨1169100866752088307929507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3117602311338902154478685 1169100866752088307929507)
    ·
      refine ⟨1753651300128132461894261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1169100866752088307929507 1753651300128132461894261)
      ·
        refine ⟨164404809387012418302587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1753651300128132461894261 164404809387012418302587)
        ·
          refine ⟨246607214080518627453881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 164404809387012418302587 246607214080518627453881)
          ·
            refine ⟨184955410560388970590411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 246607214080518627453881 184955410560388970590411)
            ·
              refine ⟨277433115840583455885617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 184955410560388970590411 277433115840583455885617)
              ·
                refine ⟨208074836880437591914213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 277433115840583455885617 208074836880437591914213)
                ·
                  refine ⟨39014031915082048483915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 208074836880437591914213 39014031915082048483915)
                  ·
                    rfl

theorem cell20_85477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 1, 2, 4].length) (baseStart_85477 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_85477 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_85477 prefixEnd_85477 := by exact prefixLift 85477
  have htrace : WordTrace (prefixWord ++ tailWord_85477) baseStart_85477 baseEnd_85477 := by
    simpa [prefixWord, tailWord_85477, baseEnd_85477] using wordTrace_append hprefix tailTrace_85477
  have hstable : (prefixWord ++ tailWord_85477).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_85477).length < 2 ^ (prefixWord ++ tailWord_85477).sum := by decide
  have hdescent : baseEnd_85477 < baseStart_85477 := by decide
  rcases family_descends (prefixWord ++ tailWord_85477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_85494 : List Nat := [5, 1, 1, 1, 2, 2, 1, 5, 2]
def baseStart_85494 : Nat := 118140960795 + 85494 * 2 ^ 59
def prefixEnd_85494 : Nat := 4983230072969 + 3 ^ 40 * 85494 * 2
def baseEnd_85494 : Nat := 39021791178305544917179

theorem tailTrace_85494 : CollatzResearch.WordTrace tailWord_85494 prefixEnd_85494 39021791178305544917179 := by
  unfold tailWord_85494
  simp only [CollatzResearch.WordTrace]
  refine ⟨194888897017332128615471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2078814901518209371898357 194888897017332128615471)
  ·
    refine ⟨292333345525998192923207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194888897017332128615471 292333345525998192923207)
    ·
      refine ⟨438500018288997289384811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 292333345525998192923207 438500018288997289384811)
      ·
        refine ⟨657750027433495934077217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 438500018288997289384811 657750027433495934077217)
        ·
          refine ⟨493312520575121950557913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 657750027433495934077217 493312520575121950557913)
          ·
            refine ⟨369984390431341462918435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 493312520575121950557913 369984390431341462918435)
            ·
              refine ⟨554976585647012194377653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 369984390431341462918435 554976585647012194377653)
              ·
                refine ⟨52029054904407393222905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 554976585647012194377653 52029054904407393222905)
                ·
                  refine ⟨39021791178305544917179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52029054904407393222905 39021791178305544917179)
                  ·
                    rfl

theorem cell20_85494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 5, 2].length) (baseStart_85494 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_85494 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_85494 prefixEnd_85494 := by exact prefixLift 85494
  have htrace : WordTrace (prefixWord ++ tailWord_85494) baseStart_85494 baseEnd_85494 := by
    simpa [prefixWord, tailWord_85494, baseEnd_85494] using wordTrace_append hprefix tailTrace_85494
  have hstable : (prefixWord ++ tailWord_85494).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_85494).length < 2 ^ (prefixWord ++ tailWord_85494).sum := by decide
  have hdescent : baseEnd_85494 < baseStart_85494 := by decide
  rcases family_descends (prefixWord ++ tailWord_85494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_85508 : List Nat := [2, 3, 2, 3, 2, 1, 1, 1, 5]
def baseStart_85508 : Nat := 118140960795 + 85508 * 2 ^ 59
def prefixEnd_85508 : Nat := 4983230072969 + 3 ^ 40 * 85508 * 2
def baseEnd_85508 : Nat := 39028181159783718450455

theorem tailTrace_85508 : CollatzResearch.WordTrace tailWord_85508 prefixEnd_85508 39028181159783718450455 := by
  unfold tailWord_85508
  simp only [CollatzResearch.WordTrace]
  refine ⟨1559366487113297224428589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2079155316151062965904785 1559366487113297224428589)
  ·
    refine ⟨584762432667486459160721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1559366487113297224428589 584762432667486459160721)
    ·
      refine ⟨438571824500614844370541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 584762432667486459160721 438571824500614844370541)
      ·
        refine ⟨164464434187730566638953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 438571824500614844370541 164464434187730566638953)
        ·
          refine ⟨123348325640797924979215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 164464434187730566638953 123348325640797924979215)
          ·
            refine ⟨185022488461196887468823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123348325640797924979215 185022488461196887468823)
            ·
              refine ⟨277533732691795331203235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 185022488461196887468823 277533732691795331203235)
              ·
                refine ⟨416300599037692996804853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 277533732691795331203235 416300599037692996804853)
                ·
                  refine ⟨39028181159783718450455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 416300599037692996804853 39028181159783718450455)
                  ·
                    rfl

theorem cell20_85508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 1, 1, 5].length) (baseStart_85508 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_85508 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_85508 prefixEnd_85508 := by exact prefixLift 85508
  have htrace : WordTrace (prefixWord ++ tailWord_85508) baseStart_85508 baseEnd_85508 := by
    simpa [prefixWord, tailWord_85508, baseEnd_85508] using wordTrace_append hprefix tailTrace_85508
  have hstable : (prefixWord ++ tailWord_85508).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_85508).length < 2 ^ (prefixWord ++ tailWord_85508).sum := by decide
  have hdescent : baseEnd_85508 < baseStart_85508 := by decide
  rcases family_descends (prefixWord ++ tailWord_85508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_85515 : List Nat := [1, 1, 1, 1, 8, 1, 2, 1, 4]
def baseStart_85515 : Nat := 118140960795 + 85515 * 2 ^ 59
def prefixEnd_85515 : Nat := 4983230072969 + 3 ^ 40 * 85515 * 2
def baseEnd_85515 : Nat := 39031376150522805217093

theorem tailTrace_85515 : CollatzResearch.WordTrace tailWord_85515 prefixEnd_85515 39031376150522805217093 := by
  unfold tailWord_85515
  simp only [CollatzResearch.WordTrace]
  refine ⟨3118988285201234644361999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2079325523467489762907999 3118988285201234644361999)
  ·
    refine ⟨4678482427801851966542999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3118988285201234644361999 4678482427801851966542999)
    ·
      refine ⟨7017723641702777949814499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4678482427801851966542999 7017723641702777949814499)
      ·
        refine ⟨10526585462554166924721749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7017723641702777949814499 10526585462554166924721749)
        ·
          refine ⟨123358423389306643649083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 10526585462554166924721749 123358423389306643649083)
          ·
            refine ⟨185037635083959965473625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123358423389306643649083 185037635083959965473625)
            ·
              refine ⟨138778226312969974105219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 185037635083959965473625 138778226312969974105219)
              ·
                refine ⟨208167339469454961157829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 138778226312969974105219 208167339469454961157829)
                ·
                  refine ⟨39031376150522805217093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 208167339469454961157829 39031376150522805217093)
                  ·
                    rfl

theorem cell20_85515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 2, 1, 4].length) (baseStart_85515 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_85515 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_85515 prefixEnd_85515 := by exact prefixLift 85515
  have htrace : WordTrace (prefixWord ++ tailWord_85515) baseStart_85515 baseEnd_85515 := by
    simpa [prefixWord, tailWord_85515, baseEnd_85515] using wordTrace_append hprefix tailTrace_85515
  have hstable : (prefixWord ++ tailWord_85515).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_85515).length < 2 ^ (prefixWord ++ tailWord_85515).sum := by decide
  have hdescent : baseEnd_85515 < baseStart_85515 := by decide
  rcases family_descends (prefixWord ++ tailWord_85515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_85539 : List Nat := [1, 1, 1, 4, 5, 2, 2, 4]
def baseStart_85539 : Nat := 118140960795 + 85539 * 2 ^ 59
def prefixEnd_85539 : Nat := 4983230072969 + 3 ^ 40 * 85539 * 2
def baseEnd_85539 : Nat := 13014110134828462805665

theorem tailTrace_85539 : CollatzResearch.WordTrace tailWord_85539 prefixEnd_85539 13014110134828462805665 := by
  unfold tailWord_85539
  simp only [CollatzResearch.WordTrace]
  refine ⟨3119863637114286743235671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2079909091409524495490447 3119863637114286743235671)
  ·
    refine ⟨4679795455671430114853507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3119863637114286743235671 4679795455671430114853507)
    ·
      refine ⟨7019693183507145172280261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4679795455671430114853507 7019693183507145172280261)
      ·
        refine ⟨1316192471907589719802549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7019693183507145172280261 1316192471907589719802549)
        ·
          refine ⟨123393044241336536231489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1316192471907589719802549 123393044241336536231489)
          ·
            refine ⟨92544783181002402173617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 123393044241336536231489 92544783181002402173617)
            ·
              refine ⟨69408587385751801630213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 92544783181002402173617 69408587385751801630213)
              ·
                refine ⟨13014110134828462805665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 69408587385751801630213 13014110134828462805665)
                ·
                  rfl

theorem cell20_85539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 2, 2, 4].length) (baseStart_85539 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_85539 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_85539 prefixEnd_85539 := by exact prefixLift 85539
  have htrace : WordTrace (prefixWord ++ tailWord_85539) baseStart_85539 baseEnd_85539 := by
    simpa [prefixWord, tailWord_85539, baseEnd_85539] using wordTrace_append hprefix tailTrace_85539
  have hstable : (prefixWord ++ tailWord_85539).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_85539).length < 2 ^ (prefixWord ++ tailWord_85539).sum := by decide
  have hdescent : baseEnd_85539 < baseStart_85539 := by decide
  rcases family_descends (prefixWord ++ tailWord_85539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_85622 : List Nat := [5, 1, 1, 2, 2, 1, 1, 4, 3]
def baseStart_85622 : Nat := 118140960795 + 85622 * 2 ^ 59
def prefixEnd_85622 : Nat := 4983230072969 + 3 ^ 40 * 85622 * 2
def baseEnd_85622 : Nat := 39080213866105988649989

theorem tailTrace_85622 : CollatzResearch.WordTrace tailWord_85622 prefixEnd_85622 39080213866105988649989 := by
  unfold tailWord_85622
  simp only [CollatzResearch.WordTrace]
  refine ⟨195180680988349494906695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2081927263875727945671413 195180680988349494906695)
  ·
    refine ⟨292771021482524242360043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195180680988349494906695 292771021482524242360043)
    ·
      refine ⟨439156532223786363540065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 292771021482524242360043 439156532223786363540065)
      ·
        refine ⟨329367399167839772655049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 439156532223786363540065 329367399167839772655049)
        ·
          refine ⟨247025549375879829491287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 329367399167839772655049 247025549375879829491287)
          ·
            refine ⟨370538324063819744236931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 247025549375879829491287 370538324063819744236931)
            ·
              refine ⟨555807486095729616355397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 370538324063819744236931 555807486095729616355397)
              ·
                refine ⟨104213903642949303066637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 555807486095729616355397 104213903642949303066637)
                ·
                  refine ⟨39080213866105988649989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 104213903642949303066637 39080213866105988649989)
                  ·
                    rfl

theorem cell20_85622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 4, 3].length) (baseStart_85622 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_85622 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_85622 prefixEnd_85622 := by exact prefixLift 85622
  have htrace : WordTrace (prefixWord ++ tailWord_85622) baseStart_85622 baseEnd_85622 := by
    simpa [prefixWord, tailWord_85622, baseEnd_85622] using wordTrace_append hprefix tailTrace_85622
  have hstable : (prefixWord ++ tailWord_85622).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_85622).length < 2 ^ (prefixWord ++ tailWord_85622).sum := by decide
  have hdescent : baseEnd_85622 < baseStart_85622 := by decide
  rcases family_descends (prefixWord ++ tailWord_85622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_85663 : List Nat := [1, 1, 2, 7, 1, 1, 2, 3, 2]
def baseStart_85663 : Nat := 118140960795 + 85663 * 2 ^ 59
def prefixEnd_85663 : Nat := 4983230072969 + 3 ^ 40 * 85663 * 2
def baseEnd_85663 : Nat := 39098927383292068283155

theorem tailTrace_85663 : CollatzResearch.WordTrace tailWord_85663 prefixEnd_85663 39098927383292068283155 := by
  unfold tailWord_85663
  simp only [CollatzResearch.WordTrace]
  refine ⟨3124386288665055920749643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2082924192443370613833095 3124386288665055920749643)
  ·
    refine ⟨4686579432997583881124465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3124386288665055920749643 4686579432997583881124465)
    ·
      refine ⟨3514934574748187910843349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4686579432997583881124465 3514934574748187910843349)
      ·
        refine ⟨82381279095660654160391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 3514934574748187910843349 82381279095660654160391)
        ·
          refine ⟨123571918643490981240587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82381279095660654160391 123571918643490981240587)
          ·
            refine ⟨185357877965236471860881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123571918643490981240587 185357877965236471860881)
            ·
              refine ⟨139018408473927353895661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 185357877965236471860881 139018408473927353895661)
              ·
                refine ⟨52131903177722757710873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 139018408473927353895661 52131903177722757710873)
                ·
                  refine ⟨39098927383292068283155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52131903177722757710873 39098927383292068283155)
                  ·
                    rfl

theorem cell20_85663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 2, 3, 2].length) (baseStart_85663 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_85663 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_85663 prefixEnd_85663 := by exact prefixLift 85663
  have htrace : WordTrace (prefixWord ++ tailWord_85663) baseStart_85663 baseEnd_85663 := by
    simpa [prefixWord, tailWord_85663, baseEnd_85663] using wordTrace_append hprefix tailTrace_85663
  have hstable : (prefixWord ++ tailWord_85663).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_85663).length < 2 ^ (prefixWord ++ tailWord_85663).sum := by decide
  have hdescent : baseEnd_85663 < baseStart_85663 := by decide
  rcases family_descends (prefixWord ++ tailWord_85663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_85667 : List Nat := [1, 1, 1, 4, 1, 1, 6, 3, 2]
def baseStart_85667 : Nat := 118140960795 + 85667 * 2 ^ 59
def prefixEnd_85667 : Nat := 4983230072969 + 3 ^ 40 * 85667 * 2
def baseEnd_85667 : Nat := 39100753092285832149805

theorem tailTrace_85667 : CollatzResearch.WordTrace tailWord_85667 prefixEnd_85667 39100753092285832149805 := by
  unfold tailWord_85667
  simp only [CollatzResearch.WordTrace]
  refine ⟨3124532180650564603895255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2083021453767043069263503 3124532180650564603895255)
  ·
    refine ⟨4686798270975846905842883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3124532180650564603895255 4686798270975846905842883)
    ·
      refine ⟨7030197406463770358764325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4686798270975846905842883 7030197406463770358764325)
      ·
        refine ⟨1318162013711956942268311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7030197406463770358764325 1318162013711956942268311)
        ·
          refine ⟨1977243020567935413402467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1318162013711956942268311 1977243020567935413402467)
          ·
            refine ⟨2965864530851903120103701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1977243020567935413402467 2965864530851903120103701)
            ·
              refine ⟨139024899883682958754861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 2965864530851903120103701 139024899883682958754861)
              ·
                refine ⟨52134337456381109533073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 139024899883682958754861 52134337456381109533073)
                ·
                  refine ⟨39100753092285832149805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52134337456381109533073 39100753092285832149805)
                  ·
                    rfl

theorem cell20_85667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 6, 3, 2].length) (baseStart_85667 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_85667 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_85667 prefixEnd_85667 := by exact prefixLift 85667
  have htrace : WordTrace (prefixWord ++ tailWord_85667) baseStart_85667 baseEnd_85667 := by
    simpa [prefixWord, tailWord_85667, baseEnd_85667] using wordTrace_append hprefix tailTrace_85667
  have hstable : (prefixWord ++ tailWord_85667).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_85667).length < 2 ^ (prefixWord ++ tailWord_85667).sum := by decide
  have hdescent : baseEnd_85667 < baseStart_85667 := by decide
  rcases family_descends (prefixWord ++ tailWord_85667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_85708 : List Nat := [2, 2, 1, 5, 3, 1, 2, 4]
def baseStart_85708 : Nat := 118140960795 + 85708 * 2 ^ 59
def prefixEnd_85708 : Nat := 4983230072969 + 3 ^ 40 * 85708 * 2
def baseEnd_85708 : Nat := 13039822203157303927657

theorem tailTrace_85708 : CollatzResearch.WordTrace tailWord_85708 prefixEnd_85708 13039822203157303927657 := by
  unfold tailWord_85708
  simp only [CollatzResearch.WordTrace]
  refine ⟨1563013786751014303068889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2084018382334685737425185 1563013786751014303068889)
  ·
    refine ⟨1172260340063260727301667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1563013786751014303068889 1172260340063260727301667)
    ·
      refine ⟨1758390510094891090952501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1172260340063260727301667 1758390510094891090952501)
      ·
        refine ⟨164849110321396039776797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1758390510094891090952501 164849110321396039776797)
        ·
          refine ⟨61818416370523514916299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 164849110321396039776797 61818416370523514916299)
          ·
            refine ⟨92727624555785272374449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61818416370523514916299 92727624555785272374449)
            ·
              refine ⟨69545718416838954280837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 92727624555785272374449 69545718416838954280837)
              ·
                refine ⟨13039822203157303927657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 69545718416838954280837 13039822203157303927657)
                ·
                  rfl

theorem cell20_85708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 1, 2, 4].length) (baseStart_85708 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_85708 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_85708 prefixEnd_85708 := by exact prefixLift 85708
  have htrace : WordTrace (prefixWord ++ tailWord_85708) baseStart_85708 baseEnd_85708 := by
    simpa [prefixWord, tailWord_85708, baseEnd_85708] using wordTrace_append hprefix tailTrace_85708
  have hstable : (prefixWord ++ tailWord_85708).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_85708).length < 2 ^ (prefixWord ++ tailWord_85708).sum := by decide
  have hdescent : baseEnd_85708 < baseStart_85708 := by decide
  rcases family_descends (prefixWord ++ tailWord_85708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_85722 : List Nat := [3, 1, 1, 2, 2, 5, 1, 3, 2]
def baseStart_85722 : Nat := 118140960795 + 85722 * 2 ^ 59
def prefixEnd_85722 : Nat := 4983230072969 + 3 ^ 40 * 85722 * 2
def baseEnd_85722 : Nat := 39125856590950085316247

theorem tailTrace_85722 : CollatzResearch.WordTrace tailWord_85722 prefixEnd_85722 39125856590950085316247 := by
  unfold tailWord_85722
  simp only [CollatzResearch.WordTrace]
  refine ⟨781634548862827249286855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2084358796967539331431613 781634548862827249286855)
  ·
    refine ⟨1172451823294240873930283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 781634548862827249286855 1172451823294240873930283)
    ·
      refine ⟨1758677734941361310895425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1172451823294240873930283 1758677734941361310895425)
      ·
        refine ⟨1319008301206020983171569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1758677734941361310895425 1319008301206020983171569)
        ·
          refine ⟨989256225904515737378677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1319008301206020983171569 989256225904515737378677)
          ·
            refine ⟨92742771178548350379251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 989256225904515737378677 92742771178548350379251)
            ·
              refine ⟨139114156767822525568877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92742771178548350379251 139114156767822525568877)
              ·
                refine ⟨52167808787933447088329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 139114156767822525568877 52167808787933447088329)
                ·
                  refine ⟨39125856590950085316247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52167808787933447088329 39125856590950085316247)
                  ·
                    rfl

theorem cell20_85722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 5, 1, 3, 2].length) (baseStart_85722 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_85722 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_85722 prefixEnd_85722 := by exact prefixLift 85722
  have htrace : WordTrace (prefixWord ++ tailWord_85722) baseStart_85722 baseEnd_85722 := by
    simpa [prefixWord, tailWord_85722, baseEnd_85722] using wordTrace_append hprefix tailTrace_85722
  have hstable : (prefixWord ++ tailWord_85722).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_85722).length < 2 ^ (prefixWord ++ tailWord_85722).sum := by decide
  have hdescent : baseEnd_85722 < baseStart_85722 := by decide
  rcases family_descends (prefixWord ++ tailWord_85722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_85740 : List Nat := [2, 2, 1, 1, 2, 2, 4, 1, 5]
def baseStart_85740 : Nat := 118140960795 + 85740 * 2 ^ 59
def prefixEnd_85740 : Nat := 4983230072969 + 3 ^ 40 * 85740 * 2
def baseEnd_85740 : Nat := 39134072281422022716173

theorem tailTrace_85740 : CollatzResearch.WordTrace tailWord_85740 prefixEnd_85740 39134072281422022716173 := by
  unfold tailWord_85740
  simp only [CollatzResearch.WordTrace]
  refine ⟨1563597354693049035651337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2084796472924065380868449 1563597354693049035651337)
  ·
    refine ⟨1172698016019786776738503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1563597354693049035651337 1172698016019786776738503)
    ·
      refine ⟨1759047024029680165107755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1172698016019786776738503 1759047024029680165107755)
      ·
        refine ⟨2638570536044520247661633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1759047024029680165107755 2638570536044520247661633)
        ·
          refine ⟨1978927902033390185746225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2638570536044520247661633 1978927902033390185746225)
          ·
            refine ⟨1484195926525042639309669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1978927902033390185746225 1484195926525042639309669)
            ·
              refine ⟨278286736223445494870563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1484195926525042639309669 278286736223445494870563)
              ·
                refine ⟨417430104335168242305845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 278286736223445494870563 417430104335168242305845)
                ·
                  refine ⟨39134072281422022716173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 417430104335168242305845 39134072281422022716173)
                  ·
                    rfl

theorem cell20_85740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 5].length) (baseStart_85740 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_85740 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_85740 prefixEnd_85740 := by exact prefixLift 85740
  have htrace : WordTrace (prefixWord ++ tailWord_85740) baseStart_85740 baseEnd_85740 := by
    simpa [prefixWord, tailWord_85740, baseEnd_85740] using wordTrace_append hprefix tailTrace_85740
  have hstable : (prefixWord ++ tailWord_85740).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_85740).length < 2 ^ (prefixWord ++ tailWord_85740).sum := by decide
  have hdescent : baseEnd_85740 < baseStart_85740 := by decide
  rcases family_descends (prefixWord ++ tailWord_85740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_85750 : List Nat := [5, 1, 1, 1, 1, 4, 2, 5]
def baseStart_85750 : Nat := 118140960795 + 85750 * 2 ^ 59
def prefixEnd_85750 : Nat := 4983230072969 + 3 ^ 40 * 85750 * 2
def baseEnd_85750 : Nat := 13046212184635477460933

theorem tailTrace_85750 : CollatzResearch.WordTrace tailWord_85750 prefixEnd_85750 13046212184635477460933 := by
  unfold tailWord_85750
  simp only [CollatzResearch.WordTrace]
  refine ⟨195472464959366861197919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2085039626233246519444469 195472464959366861197919)
  ·
    refine ⟨293208697439050291796879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195472464959366861197919 293208697439050291796879)
    ·
      refine ⟨439813046158575437695319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 293208697439050291796879 439813046158575437695319)
      ·
        refine ⟨659719569237863156542979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 439813046158575437695319 659719569237863156542979)
        ·
          refine ⟨989579353856794734814469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 659719569237863156542979 989579353856794734814469)
          ·
            refine ⟨185546128848149012777713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 989579353856794734814469 185546128848149012777713)
            ·
              refine ⟨139159596636111759583285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 185546128848149012777713 139159596636111759583285)
              ·
                refine ⟨13046212184635477460933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 139159596636111759583285 13046212184635477460933)
                ·
                  rfl

theorem cell20_85750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 2, 5].length) (baseStart_85750 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_85750 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_85750 prefixEnd_85750 := by exact prefixLift 85750
  have htrace : WordTrace (prefixWord ++ tailWord_85750) baseStart_85750 baseEnd_85750 := by
    simpa [prefixWord, tailWord_85750, baseEnd_85750] using wordTrace_append hprefix tailTrace_85750
  have hstable : (prefixWord ++ tailWord_85750).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_85750).length < 2 ^ (prefixWord ++ tailWord_85750).sum := by decide
  have hdescent : baseEnd_85750 < baseStart_85750 := by decide
  rcases family_descends (prefixWord ++ tailWord_85750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_85790 : List Nat := [4, 3, 2, 2, 2, 1, 2, 2, 2]
def baseStart_85790 : Nat := 118140960795 + 85790 * 2 ^ 59
def prefixEnd_85790 : Nat := 4983230072969 + 3 ^ 40 * 85790 * 2
def baseEnd_85790 : Nat := 39156893643844071049303

theorem tailTrace_85790 : CollatzResearch.WordTrace tailWord_85790 prefixEnd_85790 39156893643844071049303 := by
  unfold tailWord_85790
  simp only [CollatzResearch.WordTrace]
  refine ⟨391127294900619576327853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2086012239469971073748549 391127294900619576327853)
  ·
    refine ⟨146672735587732341122945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 391127294900619576327853 146672735587732341122945)
    ·
      refine ⟨110004551690799255842209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146672735587732341122945 110004551690799255842209)
      ·
        refine ⟨82503413768099441881657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110004551690799255842209 82503413768099441881657)
        ·
          refine ⟨61877560326074581411243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82503413768099441881657 61877560326074581411243)
          ·
            refine ⟨92816340489111872116865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61877560326074581411243 92816340489111872116865)
            ·
              refine ⟨69612255366833904087649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 92816340489111872116865 69612255366833904087649)
              ·
                refine ⟨52209191525125428065737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69612255366833904087649 52209191525125428065737)
                ·
                  refine ⟨39156893643844071049303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52209191525125428065737 39156893643844071049303)
                  ·
                    rfl

theorem cell20_85790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 1, 2, 2, 2].length) (baseStart_85790 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_85790 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_85790 prefixEnd_85790 := by exact prefixLift 85790
  have htrace : WordTrace (prefixWord ++ tailWord_85790) baseStart_85790 baseEnd_85790 := by
    simpa [prefixWord, tailWord_85790, baseEnd_85790] using wordTrace_append hprefix tailTrace_85790
  have hstable : (prefixWord ++ tailWord_85790).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_85790).length < 2 ^ (prefixWord ++ tailWord_85790).sum := by decide
  have hdescent : baseEnd_85790 < baseStart_85790 := by decide
  rcases family_descends (prefixWord ++ tailWord_85790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_85809 : List Nat := [1, 2, 2, 3, 2, 2, 3, 5]
def baseStart_85809 : Nat := 118140960795 + 85809 * 2 ^ 59
def prefixEnd_85809 : Nat := 4983230072969 + 3 ^ 40 * 85809 * 2
def baseEnd_85809 : Nat := 13055188587188149805297

theorem tailTrace_85809 : CollatzResearch.WordTrace tailWord_85809 prefixEnd_85809 13055188587188149805297 := by
  unfold tailWord_85809
  simp only [CollatzResearch.WordTrace]
  refine ⟨3129711346136122855564481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2086474230757415237042987 3129711346136122855564481)
  ·
    refine ⟨2347283509602092141673361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3129711346136122855564481 2347283509602092141673361)
    ·
      refine ⟨1760462632201569106255021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2347283509602092141673361 1760462632201569106255021)
      ·
        refine ⟨660173487075588414845633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1760462632201569106255021 660173487075588414845633)
        ·
          refine ⟨495130115306691311134225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 660173487075588414845633 495130115306691311134225)
          ·
            refine ⟨371347586480018483350669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 495130115306691311134225 371347586480018483350669)
            ·
              refine ⟨139255344930006931256501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 371347586480018483350669 139255344930006931256501)
              ·
                refine ⟨13055188587188149805297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 139255344930006931256501 13055188587188149805297)
                ·
                  rfl

theorem cell20_85809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 3, 5].length) (baseStart_85809 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_85809 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_85809 prefixEnd_85809 := by exact prefixLift 85809
  have htrace : WordTrace (prefixWord ++ tailWord_85809) baseStart_85809 baseEnd_85809 := by
    simpa [prefixWord, tailWord_85809, baseEnd_85809] using wordTrace_append hprefix tailTrace_85809
  have hstable : (prefixWord ++ tailWord_85809).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_85809).length < 2 ^ (prefixWord ++ tailWord_85809).sum := by decide
  have hdescent : baseEnd_85809 < baseStart_85809 := by decide
  rcases family_descends (prefixWord ++ tailWord_85809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_85812 : List Nat := [2, 5, 1, 1, 2, 1, 2, 3, 3]
def baseStart_85812 : Nat := 118140960795 + 85812 * 2 ^ 59
def prefixEnd_85812 : Nat := 4983230072969 + 3 ^ 40 * 85812 * 2
def baseEnd_85812 : Nat := 39166935043309772315879

theorem tailTrace_85812 : CollatzResearch.WordTrace tailWord_85812 prefixEnd_85812 39166935043309772315879 := by
  unfold tailWord_85812
  simp only [CollatzResearch.WordTrace]
  refine ⟨1564910382562627183961845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2086547176750169578615793 1564910382562627183961845)
  ·
    refine ⟨146710348365246298496423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1564910382562627183961845 146710348365246298496423)
    ·
      refine ⟨220065522547869447744635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146710348365246298496423 220065522547869447744635)
      ·
        refine ⟨330098283821804171616953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 220065522547869447744635 330098283821804171616953)
        ·
          refine ⟨247573712866353128712715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 330098283821804171616953 247573712866353128712715)
          ·
            refine ⟨371360569299529693069073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 247573712866353128712715 371360569299529693069073)
            ·
              refine ⟨278520426974647269801805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 371360569299529693069073 278520426974647269801805)
              ·
                refine ⟨104445160115492726175677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 278520426974647269801805 104445160115492726175677)
                ·
                  refine ⟨39166935043309772315879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 104445160115492726175677 39166935043309772315879)
                  ·
                    rfl

theorem cell20_85812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 2, 3, 3].length) (baseStart_85812 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_85812 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_85812 prefixEnd_85812 := by exact prefixLift 85812
  have htrace : WordTrace (prefixWord ++ tailWord_85812) baseStart_85812 baseEnd_85812 := by
    simpa [prefixWord, tailWord_85812, baseEnd_85812] using wordTrace_append hprefix tailTrace_85812
  have hstable : (prefixWord ++ tailWord_85812).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_85812).length < 2 ^ (prefixWord ++ tailWord_85812).sum := by decide
  have hdescent : baseEnd_85812 < baseStart_85812 := by decide
  rcases family_descends (prefixWord ++ tailWord_85812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_85836 : List Nat := [2, 2, 1, 3, 4, 1, 2, 3, 2]
def baseStart_85836 : Nat := 118140960795 + 85836 * 2 ^ 59
def prefixEnd_85836 : Nat := 4983230072969 + 3 ^ 40 * 85836 * 2
def baseEnd_85836 : Nat := 39177889297272355515781

theorem tailTrace_85836 : CollatzResearch.WordTrace tailWord_85836 prefixEnd_85836 39177889297272355515781 := by
  unfold tailWord_85836
  simp only [CollatzResearch.WordTrace]
  refine ⟨1565348058519153233398681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2087130744692204311198241 1565348058519153233398681)
  ·
    refine ⟨1174011043889364925049011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1565348058519153233398681 1174011043889364925049011)
    ·
      refine ⟨1761016565834047387573517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1174011043889364925049011 1761016565834047387573517)
      ·
        refine ⟨660381212187767770340069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1761016565834047387573517 660381212187767770340069)
        ·
          refine ⟨123821477285206456938763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 660381212187767770340069 123821477285206456938763)
          ·
            refine ⟨185732215927809685408145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123821477285206456938763 185732215927809685408145)
            ·
              refine ⟨139299161945857264056109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 185732215927809685408145 139299161945857264056109)
              ·
                refine ⟨52237185729696474021041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 139299161945857264056109 52237185729696474021041)
                ·
                  refine ⟨39177889297272355515781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52237185729696474021041 39177889297272355515781)
                  ·
                    rfl

theorem cell20_85836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 2, 3, 2].length) (baseStart_85836 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_85836 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_85836 prefixEnd_85836 := by exact prefixLift 85836
  have htrace : WordTrace (prefixWord ++ tailWord_85836) baseStart_85836 baseEnd_85836 := by
    simpa [prefixWord, tailWord_85836, baseEnd_85836] using wordTrace_append hprefix tailTrace_85836
  have hstable : (prefixWord ++ tailWord_85836).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_85836).length < 2 ^ (prefixWord ++ tailWord_85836).sum := by decide
  have hdescent : baseEnd_85836 < baseStart_85836 := by decide
  rcases family_descends (prefixWord ++ tailWord_85836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_85847 : List Nat := [1, 1, 3, 2, 5, 1, 7]
def baseStart_85847 : Nat := 118140960795 + 85847 * 2 ^ 59
def prefixEnd_85847 : Nat := 4983230072969 + 3 ^ 40 * 85847 * 2
def baseEnd_85847 : Nat := 4353656666333911794341

theorem tailTrace_85847 : CollatzResearch.WordTrace tailWord_85847 prefixEnd_85847 4353656666333911794341 := by
  unfold tailWord_85847
  simp only [CollatzResearch.WordTrace]
  refine ⟨3131097319998455345447795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2087398213332303563631863 3131097319998455345447795)
  ·
    refine ⟨4696645979997683018171693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3131097319998455345447795 4696645979997683018171693)
    ·
      refine ⟨1761242242499131131814385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4696645979997683018171693 1761242242499131131814385)
      ·
        refine ⟨1320931681874348348860789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1761242242499131131814385 1320931681874348348860789)
        ·
          refine ⟨123837345175720157705699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1320931681874348348860789 123837345175720157705699)
          ·
            refine ⟨185756017763580236558549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123837345175720157705699 185756017763580236558549)
            ·
              refine ⟨4353656666333911794341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 185756017763580236558549 4353656666333911794341)
              ·
                rfl

theorem cell20_85847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 7].length) (baseStart_85847 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_85847 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_85847 prefixEnd_85847 := by exact prefixLift 85847
  have htrace : WordTrace (prefixWord ++ tailWord_85847) baseStart_85847 baseEnd_85847 := by
    simpa [prefixWord, tailWord_85847, baseEnd_85847] using wordTrace_append hprefix tailTrace_85847
  have hstable : (prefixWord ++ tailWord_85847).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_85847).length < 2 ^ (prefixWord ++ tailWord_85847).sum := by decide
  have hdescent : baseEnd_85847 < baseStart_85847 := by decide
  rcases family_descends (prefixWord ++ tailWord_85847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_85892 : List Nat := [2, 3, 2, 1, 1, 1, 3, 2, 5]
def baseStart_85892 : Nat := 118140960795 + 85892 * 2 ^ 59
def prefixEnd_85892 : Nat := 4983230072969 + 3 ^ 40 * 85892 * 2
def baseEnd_85892 : Nat := 39203449223185049648885

theorem tailTrace_85892 : CollatzResearch.WordTrace tailWord_85892 prefixEnd_85892 39203449223185049648885 := by
  unfold tailWord_85892
  simp only [CollatzResearch.WordTrace]
  refine ⟨1566369302417714015417965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2088492403223618687223953 1566369302417714015417965)
  ·
    refine ⟨587388488406642755781737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1566369302417714015417965 587388488406642755781737)
    ·
      refine ⟨440541366304982066836303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 587388488406642755781737 440541366304982066836303)
      ·
        refine ⟨660812049457473100254455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 440541366304982066836303 660812049457473100254455)
        ·
          refine ⟨991218074186209650381683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 660812049457473100254455 991218074186209650381683)
          ·
            refine ⟨1486827111279314475572525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 991218074186209650381683 1486827111279314475572525)
            ·
              refine ⟨557560166729742928339697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1486827111279314475572525 557560166729742928339697)
              ·
                refine ⟨418170125047307196254773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 557560166729742928339697 418170125047307196254773)
                ·
                  refine ⟨39203449223185049648885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 418170125047307196254773 39203449223185049648885)
                  ·
                    rfl

theorem cell20_85892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 2, 5].length) (baseStart_85892 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_85892 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_85892 prefixEnd_85892 := by exact prefixLift 85892
  have htrace : WordTrace (prefixWord ++ tailWord_85892) baseStart_85892 baseEnd_85892 := by
    simpa [prefixWord, tailWord_85892, baseEnd_85892] using wordTrace_append hprefix tailTrace_85892
  have hstable : (prefixWord ++ tailWord_85892).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_85892).length < 2 ^ (prefixWord ++ tailWord_85892).sum := by decide
  have hdescent : baseEnd_85892 < baseStart_85892 := by decide
  rcases family_descends (prefixWord ++ tailWord_85892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_85912 : List Nat := [2, 1, 2, 6, 1, 2, 1, 1, 4]
def baseStart_85912 : Nat := 118140960795 + 85912 * 2 ^ 59
def prefixEnd_85912 : Nat := 4983230072969 + 3 ^ 40 * 85912 * 2
def baseEnd_85912 : Nat := 39212577768153868982137

theorem tailTrace_85912 : CollatzResearch.WordTrace tailWord_85912 prefixEnd_85912 39212577768153868982137 := by
  unfold tailWord_85912
  simp only [CollatzResearch.WordTrace]
  refine ⟨1566734032381485723281995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2088978709841980964375993 1566734032381485723281995)
  ·
    refine ⟨2350101048572228584922993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1566734032381485723281995 2350101048572228584922993)
    ·
      refine ⟨1762575786429171438692245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2350101048572228584922993 1762575786429171438692245)
      ·
        refine ⟨82620739988867411188699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 1762575786429171438692245 82620739988867411188699)
        ·
          refine ⟨123931109983301116783049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82620739988867411188699 123931109983301116783049)
          ·
            refine ⟨92948332487475837587287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 123931109983301116783049 92948332487475837587287)
            ·
              refine ⟨139422498731213756380931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92948332487475837587287 139422498731213756380931)
              ·
                refine ⟨209133748096820634571397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 139422498731213756380931 209133748096820634571397)
                ·
                  refine ⟨39212577768153868982137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 209133748096820634571397 39212577768153868982137)
                  ·
                    rfl

theorem cell20_85912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 2, 1, 1, 4].length) (baseStart_85912 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_85912 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_85912 prefixEnd_85912 := by exact prefixLift 85912
  have htrace : WordTrace (prefixWord ++ tailWord_85912) baseStart_85912 baseEnd_85912 := by
    simpa [prefixWord, tailWord_85912, baseEnd_85912] using wordTrace_append hprefix tailTrace_85912
  have hstable : (prefixWord ++ tailWord_85912).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_85912).length < 2 ^ (prefixWord ++ tailWord_85912).sum := by decide
  have hdescent : baseEnd_85912 < baseStart_85912 := by decide
  rcases family_descends (prefixWord ++ tailWord_85912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_85922 : List Nat := [3, 3, 1, 2, 4, 1, 2, 1, 3]
def baseStart_85922 : Nat := 118140960795 + 85922 * 2 ^ 59
def prefixEnd_85922 : Nat := 4983230072969 + 3 ^ 40 * 85922 * 2
def baseEnd_85922 : Nat := 39217142040638278648763

theorem tailTrace_85922 : CollatzResearch.WordTrace tailWord_85922 prefixEnd_85922 39217142040638278648763 := by
  unfold tailWord_85922
  simp only [CollatzResearch.WordTrace]
  refine ⟨783458198681685788607005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2089221863151162102952013 783458198681685788607005)
  ·
    refine ⟨293796824505632170727627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 783458198681685788607005 293796824505632170727627)
    ·
      refine ⟨440695236758448256091441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 293796824505632170727627 440695236758448256091441)
      ·
        refine ⟨330521427568836192068581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 440695236758448256091441 330521427568836192068581)
        ·
          refine ⟨61972767669156786012859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 330521427568836192068581 61972767669156786012859)
          ·
            refine ⟨92959151503735179019289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61972767669156786012859 92959151503735179019289)
            ·
              refine ⟨69719363627801384264467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 92959151503735179019289 69719363627801384264467)
              ·
                refine ⟨104579045441702076396701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69719363627801384264467 104579045441702076396701)
                ·
                  refine ⟨39217142040638278648763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 104579045441702076396701 39217142040638278648763)
                  ·
                    rfl

theorem cell20_85922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 1, 2, 1, 3].length) (baseStart_85922 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_85922 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_85922 prefixEnd_85922 := by exact prefixLift 85922
  have htrace : WordTrace (prefixWord ++ tailWord_85922) baseStart_85922 baseEnd_85922 := by
    simpa [prefixWord, tailWord_85922, baseEnd_85922] using wordTrace_append hprefix tailTrace_85922
  have hstable : (prefixWord ++ tailWord_85922).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_85922).length < 2 ^ (prefixWord ++ tailWord_85922).sum := by decide
  have hdescent : baseEnd_85922 < baseStart_85922 := by decide
  rcases family_descends (prefixWord ++ tailWord_85922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_85944 : List Nat := [2, 1, 2, 1, 2, 3, 1, 8]
def baseStart_85944 : Nat := 118140960795 + 85944 * 2 ^ 59
def prefixEnd_85944 : Nat := 4983230072969 + 3 ^ 40 * 85944 * 2
def baseEnd_85944 : Nat := 13075727813367993305113

theorem tailTrace_85944 : CollatzResearch.WordTrace tailWord_85944 prefixEnd_85944 13075727813367993305113 := by
  unfold tailWord_85944
  simp only [CollatzResearch.WordTrace]
  refine ⟨1567317600323520455864443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2089756800431360607819257 1567317600323520455864443)
  ·
    refine ⟨2350976400485280683796665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1567317600323520455864443 2350976400485280683796665)
    ·
      refine ⟨1763232300363960512847499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2350976400485280683796665 1763232300363960512847499)
      ·
        refine ⟨2644848450545940769271249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1763232300363960512847499 2644848450545940769271249)
        ·
          refine ⟨1983636337909455576953437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2644848450545940769271249 1983636337909455576953437)
          ·
            refine ⟨743863626716045841357539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1983636337909455576953437 743863626716045841357539)
            ·
              refine ⟨1115795440074068762036309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 743863626716045841357539 1115795440074068762036309)
              ·
                refine ⟨13075727813367993305113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1115795440074068762036309 13075727813367993305113)
                ·
                  rfl

theorem cell20_85944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 8].length) (baseStart_85944 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_85944 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_85944 prefixEnd_85944 := by exact prefixLift 85944
  have htrace : WordTrace (prefixWord ++ tailWord_85944) baseStart_85944 baseEnd_85944 := by
    simpa [prefixWord, tailWord_85944, baseEnd_85944] using wordTrace_append hprefix tailTrace_85944
  have hstable : (prefixWord ++ tailWord_85944).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_85944).length < 2 ^ (prefixWord ++ tailWord_85944).sum := by decide
  have hdescent : baseEnd_85944 < baseStart_85944 := by decide
  rcases family_descends (prefixWord ++ tailWord_85944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_85968 : List Nat := [2, 1, 1, 1, 1, 2, 5, 4, 3]
def baseStart_85968 : Nat := 118140960795 + 85968 * 2 ^ 59
def prefixEnd_85968 : Nat := 4983230072969 + 3 ^ 40 * 85968 * 2
def baseEnd_85968 : Nat := 39238137694066563115241

theorem tailTrace_85968 : CollatzResearch.WordTrace tailWord_85968 prefixEnd_85968 39238137694066563115241 := by
  unfold tailWord_85968
  simp only [CollatzResearch.WordTrace]
  refine ⟨1567755276280046505301279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2090340368373395340401705 1567755276280046505301279)
  ·
    refine ⟨2351632914420069757951919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1567755276280046505301279 2351632914420069757951919)
    ·
      refine ⟨3527449371630104636927879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2351632914420069757951919 3527449371630104636927879)
      ·
        refine ⟨5291174057445156955391819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3527449371630104636927879 5291174057445156955391819)
        ·
          refine ⟨7936761086167735433087729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5291174057445156955391819 7936761086167735433087729)
          ·
            refine ⟨5952570814625801574815797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7936761086167735433087729 5952570814625801574815797)
            ·
              refine ⟨558053513871168897638981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5952570814625801574815797 558053513871168897638981)
              ·
                refine ⟨104635033850844168307309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 558053513871168897638981 104635033850844168307309)
                ·
                  refine ⟨39238137694066563115241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 104635033850844168307309 39238137694066563115241)
                  ·
                    rfl

theorem cell20_85968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 4, 3].length) (baseStart_85968 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_85968 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_85968 prefixEnd_85968 := by exact prefixLift 85968
  have htrace : WordTrace (prefixWord ++ tailWord_85968) baseStart_85968 baseEnd_85968 := by
    simpa [prefixWord, tailWord_85968, baseEnd_85968] using wordTrace_append hprefix tailTrace_85968
  have hstable : (prefixWord ++ tailWord_85968).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_85968).length < 2 ^ (prefixWord ++ tailWord_85968).sum := by decide
  have hdescent : baseEnd_85968 < baseStart_85968 := by decide
  rcases family_descends (prefixWord ++ tailWord_85968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_85974 : List Nat := [5, 2, 1, 1, 4, 1, 1, 5]
def baseStart_85974 : Nat := 118140960795 + 85974 * 2 ^ 59
def prefixEnd_85974 : Nat := 4983230072969 + 3 ^ 40 * 85974 * 2
def baseEnd_85974 : Nat := 13080292085852402971739

theorem tailTrace_85974 : CollatzResearch.WordTrace tailWord_85974 prefixEnd_85974 13080292085852402971739 := by
  unfold tailWord_85974
  simp only [CollatzResearch.WordTrace]
  refine ⟨195983086908647252207561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2090486260358904023547317 195983086908647252207561)
  ·
    refine ⟨146987315181485439155671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 195983086908647252207561 146987315181485439155671)
    ·
      refine ⟨220480972772228158733507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146987315181485439155671 220480972772228158733507)
      ·
        refine ⟨330721459158342238100261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 220480972772228158733507 330721459158342238100261)
        ·
          refine ⟨62010273592189169643799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 330721459158342238100261 62010273592189169643799)
          ·
            refine ⟨93015410388283754465699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62010273592189169643799 93015410388283754465699)
            ·
              refine ⟨139523115582425631698549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93015410388283754465699 139523115582425631698549)
              ·
                refine ⟨13080292085852402971739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 139523115582425631698549 13080292085852402971739)
                ·
                  rfl

theorem cell20_85974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 1, 1, 5].length) (baseStart_85974 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_85974 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_85974 prefixEnd_85974 := by exact prefixLift 85974
  have htrace : WordTrace (prefixWord ++ tailWord_85974) baseStart_85974 baseEnd_85974 := by
    simpa [prefixWord, tailWord_85974, baseEnd_85974] using wordTrace_append hprefix tailTrace_85974
  have hstable : (prefixWord ++ tailWord_85974).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_85974).length < 2 ^ (prefixWord ++ tailWord_85974).sum := by decide
  have hdescent : baseEnd_85974 < baseStart_85974 := by decide
  rcases family_descends (prefixWord ++ tailWord_85974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_85975 : List Nat := [1, 1, 3, 2, 1, 1, 4, 3, 4]
def baseStart_85975 : Nat := 118140960795 + 85975 * 2 ^ 59
def prefixEnd_85975 : Nat := 4983230072969 + 3 ^ 40 * 85975 * 2
def baseEnd_85975 : Nat := 39241332684805649881879

theorem tailTrace_85975 : CollatzResearch.WordTrace tailWord_85975 prefixEnd_85975 39241332684805649881879 := by
  unfold tailWord_85975
  simp only [CollatzResearch.WordTrace]
  refine ⟨3135765863534733206107379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2090510575689822137404919 3135765863534733206107379)
  ·
    refine ⟨4703648795302099809161069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3135765863534733206107379 4703648795302099809161069)
    ·
      refine ⟨1763868298238287428435401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4703648795302099809161069 1763868298238287428435401)
      ·
        refine ⟨1322901223678715571326551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1763868298238287428435401 1322901223678715571326551)
        ·
          refine ⟨1984351835518073356989827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1322901223678715571326551 1984351835518073356989827)
          ·
            refine ⟨2976527753277110035484741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1984351835518073356989827 2976527753277110035484741)
            ·
              refine ⟨558098953739458131653389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2976527753277110035484741 558098953739458131653389)
              ·
                refine ⟨209287107652296799370021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 558098953739458131653389 209287107652296799370021)
                ·
                  refine ⟨39241332684805649881879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 209287107652296799370021 39241332684805649881879)
                  ·
                    rfl

theorem cell20_85975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 3, 4].length) (baseStart_85975 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_85975 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_85975 prefixEnd_85975 := by exact prefixLift 85975
  have htrace : WordTrace (prefixWord ++ tailWord_85975) baseStart_85975 baseEnd_85975 := by
    simpa [prefixWord, tailWord_85975, baseEnd_85975] using wordTrace_append hprefix tailTrace_85975
  have hstable : (prefixWord ++ tailWord_85975).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_85975).length < 2 ^ (prefixWord ++ tailWord_85975).sum := by decide
  have hdescent : baseEnd_85975 < baseStart_85975 := by decide
  rcases family_descends (prefixWord ++ tailWord_85975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_85978 : List Nat := [3, 1, 1, 2, 5, 2, 1, 5]
def baseStart_85978 : Nat := 118140960795 + 85978 * 2 ^ 59
def prefixEnd_85978 : Nat := 4983230072969 + 3 ^ 40 * 85978 * 2
def baseEnd_85978 : Nat := 13080900655516990927289

theorem tailTrace_85978 : CollatzResearch.WordTrace tailWord_85978 prefixEnd_85978 13080900655516990927289 := by
  unfold tailWord_85978
  simp only [CollatzResearch.WordTrace]
  refine ⟨783968820630966179616647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2090583521682576478977725 783968820630966179616647)
  ·
    refine ⟨1175953230946449269424971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 783968820630966179616647 1175953230946449269424971)
    ·
      refine ⟨1763929846419673904137457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1175953230946449269424971 1763929846419673904137457)
      ·
        refine ⟨1322947384814755428103093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1763929846419673904137457 1322947384814755428103093)
        ·
          refine ⟨124026317326383321384665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1322947384814755428103093 124026317326383321384665)
          ·
            refine ⟨93019737994787491038499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 124026317326383321384665 93019737994787491038499)
            ·
              refine ⟨139529606992181236557749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93019737994787491038499 139529606992181236557749)
              ·
                refine ⟨13080900655516990927289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 139529606992181236557749 13080900655516990927289)
                ·
                  rfl

theorem cell20_85978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 2, 1, 5].length) (baseStart_85978 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_85978 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_85978 prefixEnd_85978 := by exact prefixLift 85978
  have htrace : WordTrace (prefixWord ++ tailWord_85978) baseStart_85978 baseEnd_85978 := by
    simpa [prefixWord, tailWord_85978, baseEnd_85978] using wordTrace_append hprefix tailTrace_85978
  have hstable : (prefixWord ++ tailWord_85978).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_85978).length < 2 ^ (prefixWord ++ tailWord_85978).sum := by decide
  have hdescent : baseEnd_85978 < baseStart_85978 := by decide
  rcases family_descends (prefixWord ++ tailWord_85978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_85999 : List Nat := [1, 1, 2, 1, 4, 2, 5, 4]
def baseStart_85999 : Nat := 118140960795 + 85999 * 2 ^ 59
def prefixEnd_85999 : Nat := 4983230072969 + 3 ^ 40 * 85999 * 2
def baseEnd_85999 : Nat := 13084095646256077693927

theorem tailTrace_85999 : CollatzResearch.WordTrace tailWord_85999 prefixEnd_85999 13084095646256077693927 := by
  unfold tailWord_85999
  simp only [CollatzResearch.WordTrace]
  refine ⟨3136641215447785304981051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2091094143631856869987367 3136641215447785304981051)
  ·
    refine ⟨4704961823171677957471577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3136641215447785304981051 4704961823171677957471577)
    ·
      refine ⟨3528721367378758468103683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4704961823171677957471577 3528721367378758468103683)
      ·
        refine ⟨5293082051068137702155525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3528721367378758468103683 5293082051068137702155525)
        ·
          refine ⟨992452884575275819154161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5293082051068137702155525 992452884575275819154161)
          ·
            refine ⟨744339663431456864365621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 992452884575275819154161 744339663431456864365621)
            ·
              refine ⟨69781843446699081034277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 744339663431456864365621 69781843446699081034277)
              ·
                refine ⟨13084095646256077693927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 69781843446699081034277 13084095646256077693927)
                ·
                  rfl

theorem cell20_85999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 5, 4].length) (baseStart_85999 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_85999 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_85999 prefixEnd_85999 := by exact prefixLift 85999
  have htrace : WordTrace (prefixWord ++ tailWord_85999) baseStart_85999 baseEnd_85999 := by
    simpa [prefixWord, tailWord_85999, baseEnd_85999] using wordTrace_append hprefix tailTrace_85999
  have hstable : (prefixWord ++ tailWord_85999).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_85999).length < 2 ^ (prefixWord ++ tailWord_85999).sum := by decide
  have hdescent : baseEnd_85999 < baseStart_85999 := by decide
  rcases family_descends (prefixWord ++ tailWord_85999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86009 : List Nat := [1, 2, 1, 3, 1, 5, 2, 3, 2]
def baseStart_86009 : Nat := 118140960795 + 86009 * 2 ^ 59
def prefixEnd_86009 : Nat := 4983230072969 + 3 ^ 40 * 86009 * 2
def baseEnd_86009 : Nat := 39256851211252642748407

theorem tailTrace_86009 : CollatzResearch.WordTrace tailWord_86009 prefixEnd_86009 39256851211252642748407 := by
  unfold tailWord_86009
  simp only [CollatzResearch.WordTrace]
  refine ⟨3137005945411557012845081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2091337296941038008563387 3137005945411557012845081)
  ·
    refine ⟨2352754459058667759633811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3137005945411557012845081 2352754459058667759633811)
    ·
      refine ⟨3529131688588001639450717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2352754459058667759633811 3529131688588001639450717)
      ·
        refine ⟨1323424383220500614794019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3529131688588001639450717 1323424383220500614794019)
        ·
          refine ⟨1985136574830750922191029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1323424383220500614794019 1985136574830750922191029)
          ·
            refine ⟨186106553890382898955409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1985136574830750922191029 186106553890382898955409)
            ·
              refine ⟨139579915417787174216557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 186106553890382898955409 139579915417787174216557)
              ·
                refine ⟨52342468281670190331209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 139579915417787174216557 52342468281670190331209)
                ·
                  refine ⟨39256851211252642748407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52342468281670190331209 39256851211252642748407)
                  ·
                    rfl

theorem cell20_86009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 2, 3, 2].length) (baseStart_86009 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_86009 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_86009 prefixEnd_86009 := by exact prefixLift 86009
  have htrace : WordTrace (prefixWord ++ tailWord_86009) baseStart_86009 baseEnd_86009 := by
    simpa [prefixWord, tailWord_86009, baseEnd_86009] using wordTrace_append hprefix tailTrace_86009
  have hstable : (prefixWord ++ tailWord_86009).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86009).length < 2 ^ (prefixWord ++ tailWord_86009).sum := by decide
  have hdescent : baseEnd_86009 < baseStart_86009 := by decide
  rcases family_descends (prefixWord ++ tailWord_86009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86022 : List Nat := [6, 2, 1, 2, 1, 1, 2, 1, 4]
def baseStart_86022 : Nat := 118140960795 + 86022 * 2 ^ 59
def prefixEnd_86022 : Nat := 4983230072969 + 3 ^ 40 * 86022 * 2
def baseEnd_86022 : Nat := 39262784765482375315021

theorem tailTrace_86022 : CollatzResearch.WordTrace tailWord_86022 prefixEnd_86022 39262784765482375315021 := by
  unfold tailWord_86022
  simp only [CollatzResearch.WordTrace]
  refine ⟨98046252948889382283385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 2091653396242973488712213 98046252948889382283385)
  ·
    refine ⟨73534689711667036712539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98046252948889382283385 73534689711667036712539)
    ·
      refine ⟨110302034567500555068809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73534689711667036712539 110302034567500555068809)
      ·
        refine ⟨82726525925625416301607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110302034567500555068809 82726525925625416301607)
        ·
          refine ⟨124089788888438124452411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82726525925625416301607 124089788888438124452411)
          ·
            refine ⟨186134683332657186678617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124089788888438124452411 186134683332657186678617)
            ·
              refine ⟨139601012499492890008963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 186134683332657186678617 139601012499492890008963)
              ·
                refine ⟨209401518749239335013445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 139601012499492890008963 209401518749239335013445)
                ·
                  refine ⟨39262784765482375315021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 209401518749239335013445 39262784765482375315021)
                  ·
                    rfl

theorem cell20_86022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 2, 1, 4].length) (baseStart_86022 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_86022 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_86022 prefixEnd_86022 := by exact prefixLift 86022
  have htrace : WordTrace (prefixWord ++ tailWord_86022) baseStart_86022 baseEnd_86022 := by
    simpa [prefixWord, tailWord_86022, baseEnd_86022] using wordTrace_append hprefix tailTrace_86022
  have hstable : (prefixWord ++ tailWord_86022).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86022).length < 2 ^ (prefixWord ++ tailWord_86022).sum := by decide
  have hdescent : baseEnd_86022 < baseStart_86022 := by decide
  rcases family_descends (prefixWord ++ tailWord_86022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86023 : List Nat := [1, 1, 4, 3, 1, 2, 3, 2, 3]
def baseStart_86023 : Nat := 118140960795 + 86023 * 2 ^ 59
def prefixEnd_86023 : Nat := 4983230072969 + 3 ^ 40 * 86023 * 2
def baseEnd_86023 : Nat := 39263241192730816281683

theorem tailTrace_86023 : CollatzResearch.WordTrace tailWord_86023 prefixEnd_86023 39263241192730816281683 := by
  unfold tailWord_86023
  simp only [CollatzResearch.WordTrace]
  refine ⟨3137516567360837403854723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2091677711573891602569815 3137516567360837403854723)
  ·
    refine ⟨4706274851041256105782085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3137516567360837403854723 4706274851041256105782085)
    ·
      refine ⟨882426534570235519834141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4706274851041256105782085 882426534570235519834141)
      ·
        refine ⟨330909950463838319937803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 882426534570235519834141 330909950463838319937803)
        ·
          refine ⟨496364925695757479906705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 330909950463838319937803 496364925695757479906705)
          ·
            refine ⟨372273694271818109930029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 496364925695757479906705 372273694271818109930029)
            ·
              refine ⟨139602635351931791223761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 372273694271818109930029 139602635351931791223761)
              ·
                refine ⟨104701976513948843417821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 139602635351931791223761 104701976513948843417821)
                ·
                  refine ⟨39263241192730816281683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 104701976513948843417821 39263241192730816281683)
                  ·
                    rfl

theorem cell20_86023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 3, 2, 3].length) (baseStart_86023 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_86023 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_86023 prefixEnd_86023 := by exact prefixLift 86023
  have htrace : WordTrace (prefixWord ++ tailWord_86023) baseStart_86023 baseEnd_86023 := by
    simpa [prefixWord, tailWord_86023, baseEnd_86023] using wordTrace_append hprefix tailTrace_86023
  have hstable : (prefixWord ++ tailWord_86023).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86023).length < 2 ^ (prefixWord ++ tailWord_86023).sum := by decide
  have hdescent : baseEnd_86023 < baseStart_86023 := by decide
  rcases family_descends (prefixWord ++ tailWord_86023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86030 : List Nat := [4, 1, 1, 2, 2, 1, 4, 1, 4]
def baseStart_86030 : Nat := 118140960795 + 86030 * 2 ^ 59
def prefixEnd_86030 : Nat := 4983230072969 + 3 ^ 40 * 86030 * 2
def baseEnd_86030 : Nat := 39266436183469903048321

theorem tailTrace_86030 : CollatzResearch.WordTrace tailWord_86030 prefixEnd_86030 39266436183469903048321 := by
  unfold tailWord_86030
  simp only [CollatzResearch.WordTrace]
  refine ⟨392221484791934699919943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2091847918890318399573029 392221484791934699919943)
  ·
    refine ⟨588332227187902049879915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 392221484791934699919943 588332227187902049879915)
    ·
      refine ⟨882498340781853074819873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 588332227187902049879915 882498340781853074819873)
      ·
        refine ⟨661873755586389806114905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 882498340781853074819873 661873755586389806114905)
        ·
          refine ⟨496405316689792354586179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 661873755586389806114905 496405316689792354586179)
          ·
            refine ⟨744607975034688531879269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 496405316689792354586179 744607975034688531879269)
            ·
              refine ⟨139613995319004099727363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 744607975034688531879269 139613995319004099727363)
              ·
                refine ⟨209420992978506149591045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 139613995319004099727363 209420992978506149591045)
                ·
                  refine ⟨39266436183469903048321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 209420992978506149591045 39266436183469903048321)
                  ·
                    rfl

theorem cell20_86030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 4, 1, 4].length) (baseStart_86030 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_86030 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_86030 prefixEnd_86030 := by exact prefixLift 86030
  have htrace : WordTrace (prefixWord ++ tailWord_86030) baseStart_86030 baseEnd_86030 := by
    simpa [prefixWord, tailWord_86030, baseEnd_86030] using wordTrace_append hprefix tailTrace_86030
  have hstable : (prefixWord ++ tailWord_86030).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86030).length < 2 ^ (prefixWord ++ tailWord_86030).sum := by decide
  have hdescent : baseEnd_86030 < baseStart_86030 := by decide
  rcases family_descends (prefixWord ++ tailWord_86030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86036 : List Nat := [2, 4, 3, 2, 1, 1, 3, 1, 3]
def baseStart_86036 : Nat := 118140960795 + 86036 * 2 ^ 59
def prefixEnd_86036 : Nat := 4983230072969 + 3 ^ 40 * 86036 * 2
def baseEnd_86036 : Nat := 39269174746960548848297

theorem tailTrace_86036 : CollatzResearch.WordTrace tailWord_86036 prefixEnd_86036 39269174746960548848297 := by
  unfold tailWord_86036
  simp only [CollatzResearch.WordTrace]
  refine ⟨1568995358156870312038981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2091993810875827082718641 1568995358156870312038981)
  ·
    refine ⟨294186629654413183507309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1568995358156870312038981 294186629654413183507309)
    ·
      refine ⟨110319986120404943815241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 294186629654413183507309 110319986120404943815241)
      ·
        refine ⟨82739989590303707861431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110319986120404943815241 82739989590303707861431)
        ·
          refine ⟨124109984385455561792147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82739989590303707861431 124109984385455561792147)
          ·
            refine ⟨186164976578183342688221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124109984385455561792147 186164976578183342688221)
            ·
              refine ⟨69811866216818753508083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 186164976578183342688221 69811866216818753508083)
              ·
                refine ⟨104717799325228130262125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69811866216818753508083 104717799325228130262125)
                ·
                  refine ⟨39269174746960548848297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 104717799325228130262125 39269174746960548848297)
                  ·
                    rfl

theorem cell20_86036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 3, 1, 3].length) (baseStart_86036 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_86036 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_86036 prefixEnd_86036 := by exact prefixLift 86036
  have htrace : WordTrace (prefixWord ++ tailWord_86036) baseStart_86036 baseEnd_86036 := by
    simpa [prefixWord, tailWord_86036, baseEnd_86036] using wordTrace_append hprefix tailTrace_86036
  have hstable : (prefixWord ++ tailWord_86036).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86036).length < 2 ^ (prefixWord ++ tailWord_86036).sum := by decide
  have hdescent : baseEnd_86036 < baseStart_86036 := by decide
  rcases family_descends (prefixWord ++ tailWord_86036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86051 : List Nat := [1, 1, 1, 4, 3, 1, 1, 4, 4]
def baseStart_86051 : Nat := 118140960795 + 86051 * 2 ^ 59
def prefixEnd_86051 : Nat := 4983230072969 + 3 ^ 40 * 86051 * 2
def baseEnd_86051 : Nat := 39276021155687163348235

theorem tailTrace_86051 : CollatzResearch.WordTrace tailWord_86051 prefixEnd_86051 39276021155687163348235 := by
  unfold tailWord_86051
  simp only [CollatzResearch.WordTrace]
  refine ⟨3138537811259398185874007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2092358540839598790582671 3138537811259398185874007)
  ·
    refine ⟨4707806716889097278811011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3138537811259398185874007 4707806716889097278811011)
    ·
      refine ⟨7061710075333645918216517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4707806716889097278811011 7061710075333645918216517)
      ·
        refine ⟨1324070639125058609665597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7061710075333645918216517 1324070639125058609665597)
        ·
          refine ⟨496526489671896978624599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1324070639125058609665597 496526489671896978624599)
          ·
            refine ⟨744789734507845467936899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 496526489671896978624599 744789734507845467936899)
            ·
              refine ⟨1117184601761768201905349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 744789734507845467936899 1117184601761768201905349)
              ·
                refine ⟨209472112830331537857253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1117184601761768201905349 209472112830331537857253)
                ·
                  refine ⟨39276021155687163348235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 209472112830331537857253 39276021155687163348235)
                  ·
                    rfl

theorem cell20_86051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 4, 4].length) (baseStart_86051 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_86051 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_86051 prefixEnd_86051 := by exact prefixLift 86051
  have htrace : WordTrace (prefixWord ++ tailWord_86051) baseStart_86051 baseEnd_86051 := by
    simpa [prefixWord, tailWord_86051, baseEnd_86051] using wordTrace_append hprefix tailTrace_86051
  have hstable : (prefixWord ++ tailWord_86051).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86051).length < 2 ^ (prefixWord ++ tailWord_86051).sum := by decide
  have hdescent : baseEnd_86051 < baseStart_86051 := by decide
  rcases family_descends (prefixWord ++ tailWord_86051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86137 : List Nat := [1, 2, 1, 3, 4, 2, 2, 2, 3]
def baseStart_86137 : Nat := 118140960795 + 86137 * 2 ^ 59
def prefixEnd_86137 : Nat := 4983230072969 + 3 ^ 40 * 86137 * 2
def baseEnd_86137 : Nat := 39315273899053086481217

theorem tailTrace_86137 : CollatzResearch.WordTrace tailWord_86137 prefixEnd_86137 39315273899053086481217 := by
  unfold tailWord_86137
  simp only [CollatzResearch.WordTrace]
  refine ⟨3141674488947834873504665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2094449659298556582336443 3141674488947834873504665)
  ·
    refine ⟨2356255866710876155128499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3141674488947834873504665 2356255866710876155128499)
    ·
      refine ⟨3534383800066314232692749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2356255866710876155128499 3534383800066314232692749)
      ·
        refine ⟨1325393925024867837259781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3534383800066314232692749 1325393925024867837259781)
        ·
          refine ⟨248511360942162719486209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1325393925024867837259781 248511360942162719486209)
          ·
            refine ⟨186383520706622039614657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 248511360942162719486209 186383520706622039614657)
            ·
              refine ⟨139787640529966529710993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 186383520706622039614657 139787640529966529710993)
              ·
                refine ⟨104840730397474897283245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 139787640529966529710993 104840730397474897283245)
                ·
                  refine ⟨39315273899053086481217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 104840730397474897283245 39315273899053086481217)
                  ·
                    rfl

theorem cell20_86137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 2, 2, 3].length) (baseStart_86137 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_86137 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_86137 prefixEnd_86137 := by exact prefixLift 86137
  have htrace : WordTrace (prefixWord ++ tailWord_86137) baseStart_86137 baseEnd_86137 := by
    simpa [prefixWord, tailWord_86137, baseEnd_86137] using wordTrace_append hprefix tailTrace_86137
  have hstable : (prefixWord ++ tailWord_86137).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86137).length < 2 ^ (prefixWord ++ tailWord_86137).sum := by decide
  have hdescent : baseEnd_86137 < baseStart_86137 := by decide
  rcases family_descends (prefixWord ++ tailWord_86137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86140 : List Nat := [2, 2, 2, 1, 1, 6, 2, 2, 2]
def baseStart_86140 : Nat := 118140960795 + 86140 * 2 ^ 59
def prefixEnd_86140 : Nat := 4983230072969 + 3 ^ 40 * 86140 * 2
def baseEnd_86140 : Nat := 39316643180798409381205

theorem tailTrace_86140 : CollatzResearch.WordTrace tailWord_86140 prefixEnd_86140 39316643180798409381205 := by
  unfold tailWord_86140
  simp only [CollatzResearch.WordTrace]
  refine ⟨1570891953968483192931937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2094522605291310923909249 1570891953968483192931937)
  ·
    refine ⟨1178168965476362394698953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1570891953968483192931937 1178168965476362394698953)
    ·
      refine ⟨883626724107271796024215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1178168965476362394698953 883626724107271796024215)
      ·
        refine ⟨1325440086160907694036323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 883626724107271796024215 1325440086160907694036323)
        ·
          refine ⟨1988160129241361541054485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1325440086160907694036323 1988160129241361541054485)
          ·
            refine ⟨93195006058188822236929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 1988160129241361541054485 93195006058188822236929)
            ·
              refine ⟨69896254543641616677697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 93195006058188822236929 69896254543641616677697)
              ·
                refine ⟨52422190907731212508273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69896254543641616677697 52422190907731212508273)
                ·
                  refine ⟨39316643180798409381205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52422190907731212508273 39316643180798409381205)
                  ·
                    rfl

theorem cell20_86140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 6, 2, 2, 2].length) (baseStart_86140 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_86140 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_86140 prefixEnd_86140 := by exact prefixLift 86140
  have htrace : WordTrace (prefixWord ++ tailWord_86140) baseStart_86140 baseEnd_86140 := by
    simpa [prefixWord, tailWord_86140, baseEnd_86140] using wordTrace_append hprefix tailTrace_86140
  have hstable : (prefixWord ++ tailWord_86140).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86140).length < 2 ^ (prefixWord ++ tailWord_86140).sum := by decide
  have hdescent : baseEnd_86140 < baseStart_86140 := by decide
  rcases family_descends (prefixWord ++ tailWord_86140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86165 : List Nat := [1, 3, 2, 1, 1, 1, 5, 2, 4]
def baseStart_86165 : Nat := 118140960795 + 86165 * 2 ^ 59
def prefixEnd_86165 : Nat := 4983230072969 + 3 ^ 40 * 86165 * 2
def baseEnd_86165 : Nat := 39328053862009433547769

theorem tailTrace_86165 : CollatzResearch.WordTrace tailWord_86165 prefixEnd_86165 39328053862009433547769 := by
  unfold tailWord_86165
  simp only [CollatzResearch.WordTrace]
  refine ⟨3142695732846395655523949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2095130488564263770349299 3142695732846395655523949)
  ·
    refine ⟨1178510899817398370821481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3142695732846395655523949 1178510899817398370821481)
    ·
      refine ⟨883883174863048778116111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1178510899817398370821481 883883174863048778116111)
      ·
        refine ⟨1325824762294573167174167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 883883174863048778116111 1325824762294573167174167)
        ·
          refine ⟨1988737143441859750761251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1325824762294573167174167 1988737143441859750761251)
          ·
            refine ⟨2983105715162789626141877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1988737143441859750761251 2983105715162789626141877)
            ·
              refine ⟨279666160796511527450801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2983105715162789626141877 279666160796511527450801)
              ·
                refine ⟨209749620597383645588101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 279666160796511527450801 209749620597383645588101)
                ·
                  refine ⟨39328053862009433547769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 209749620597383645588101 39328053862009433547769)
                  ·
                    rfl

theorem cell20_86165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 5, 2, 4].length) (baseStart_86165 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_86165 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_86165 prefixEnd_86165 := by exact prefixLift 86165
  have htrace : WordTrace (prefixWord ++ tailWord_86165) baseStart_86165 baseEnd_86165 := by
    simpa [prefixWord, tailWord_86165, baseEnd_86165] using wordTrace_append hprefix tailTrace_86165
  have hstable : (prefixWord ++ tailWord_86165).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86165).length < 2 ^ (prefixWord ++ tailWord_86165).sum := by decide
  have hdescent : baseEnd_86165 < baseStart_86165 := by decide
  rcases family_descends (prefixWord ++ tailWord_86165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86168 : List Nat := [2, 1, 2, 4, 3, 1, 3, 4]
def baseStart_86168 : Nat := 118140960795 + 86168 * 2 ^ 59
def prefixEnd_86168 : Nat := 4983230072969 + 3 ^ 40 * 86168 * 2
def baseEnd_86168 : Nat := 13109807714584918815919

theorem tailTrace_86168 : CollatzResearch.WordTrace tailWord_86168 prefixEnd_86168 13109807714584918815919 := by
  unfold tailWord_86168
  simp only [CollatzResearch.WordTrace]
  refine ⟨1571402575917763583941579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2095203434557018111922105 1571402575917763583941579)
  ·
    refine ⟨2357103863876645375912369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1571402575917763583941579 2357103863876645375912369)
    ·
      refine ⟨1767827897907484031934277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2357103863876645375912369 1767827897907484031934277)
      ·
        refine ⟨331467730857653255987677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1767827897907484031934277 331467730857653255987677)
        ·
          refine ⟨124300399071619970995379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 331467730857653255987677 124300399071619970995379)
          ·
            refine ⟨186450598607429956493069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124300399071619970995379 186450598607429956493069)
            ·
              refine ⟨69918974477786233684901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 186450598607429956493069 69918974477786233684901)
              ·
                refine ⟨13109807714584918815919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 69918974477786233684901 13109807714584918815919)
                ·
                  rfl

theorem cell20_86168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 3, 4].length) (baseStart_86168 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_86168 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_86168 prefixEnd_86168 := by exact prefixLift 86168
  have htrace : WordTrace (prefixWord ++ tailWord_86168) baseStart_86168 baseEnd_86168 := by
    simpa [prefixWord, tailWord_86168, baseEnd_86168] using wordTrace_append hprefix tailTrace_86168
  have hstable : (prefixWord ++ tailWord_86168).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86168).length < 2 ^ (prefixWord ++ tailWord_86168).sum := by decide
  have hdescent : baseEnd_86168 < baseStart_86168 := by decide
  rcases family_descends (prefixWord ++ tailWord_86168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86178 : List Nat := [3, 3, 1, 3, 1, 2, 2, 3, 2]
def baseStart_86178 : Nat := 118140960795 + 86178 * 2 ^ 59
def prefixEnd_86178 : Nat := 4983230072969 + 3 ^ 40 * 86178 * 2
def baseEnd_86178 : Nat := 39333987416239166114383

theorem tailTrace_86178 : CollatzResearch.WordTrace tailWord_86178 prefixEnd_86178 39333987416239166114383 := by
  unfold tailWord_86178
  simp only [CollatzResearch.WordTrace]
  refine ⟨785792470449824718936797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2095446587866199250498125 785792470449824718936797)
  ·
    refine ⟨294672176418684269601299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 785792470449824718936797 294672176418684269601299)
    ·
      refine ⟨442008264628026404401949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 294672176418684269601299 442008264628026404401949)
      ·
        refine ⟨165753099235509901650731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 442008264628026404401949 165753099235509901650731)
        ·
          refine ⟨248629648853264852476097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 165753099235509901650731 248629648853264852476097)
          ·
            refine ⟨186472236639948639357073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 248629648853264852476097 186472236639948639357073)
            ·
              refine ⟨139854177479961479517805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 186472236639948639357073 139854177479961479517805)
              ·
                refine ⟨52445316554985554819177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 139854177479961479517805 52445316554985554819177)
                ·
                  refine ⟨39333987416239166114383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52445316554985554819177 39333987416239166114383)
                  ·
                    rfl

theorem cell20_86178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 2, 3, 2].length) (baseStart_86178 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_86178 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_86178 prefixEnd_86178 := by exact prefixLift 86178
  have htrace : WordTrace (prefixWord ++ tailWord_86178) baseStart_86178 baseEnd_86178 := by
    simpa [prefixWord, tailWord_86178, baseEnd_86178] using wordTrace_append hprefix tailTrace_86178
  have hstable : (prefixWord ++ tailWord_86178).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86178).length < 2 ^ (prefixWord ++ tailWord_86178).sum := by decide
  have hdescent : baseEnd_86178 < baseStart_86178 := by decide
  rcases family_descends (prefixWord ++ tailWord_86178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86189 : List Nat := [1, 5, 2, 1, 2, 2, 7]
def baseStart_86189 : Nat := 118140960795 + 86189 * 2 ^ 59
def prefixEnd_86189 : Nat := 4983230072969 + 3 ^ 40 * 86189 * 2
def baseEnd_86189 : Nat := 4371000901774668527519

theorem tailTrace_86189 : CollatzResearch.WordTrace tailWord_86189 prefixEnd_86189 4371000901774668527519 := by
  unfold tailWord_86189
  simp only [CollatzResearch.WordTrace]
  refine ⟨3143571084759447754397621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2095714056506298502931747 3143571084759447754397621)
  ·
    refine ⟨294709789196198226974777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3143571084759447754397621 294709789196198226974777)
    ·
      refine ⟨221032341897148670231083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 294709789196198226974777 221032341897148670231083)
      ·
        refine ⟨331548512845723005346625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 221032341897148670231083 331548512845723005346625)
        ·
          refine ⟨248661384634292254009969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 331548512845723005346625 248661384634292254009969)
          ·
            refine ⟨186496038475719190507477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 248661384634292254009969 186496038475719190507477)
            ·
              refine ⟨4371000901774668527519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 186496038475719190507477 4371000901774668527519)
              ·
                rfl

theorem cell20_86189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 7].length) (baseStart_86189 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_86189 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_86189 prefixEnd_86189 := by exact prefixLift 86189
  have htrace : WordTrace (prefixWord ++ tailWord_86189) baseStart_86189 baseEnd_86189 := by
    simpa [prefixWord, tailWord_86189, baseEnd_86189] using wordTrace_append hprefix tailTrace_86189
  have hstable : (prefixWord ++ tailWord_86189).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86189).length < 2 ^ (prefixWord ++ tailWord_86189).sum := by decide
  have hdescent : baseEnd_86189 < baseStart_86189 := by decide
  rcases family_descends (prefixWord ++ tailWord_86189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86203 : List Nat := [1, 1, 1, 1, 1, 2, 8, 1, 4]
def baseStart_86203 : Nat := 118140960795 + 86203 * 2 ^ 59
def prefixEnd_86203 : Nat := 4983230072969 + 3 ^ 40 * 86203 * 2
def baseEnd_86203 : Nat := 39345398097450190280947

theorem tailTrace_86203 : CollatzResearch.WordTrace tailWord_86203 prefixEnd_86203 39345398097450190280947 := by
  unfold tailWord_86203
  simp only [CollatzResearch.WordTrace]
  refine ⟨3144081706708728145407263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2096054471139152096938175 3144081706708728145407263)
  ·
    refine ⟨4716122560063092218110895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3144081706708728145407263 4716122560063092218110895)
    ·
      refine ⟨7074183840094638327166343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4716122560063092218110895 7074183840094638327166343)
      ·
        refine ⟨10611275760141957490749515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7074183840094638327166343 10611275760141957490749515)
        ·
          refine ⟨15916913640212936236124273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10611275760141957490749515 15916913640212936236124273)
          ·
            refine ⟨11937685230159702177093205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15916913640212936236124273 11937685230159702177093205)
            ·
              refine ⟨139894748790934009887811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 11937685230159702177093205 139894748790934009887811)
              ·
                refine ⟨209842123186401014831717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 139894748790934009887811 209842123186401014831717)
                ·
                  refine ⟨39345398097450190280947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 209842123186401014831717 39345398097450190280947)
                  ·
                    rfl

theorem cell20_86203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 8, 1, 4].length) (baseStart_86203 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_86203 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_86203 prefixEnd_86203 := by exact prefixLift 86203
  have htrace : WordTrace (prefixWord ++ tailWord_86203) baseStart_86203 baseEnd_86203 := by
    simpa [prefixWord, tailWord_86203, baseEnd_86203] using wordTrace_append hprefix tailTrace_86203
  have hstable : (prefixWord ++ tailWord_86203).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86203).length < 2 ^ (prefixWord ++ tailWord_86203).sum := by decide
  have hdescent : baseEnd_86203 < baseStart_86203 := by decide
  rcases family_descends (prefixWord ++ tailWord_86203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86209 : List Nat := [1, 2, 6, 1, 2, 1, 3, 1, 3]
def baseStart_86209 : Nat := 118140960795 + 86209 * 2 ^ 59
def prefixEnd_86209 : Nat := 4983230072969 + 3 ^ 40 * 86209 * 2
def baseEnd_86209 : Nat := 39348136660940836080923

theorem tailTrace_86209 : CollatzResearch.WordTrace tailWord_86209 prefixEnd_86209 39348136660940836080923 := by
  unfold tailWord_86209
  simp only [CollatzResearch.WordTrace]
  refine ⟨3144300544686991170125681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2096200363124660780083787 3144300544686991170125681)
  ·
    refine ⟨2358225408515243377594261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3144300544686991170125681 2358225408515243377594261)
    ·
      refine ⟨110541816024152033324731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 2358225408515243377594261 110541816024152033324731)
      ·
        refine ⟨165812724036228049987097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110541816024152033324731 165812724036228049987097)
        ·
          refine ⟨124359543027171037490323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 165812724036228049987097 124359543027171037490323)
          ·
            refine ⟨186539314540756556235485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124359543027171037490323 186539314540756556235485)
            ·
              refine ⟨69952242952783708588307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 186539314540756556235485 69952242952783708588307)
              ·
                refine ⟨104928364429175562882461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69952242952783708588307 104928364429175562882461)
                ·
                  refine ⟨39348136660940836080923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 104928364429175562882461 39348136660940836080923)
                  ·
                    rfl

theorem cell20_86209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 3, 1, 3].length) (baseStart_86209 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_86209 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_86209 prefixEnd_86209 := by exact prefixLift 86209
  have htrace : WordTrace (prefixWord ++ tailWord_86209) baseStart_86209 baseEnd_86209 := by
    simpa [prefixWord, tailWord_86209, baseEnd_86209] using wordTrace_append hprefix tailTrace_86209
  have hstable : (prefixWord ++ tailWord_86209).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86209).length < 2 ^ (prefixWord ++ tailWord_86209).sum := by decide
  have hdescent : baseEnd_86209 < baseStart_86209 := by decide
  rcases family_descends (prefixWord ++ tailWord_86209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86248 : List Nat := [2, 1, 4, 1, 2, 2, 8]
def baseStart_86248 : Nat := 118140960795 + 86248 * 2 ^ 59
def prefixEnd_86248 : Nat := 4983230072969 + 3 ^ 40 * 86248 * 2
def baseEnd_86248 : Nat := 4373993035958892642307

theorem tailTrace_86248 : CollatzResearch.WordTrace tailWord_86248 prefixEnd_86248 4373993035958892642307 := by
  unfold tailWord_86248
  simp only [CollatzResearch.WordTrace]
  refine ⟨1572861495772850415397699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2097148661030467220530265 1572861495772850415397699)
  ·
    refine ⟨2359292243659275623096549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1572861495772850415397699 2359292243659275623096549)
    ·
      refine ⟨442367295686114179330603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2359292243659275623096549 442367295686114179330603)
      ·
        refine ⟨663550943529171268995905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 442367295686114179330603 663550943529171268995905)
        ·
          refine ⟨497663207646878451746929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 663550943529171268995905 497663207646878451746929)
          ·
            refine ⟨373247405735158838810197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 497663207646878451746929 373247405735158838810197)
            ·
              refine ⟨4373993035958892642307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 373247405735158838810197 4373993035958892642307)
              ·
                rfl

theorem cell20_86248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 8].length) (baseStart_86248 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_86248 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_86248 prefixEnd_86248 := by exact prefixLift 86248
  have htrace : WordTrace (prefixWord ++ tailWord_86248) baseStart_86248 baseEnd_86248 := by
    simpa [prefixWord, tailWord_86248, baseEnd_86248] using wordTrace_append hprefix tailTrace_86248
  have hstable : (prefixWord ++ tailWord_86248).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86248).length < 2 ^ (prefixWord ++ tailWord_86248).sum := by decide
  have hdescent : baseEnd_86248 < baseStart_86248 := by decide
  rcases family_descends (prefixWord ++ tailWord_86248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86258 : List Nat := [3, 2, 1, 3, 2, 1, 3, 1, 4]
def baseStart_86258 : Nat := 118140960795 + 86258 * 2 ^ 59
def prefixEnd_86258 : Nat := 4983230072969 + 3 ^ 40 * 86258 * 2
def baseEnd_86258 : Nat := 39370501596114443447389

theorem tailTrace_86258 : CollatzResearch.WordTrace tailWord_86258 prefixEnd_86258 39370501596114443447389 := by
  unfold tailWord_86258
  simp only [CollatzResearch.WordTrace]
  refine ⟨786521930377368134664857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2097391814339648359106285 786521930377368134664857)
  ·
    refine ⟨589891447783026100998643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 786521930377368134664857 589891447783026100998643)
    ·
      refine ⟨884837171674539151497965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 589891447783026100998643 884837171674539151497965)
      ·
        refine ⟨331813939377952181811737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 884837171674539151497965 331813939377952181811737)
        ·
          refine ⟨248860454533464136358803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 331813939377952181811737 248860454533464136358803)
          ·
            refine ⟨373290681800196204538205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 248860454533464136358803 373290681800196204538205)
            ·
              refine ⟨139984005675073576701827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 373290681800196204538205 139984005675073576701827)
              ·
                refine ⟨209976008512610365052741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 139984005675073576701827 209976008512610365052741)
                ·
                  refine ⟨39370501596114443447389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 209976008512610365052741 39370501596114443447389)
                  ·
                    rfl

theorem cell20_86258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 3, 1, 4].length) (baseStart_86258 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_86258 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_86258 prefixEnd_86258 := by exact prefixLift 86258
  have htrace : WordTrace (prefixWord ++ tailWord_86258) baseStart_86258 baseEnd_86258 := by
    simpa [prefixWord, tailWord_86258, baseEnd_86258] using wordTrace_append hprefix tailTrace_86258
  have hstable : (prefixWord ++ tailWord_86258).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86258).length < 2 ^ (prefixWord ++ tailWord_86258).sum := by decide
  have hdescent : baseEnd_86258 < baseStart_86258 := by decide
  rcases family_descends (prefixWord ++ tailWord_86258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86268 : List Nat := [2, 2, 2, 1, 4, 3, 2, 1, 3]
def baseStart_86268 : Nat := 118140960795 + 86268 * 2 ^ 59
def prefixEnd_86268 : Nat := 4983230072969 + 3 ^ 40 * 86268 * 2
def baseEnd_86268 : Nat := 39375065868598853114015

theorem tailTrace_86268 : CollatzResearch.WordTrace tailWord_86268 prefixEnd_86268 39375065868598853114015 := by
  unfold tailWord_86268
  simp only [CollatzResearch.WordTrace]
  refine ⟨1573226225736622123261729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2097634967648829497682305 1573226225736622123261729)
  ·
    refine ⟨1179919669302466592446297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1573226225736622123261729 1179919669302466592446297)
    ·
      refine ⟨884939751976849944334723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1179919669302466592446297 884939751976849944334723)
      ·
        refine ⟨1327409627965274916502085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 884939751976849944334723 1327409627965274916502085)
        ·
          refine ⟨248889305243489046844141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1327409627965274916502085 248889305243489046844141)
          ·
            refine ⟨93333489466308392566553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 248889305243489046844141 93333489466308392566553)
            ·
              refine ⟨70000117099731294424915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 93333489466308392566553 70000117099731294424915)
              ·
                refine ⟨105000175649596941637373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70000117099731294424915 105000175649596941637373)
                ·
                  refine ⟨39375065868598853114015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 105000175649596941637373 39375065868598853114015)
                  ·
                    rfl

theorem cell20_86268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 3, 2, 1, 3].length) (baseStart_86268 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_86268 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_86268 prefixEnd_86268 := by exact prefixLift 86268
  have htrace : WordTrace (prefixWord ++ tailWord_86268) baseStart_86268 baseEnd_86268 := by
    simpa [prefixWord, tailWord_86268, baseEnd_86268] using wordTrace_append hprefix tailTrace_86268
  have hstable : (prefixWord ++ tailWord_86268).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86268).length < 2 ^ (prefixWord ++ tailWord_86268).sum := by decide
  have hdescent : baseEnd_86268 < baseStart_86268 := by decide
  rcases family_descends (prefixWord ++ tailWord_86268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86286 : List Nat := [4, 1, 1, 2, 1, 2, 1, 8]
def baseStart_86286 : Nat := 118140960795 + 86286 * 2 ^ 59
def prefixEnd_86286 : Nat := 4983230072969 + 3 ^ 40 * 86286 * 2
def baseEnd_86286 : Nat := 13127760519690263504647

theorem tailTrace_86286 : CollatzResearch.WordTrace tailWord_86286 prefixEnd_86286 13127760519690263504647 := by
  unfold tailWord_86286
  simp only [CollatzResearch.WordTrace]
  refine ⟨393388620676004165084839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2098072643605355547119141 393388620676004165084839)
  ·
    refine ⟨590082931014006247627259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 393388620676004165084839 590082931014006247627259)
    ·
      refine ⟨885124396521009371440889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 590082931014006247627259 885124396521009371440889)
      ·
        refine ⟨663843297390757028580667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 885124396521009371440889 663843297390757028580667)
        ·
          refine ⟨995764946086135542871001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 663843297390757028580667 995764946086135542871001)
          ·
            refine ⟨746823709564601657153251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 995764946086135542871001 746823709564601657153251)
            ·
              refine ⟨1120235564346902485729877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 746823709564601657153251 1120235564346902485729877)
              ·
                refine ⟨13127760519690263504647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1120235564346902485729877 13127760519690263504647)
                ·
                  rfl

theorem cell20_86286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 8].length) (baseStart_86286 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_86286 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_86286 prefixEnd_86286 := by exact prefixLift 86286
  have htrace : WordTrace (prefixWord ++ tailWord_86286) baseStart_86286 baseEnd_86286 := by
    simpa [prefixWord, tailWord_86286, baseEnd_86286] using wordTrace_append hprefix tailTrace_86286
  have hstable : (prefixWord ++ tailWord_86286).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86286).length < 2 ^ (prefixWord ++ tailWord_86286).sum := by decide
  have hdescent : baseEnd_86286 < baseStart_86286 := by decide
  rcases family_descends (prefixWord ++ tailWord_86286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86293 : List Nat := [1, 3, 2, 1, 2, 1, 2, 1, 7]
def baseStart_86293 : Nat := 118140960795 + 86293 * 2 ^ 59
def prefixEnd_86293 : Nat := 4983230072969 + 3 ^ 40 * 86293 * 2
def baseEnd_86293 : Nat := 39386476549809877280579

theorem tailTrace_86293 : CollatzResearch.WordTrace tailWord_86293 prefixEnd_86293 39386476549809877280579 := by
  unfold tailWord_86293
  simp only [CollatzResearch.WordTrace]
  refine ⟨3147364276382673516183533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2098242850921782344122355 3147364276382673516183533)
  ·
    refine ⟨1180261603643502568568825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3147364276382673516183533 1180261603643502568568825)
    ·
      refine ⟨885196202732626926426619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1180261603643502568568825 885196202732626926426619)
      ·
        refine ⟨1327794304098940389639929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 885196202732626926426619 1327794304098940389639929)
        ·
          refine ⟨995845728074205292229947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1327794304098940389639929 995845728074205292229947)
          ·
            refine ⟨1493768592111307938344921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 995845728074205292229947 1493768592111307938344921)
            ·
              refine ⟨1120326444083480953758691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1493768592111307938344921 1120326444083480953758691)
              ·
                refine ⟨1680489666125221430638037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1120326444083480953758691 1680489666125221430638037)
                ·
                  refine ⟨39386476549809877280579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1680489666125221430638037 39386476549809877280579)
                  ·
                    rfl

theorem cell20_86293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 1, 7].length) (baseStart_86293 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_86293 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_86293 prefixEnd_86293 := by exact prefixLift 86293
  have htrace : WordTrace (prefixWord ++ tailWord_86293) baseStart_86293 baseEnd_86293 := by
    simpa [prefixWord, tailWord_86293, baseEnd_86293] using wordTrace_append hprefix tailTrace_86293
  have hstable : (prefixWord ++ tailWord_86293).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86293).length < 2 ^ (prefixWord ++ tailWord_86293).sum := by decide
  have hdescent : baseEnd_86293 < baseStart_86293 := by decide
  rcases family_descends (prefixWord ++ tailWord_86293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86296 : List Nat := [2, 1, 2, 3, 1, 2, 2, 5, 2]
def baseStart_86296 : Nat := 118140960795 + 86296 * 2 ^ 59
def prefixEnd_86296 : Nat := 4983230072969 + 3 ^ 40 * 86296 * 2
def baseEnd_86296 : Nat := 39387845831555200180567

theorem tailTrace_86296 : CollatzResearch.WordTrace tailWord_86296 prefixEnd_86296 39387845831555200180567 := by
  unfold tailWord_86296
  simp only [CollatzResearch.WordTrace]
  refine ⟨1573736847685902514271371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2098315796914536685695161 1573736847685902514271371)
  ·
    refine ⟨2360605271528853771407057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1573736847685902514271371 2360605271528853771407057)
    ·
      refine ⟨1770453953646640328555293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2360605271528853771407057 1770453953646640328555293)
      ·
        refine ⟨663920232617490123208235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1770453953646640328555293 663920232617490123208235)
        ·
          refine ⟨995880348926235184812353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 663920232617490123208235 995880348926235184812353)
          ·
            refine ⟨746910261694676388609265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 995880348926235184812353 746910261694676388609265)
            ·
              refine ⟨560182696271007291456949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 746910261694676388609265 560182696271007291456949)
              ·
                refine ⟨52517127775406933574089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 560182696271007291456949 52517127775406933574089)
                ·
                  refine ⟨39387845831555200180567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52517127775406933574089 39387845831555200180567)
                  ·
                    rfl

theorem cell20_86296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 5, 2].length) (baseStart_86296 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_86296 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_86296 prefixEnd_86296 := by exact prefixLift 86296
  have htrace : WordTrace (prefixWord ++ tailWord_86296) baseStart_86296 baseEnd_86296 := by
    simpa [prefixWord, tailWord_86296, baseEnd_86296] using wordTrace_append hprefix tailTrace_86296
  have hstable : (prefixWord ++ tailWord_86296).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86296).length < 2 ^ (prefixWord ++ tailWord_86296).sum := by decide
  have hdescent : baseEnd_86296 < baseStart_86296 := by decide
  rcases family_descends (prefixWord ++ tailWord_86296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86309 : List Nat := [1, 3, 1, 2, 6, 1, 2, 2, 2]
def baseStart_86309 : Nat := 118140960795 + 86309 * 2 ^ 59
def prefixEnd_86309 : Nat := 4983230072969 + 3 ^ 40 * 86309 * 2
def baseEnd_86309 : Nat := 39393779385784932747181

theorem tailTrace_86309 : CollatzResearch.WordTrace tailWord_86309 prefixEnd_86309 39393779385784932747181 := by
  unfold tailWord_86309
  simp only [CollatzResearch.WordTrace]
  refine ⟨3147947844324708248765981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2098631896216472165843987 3147947844324708248765981)
  ·
    refine ⟨1180480441621765593287243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3147947844324708248765981 1180480441621765593287243)
    ·
      refine ⟨1770720662432648389930865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1180480441621765593287243 1770720662432648389930865)
      ·
        refine ⟨1328040496824486292448149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1770720662432648389930865 1328040496824486292448149)
        ·
          refine ⟨62251898288647794958507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 1328040496824486292448149 62251898288647794958507)
          ·
            refine ⟨93377847432971692437761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62251898288647794958507 93377847432971692437761)
            ·
              refine ⟨70033385574728769328321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 93377847432971692437761 70033385574728769328321)
              ·
                refine ⟨52525039181046576996241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70033385574728769328321 52525039181046576996241)
                ·
                  refine ⟨39393779385784932747181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52525039181046576996241 39393779385784932747181)
                  ·
                    rfl

theorem cell20_86309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 1, 2, 2, 2].length) (baseStart_86309 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_86309 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_86309 prefixEnd_86309 := by exact prefixLift 86309
  have htrace : WordTrace (prefixWord ++ tailWord_86309) baseStart_86309 baseEnd_86309 := by
    simpa [prefixWord, tailWord_86309, baseEnd_86309] using wordTrace_append hprefix tailTrace_86309
  have hstable : (prefixWord ++ tailWord_86309).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86309).length < 2 ^ (prefixWord ++ tailWord_86309).sum := by decide
  have hdescent : baseEnd_86309 < baseStart_86309 := by decide
  rcases family_descends (prefixWord ++ tailWord_86309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86334 : List Nat := [4, 2, 1, 2, 1, 3, 1, 2, 4]
def baseStart_86334 : Nat := 118140960795 + 86334 * 2 ^ 59
def prefixEnd_86334 : Nat := 4983230072969 + 3 ^ 40 * 86334 * 2
def baseEnd_86334 : Nat := 39405190066995956913745

theorem tailTrace_86334 : CollatzResearch.WordTrace tailWord_86334 prefixEnd_86334 39405190066995956913745 := by
  unfold tailWord_86334
  simp only [CollatzResearch.WordTrace]
  refine ⟨393607458654267189803257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2099239779489425012284037 393607458654267189803257)
  ·
    refine ⟨295205593990700392352443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 393607458654267189803257 295205593990700392352443)
    ·
      refine ⟨442808390986050588528665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 295205593990700392352443 442808390986050588528665)
      ·
        refine ⟨332106293239537941396499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 442808390986050588528665 332106293239537941396499)
        ·
          refine ⟨498159439859306912094749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 332106293239537941396499 498159439859306912094749)
          ·
            refine ⟨186809789947240092035531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 498159439859306912094749 186809789947240092035531)
            ·
              refine ⟨280214684920860138053297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 186809789947240092035531 280214684920860138053297)
              ·
                refine ⟨210161013690645103539973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 280214684920860138053297 210161013690645103539973)
                ·
                  refine ⟨39405190066995956913745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 210161013690645103539973 39405190066995956913745)
                  ·
                    rfl

theorem cell20_86334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 1, 2, 4].length) (baseStart_86334 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_86334 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_86334 prefixEnd_86334 := by exact prefixLift 86334
  have htrace : WordTrace (prefixWord ++ tailWord_86334) baseStart_86334 baseEnd_86334 := by
    simpa [prefixWord, tailWord_86334, baseEnd_86334] using wordTrace_append hprefix tailTrace_86334
  have hstable : (prefixWord ++ tailWord_86334).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86334).length < 2 ^ (prefixWord ++ tailWord_86334).sum := by decide
  have hdescent : baseEnd_86334 < baseStart_86334 := by decide
  rcases family_descends (prefixWord ++ tailWord_86334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86372 : List Nat := [2, 3, 1, 1, 3, 1, 1, 6, 2]
def baseStart_86372 : Nat := 118140960795 + 86372 * 2 ^ 59
def prefixEnd_86372 : Nat := 4983230072969 + 3 ^ 40 * 86372 * 2
def baseEnd_86372 : Nat := 39422534302436713646923

theorem tailTrace_86372 : CollatzResearch.WordTrace tailWord_86372 prefixEnd_86372 39422534302436713646923 := by
  unfold tailWord_86372
  simp only [CollatzResearch.WordTrace]
  refine ⟨1575122821548235004154685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2100163762064313338872913 1575122821548235004154685)
  ·
    refine ⟨590671058080588126558007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1575122821548235004154685 590671058080588126558007)
    ·
      refine ⟨886006587120882189837011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 590671058080588126558007 886006587120882189837011)
      ·
        refine ⟨1329009880681323284755517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 886006587120882189837011 1329009880681323284755517)
        ·
          refine ⟨498378705255496231783319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1329009880681323284755517 498378705255496231783319)
          ·
            refine ⟨747568057883244347674979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 498378705255496231783319 747568057883244347674979)
            ·
              refine ⟨1121352086824866521512469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 747568057883244347674979 1121352086824866521512469)
              ·
                refine ⟨52563379069915618195897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1121352086824866521512469 52563379069915618195897)
                ·
                  refine ⟨39422534302436713646923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52563379069915618195897 39422534302436713646923)
                  ·
                    rfl

theorem cell20_86372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 6, 2].length) (baseStart_86372 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_86372 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_86372 prefixEnd_86372 := by exact prefixLift 86372
  have htrace : WordTrace (prefixWord ++ tailWord_86372) baseStart_86372 baseEnd_86372 := by
    simpa [prefixWord, tailWord_86372, baseEnd_86372] using wordTrace_append hprefix tailTrace_86372
  have hstable : (prefixWord ++ tailWord_86372).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86372).length < 2 ^ (prefixWord ++ tailWord_86372).sum := by decide
  have hdescent : baseEnd_86372 < baseStart_86372 := by decide
  rcases family_descends (prefixWord ++ tailWord_86372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86402 : List Nat := [3, 4, 2, 1, 3, 1, 1, 3, 2]
def baseStart_86402 : Nat := 118140960795 + 86402 * 2 ^ 59
def prefixEnd_86402 : Nat := 4983230072969 + 3 ^ 40 * 86402 * 2
def baseEnd_86402 : Nat := 39436227119889942646801

theorem tailTrace_86402 : CollatzResearch.WordTrace tailWord_86402 prefixEnd_86402 39436227119889942646801 := by
  unfold tailWord_86402
  simp only [CollatzResearch.WordTrace]
  refine ⟨787834958246946282975365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2100893221991856754600973 787834958246946282975365)
  ·
    refine ⟨147719054671302428057881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 787834958246946282975365 147719054671302428057881)
    ·
      refine ⟨110789291003476821043411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147719054671302428057881 110789291003476821043411)
      ·
        refine ⟨166183936505215231565117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110789291003476821043411 166183936505215231565117)
        ·
          refine ⟨62318976189455711836919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 166183936505215231565117 62318976189455711836919)
          ·
            refine ⟨93478464284183567755379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62318976189455711836919 93478464284183567755379)
            ·
              refine ⟨140217696426275351633069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93478464284183567755379 140217696426275351633069)
              ·
                refine ⟨52581636159853256862401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 140217696426275351633069 52581636159853256862401)
                ·
                  refine ⟨39436227119889942646801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52581636159853256862401 39436227119889942646801)
                  ·
                    rfl

theorem cell20_86402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 1, 1, 3, 2].length) (baseStart_86402 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_86402 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_86402 prefixEnd_86402 := by exact prefixLift 86402
  have htrace : WordTrace (prefixWord ++ tailWord_86402) baseStart_86402 baseEnd_86402 := by
    simpa [prefixWord, tailWord_86402, baseEnd_86402] using wordTrace_append hprefix tailTrace_86402
  have hstable : (prefixWord ++ tailWord_86402).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86402).length < 2 ^ (prefixWord ++ tailWord_86402).sum := by decide
  have hdescent : baseEnd_86402 < baseStart_86402 := by decide
  rcases family_descends (prefixWord ++ tailWord_86402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86407 : List Nat := [1, 1, 4, 2, 2, 1, 1, 1, 7]
def baseStart_86407 : Nat := 118140960795 + 86407 * 2 ^ 59
def prefixEnd_86407 : Nat := 4983230072969 + 3 ^ 40 * 86407 * 2
def baseEnd_86407 : Nat := 39438509256132147480113

theorem tailTrace_86407 : CollatzResearch.WordTrace tailWord_86407 prefixEnd_86407 39438509256132147480113 := by
  unfold tailWord_86407
  simp only [CollatzResearch.WordTrace]
  refine ⟨3151522197969670985833475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2101014798646447323888983 3151522197969670985833475)
  ·
    refine ⟨4727283296954506478750213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3151522197969670985833475 4727283296954506478750213)
    ·
      refine ⟨886365618178969964765665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4727283296954506478750213 886365618178969964765665)
      ·
        refine ⟨664774213634227473574249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 886365618178969964765665 664774213634227473574249)
        ·
          refine ⟨498580660225670605180687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 664774213634227473574249 498580660225670605180687)
          ·
            refine ⟨747870990338505907771031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 498580660225670605180687 747870990338505907771031)
            ·
              refine ⟨1121806485507758861656547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 747870990338505907771031 1121806485507758861656547)
              ·
                refine ⟨1682709728261638292484821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1121806485507758861656547 1682709728261638292484821)
                ·
                  refine ⟨39438509256132147480113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1682709728261638292484821 39438509256132147480113)
                  ·
                    rfl

theorem cell20_86407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 1, 7].length) (baseStart_86407 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_86407 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_86407 prefixEnd_86407 := by exact prefixLift 86407
  have htrace : WordTrace (prefixWord ++ tailWord_86407) baseStart_86407 baseEnd_86407 := by
    simpa [prefixWord, tailWord_86407, baseEnd_86407] using wordTrace_append hprefix tailTrace_86407
  have hstable : (prefixWord ++ tailWord_86407).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86407).length < 2 ^ (prefixWord ++ tailWord_86407).sum := by decide
  have hdescent : baseEnd_86407 < baseStart_86407 := by decide
  rcases family_descends (prefixWord ++ tailWord_86407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86424 : List Nat := [2, 1, 2, 5, 1, 1, 2, 1, 5]
def baseStart_86424 : Nat := 118140960795 + 86424 * 2 ^ 59
def prefixEnd_86424 : Nat := 4983230072969 + 3 ^ 40 * 86424 * 2
def baseEnd_86424 : Nat := 39446268519355643913377

theorem tailTrace_86424 : CollatzResearch.WordTrace tailWord_86424 prefixEnd_86424 39446268519355643913377 := by
  unfold tailWord_86424
  simp only [CollatzResearch.WordTrace]
  refine ⟨1576071119454041444601163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2101428159272055259468217 1576071119454041444601163)
  ·
    refine ⟨2364106679181062166901745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1576071119454041444601163 2364106679181062166901745)
    ·
      refine ⟨1773080009385796625176309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2364106679181062166901745 1773080009385796625176309)
      ·
        refine ⟨166226250879918433610279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1773080009385796625176309 166226250879918433610279)
        ·
          refine ⟨249339376319877650415419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 166226250879918433610279 249339376319877650415419)
          ·
            refine ⟨374009064479816475623129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 249339376319877650415419 374009064479816475623129)
            ·
              refine ⟨280506798359862356717347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 374009064479816475623129 280506798359862356717347)
              ·
                refine ⟨420760197539793535076021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 280506798359862356717347 420760197539793535076021)
                ·
                  refine ⟨39446268519355643913377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 420760197539793535076021 39446268519355643913377)
                  ·
                    rfl

theorem cell20_86424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 2, 1, 5].length) (baseStart_86424 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_86424 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_86424 prefixEnd_86424 := by exact prefixLift 86424
  have htrace : WordTrace (prefixWord ++ tailWord_86424) baseStart_86424 baseEnd_86424 := by
    simpa [prefixWord, tailWord_86424, baseEnd_86424] using wordTrace_append hprefix tailTrace_86424
  have hstable : (prefixWord ++ tailWord_86424).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86424).length < 2 ^ (prefixWord ++ tailWord_86424).sum := by decide
  have hdescent : baseEnd_86424 < baseStart_86424 := by decide
  rcases family_descends (prefixWord ++ tailWord_86424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86476 : List Nat := [2, 2, 1, 4, 3, 8]
def baseStart_86476 : Nat := 118140960795 + 86476 * 2 ^ 59
def prefixEnd_86476 : Nat := 4983230072969 + 3 ^ 40 * 86476 * 2
def baseEnd_86476 : Nat := 1461851953195354599253

theorem tailTrace_86476 : CollatzResearch.WordTrace tailWord_86476 prefixEnd_86476 1461851953195354599253 := by
  unfold tailWord_86476
  simp only [CollatzResearch.WordTrace]
  refine ⟨1577019417359847885047641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2102692556479797180063521 1577019417359847885047641)
  ·
    refine ⟨1182764563019885913785731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1577019417359847885047641 1182764563019885913785731)
    ·
      refine ⟨1774146844529828870678597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1182764563019885913785731 1774146844529828870678597)
      ·
        refine ⟨332652533349342913252237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1774146844529828870678597 332652533349342913252237)
        ·
          refine ⟨124744700006003592469589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 332652533349342913252237 124744700006003592469589)
          ·
            refine ⟨1461851953195354599253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 124744700006003592469589 1461851953195354599253)
            ·
              rfl

theorem cell20_86476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 8].length) (baseStart_86476 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_86476 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_86476 prefixEnd_86476 := by exact prefixLift 86476
  have htrace : WordTrace (prefixWord ++ tailWord_86476) baseStart_86476 baseEnd_86476 := by
    simpa [prefixWord, tailWord_86476, baseEnd_86476] using wordTrace_append hprefix tailTrace_86476
  have hstable : (prefixWord ++ tailWord_86476).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86476).length < 2 ^ (prefixWord ++ tailWord_86476).sum := by decide
  have hdescent : baseEnd_86476 < baseStart_86476 := by decide
  rcases family_descends (prefixWord ++ tailWord_86476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86482 : List Nat := [3, 2, 2, 4, 1, 1, 1, 4, 2]
def baseStart_86482 : Nat := 118140960795 + 86482 * 2 ^ 59
def prefixEnd_86482 : Nat := 4983230072969 + 3 ^ 40 * 86482 * 2
def baseEnd_86482 : Nat := 39472741299765219979807

theorem tailTrace_86482 : CollatzResearch.WordTrace tailWord_86482 prefixEnd_86482 39472741299765219979807 := by
  unfold tailWord_86482
  simp only [CollatzResearch.WordTrace]
  refine ⟨788564418174489698703425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2102838448465305863209133 788564418174489698703425)
  ·
    refine ⟨591423313630867274027569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 788564418174489698703425 591423313630867274027569)
    ·
      refine ⟨443567485223150455520677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 591423313630867274027569 443567485223150455520677)
      ·
        refine ⟨83168903479340710410127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 443567485223150455520677 83168903479340710410127)
        ·
          refine ⟨124753355219011065615191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83168903479340710410127 124753355219011065615191)
          ·
            refine ⟨187130032828516598422787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124753355219011065615191 187130032828516598422787)
            ·
              refine ⟨280695049242774897634181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 187130032828516598422787 280695049242774897634181)
              ·
                refine ⟨52630321733020293306409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 280695049242774897634181 52630321733020293306409)
                ·
                  refine ⟨39472741299765219979807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52630321733020293306409 39472741299765219979807)
                  ·
                    rfl

theorem cell20_86482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 1, 4, 2].length) (baseStart_86482 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_86482 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_86482 prefixEnd_86482 := by exact prefixLift 86482
  have htrace : WordTrace (prefixWord ++ tailWord_86482) baseStart_86482 baseEnd_86482 := by
    simpa [prefixWord, tailWord_86482, baseEnd_86482] using wordTrace_append hprefix tailTrace_86482
  have hstable : (prefixWord ++ tailWord_86482).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86482).length < 2 ^ (prefixWord ++ tailWord_86482).sum := by decide
  have hdescent : baseEnd_86482 < baseStart_86482 := by decide
  rcases family_descends (prefixWord ++ tailWord_86482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86486 : List Nat := [5, 2, 1, 1, 1, 1, 2, 3, 4]
def baseStart_86486 : Nat := 118140960795 + 86486 * 2 ^ 59
def prefixEnd_86486 : Nat := 4983230072969 + 3 ^ 40 * 86486 * 2
def baseEnd_86486 : Nat := 39474567008758983846457

theorem tailTrace_86486 : CollatzResearch.WordTrace tailWord_86486 prefixEnd_86486 39474567008758983846457 := by
  unfold tailWord_86486
  simp only [CollatzResearch.WordTrace]
  refine ⟨197150222792716717372457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2102935709788978318639541 197150222792716717372457)
  ·
    refine ⟨147862667094537538029343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 197150222792716717372457 147862667094537538029343)
    ·
      refine ⟨221794000641806307044015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147862667094537538029343 221794000641806307044015)
      ·
        refine ⟨332691000962709460566023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 221794000641806307044015 332691000962709460566023)
        ·
          refine ⟨499036501444064190849035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 332691000962709460566023 499036501444064190849035)
          ·
            refine ⟨748554752166096286273553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 499036501444064190849035 748554752166096286273553)
            ·
              refine ⟨561416064124572214705165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 748554752166096286273553 561416064124572214705165)
              ·
                refine ⟨210531024046714580514437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 561416064124572214705165 210531024046714580514437)
                ·
                  refine ⟨39474567008758983846457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 210531024046714580514437 39474567008758983846457)
                  ·
                    rfl

theorem cell20_86486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 3, 4].length) (baseStart_86486 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_86486 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_86486 prefixEnd_86486 := by exact prefixLift 86486
  have htrace : WordTrace (prefixWord ++ tailWord_86486) baseStart_86486 baseEnd_86486 := by
    simpa [prefixWord, tailWord_86486, baseEnd_86486] using wordTrace_append hprefix tailTrace_86486
  have hstable : (prefixWord ++ tailWord_86486).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86486).length < 2 ^ (prefixWord ++ tailWord_86486).sum := by decide
  have hdescent : baseEnd_86486 < baseStart_86486 := by decide
  rcases family_descends (prefixWord ++ tailWord_86486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86541 : List Nat := [1, 7, 1, 1, 1, 1, 1, 3, 4]
def baseStart_86541 : Nat := 118140960795 + 86541 * 2 ^ 59
def prefixEnd_86541 : Nat := 4983230072969 + 3 ^ 40 * 86541 * 2
def baseEnd_86541 : Nat := 39499670507423237012899

theorem tailTrace_86541 : CollatzResearch.WordTrace tailWord_86541 prefixEnd_86541 39499670507423237012899 := by
  unfold tailWord_86541
  simp only [CollatzResearch.WordTrace]
  refine ⟨3156409579484211871211477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2104273052989474580807651 3156409579484211871211477)
  ·
    refine ⟨73978349519161215731519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 3156409579484211871211477 73978349519161215731519)
    ·
      refine ⟨110967524278741823597279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73978349519161215731519 110967524278741823597279)
      ·
        refine ⟨166451286418112735395919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110967524278741823597279 166451286418112735395919)
        ·
          refine ⟨249676929627169103093879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 166451286418112735395919 249676929627169103093879)
          ·
            refine ⟨374515394440753654640819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 249676929627169103093879 374515394440753654640819)
            ·
              refine ⟨561773091661130481961229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 374515394440753654640819 561773091661130481961229)
              ·
                refine ⟨210664909372923930735461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 561773091661130481961229 210664909372923930735461)
                ·
                  refine ⟨39499670507423237012899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 210664909372923930735461 39499670507423237012899)
                  ·
                    rfl

theorem cell20_86541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 3, 4].length) (baseStart_86541 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_86541 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_86541 prefixEnd_86541 := by exact prefixLift 86541
  have htrace : WordTrace (prefixWord ++ tailWord_86541) baseStart_86541 baseEnd_86541 := by
    simpa [prefixWord, tailWord_86541, baseEnd_86541] using wordTrace_append hprefix tailTrace_86541
  have hstable : (prefixWord ++ tailWord_86541).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86541).length < 2 ^ (prefixWord ++ tailWord_86541).sum := by decide
  have hdescent : baseEnd_86541 < baseStart_86541 := by decide
  rcases family_descends (prefixWord ++ tailWord_86541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86597 : List Nat := [1, 3, 1, 1, 1, 5, 2, 1, 5]
def baseStart_86597 : Nat := 118140960795 + 86597 * 2 ^ 59
def prefixEnd_86597 : Nat := 4983230072969 + 3 ^ 40 * 86597 * 2
def baseEnd_86597 : Nat := 39525230433335931146003

theorem tailTrace_86597 : CollatzResearch.WordTrace tailWord_86597 prefixEnd_86597 39525230433335931146003 := by
  unfold tailWord_86597
  simp only [CollatzResearch.WordTrace]
  refine ⟨3158452067281333435250045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2105634711520888956833363 3158452067281333435250045)
  ·
    refine ⟨1184419525230500038218767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3158452067281333435250045 1184419525230500038218767)
    ·
      refine ⟨1776629287845750057328151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1184419525230500038218767 1776629287845750057328151)
      ·
        refine ⟨2664943931768625085992227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1776629287845750057328151 2664943931768625085992227)
        ·
          refine ⟨3997415897652937628988341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2664943931768625085992227 3997415897652937628988341)
          ·
            refine ⟨374757740404962902717657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3997415897652937628988341 374757740404962902717657)
            ·
              refine ⟨281068305303722177038243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 374757740404962902717657 281068305303722177038243)
              ·
                refine ⟨421602457955583265557365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 281068305303722177038243 421602457955583265557365)
                ·
                  refine ⟨39525230433335931146003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 421602457955583265557365 39525230433335931146003)
                  ·
                    rfl

theorem cell20_86597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 2, 1, 5].length) (baseStart_86597 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_86597 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_86597 prefixEnd_86597 := by exact prefixLift 86597
  have htrace : WordTrace (prefixWord ++ tailWord_86597) baseStart_86597 baseEnd_86597 := by
    simpa [prefixWord, tailWord_86597, baseEnd_86597] using wordTrace_append hprefix tailTrace_86597
  have hstable : (prefixWord ++ tailWord_86597).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86597).length < 2 ^ (prefixWord ++ tailWord_86597).sum := by decide
  have hdescent : baseEnd_86597 < baseStart_86597 := by decide
  rcases family_descends (prefixWord ++ tailWord_86597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86645 : List Nat := [1, 3, 4, 2, 3, 7]
def baseStart_86645 : Nat := 118140960795 + 86645 * 2 ^ 59
def prefixEnd_86645 : Nat := 4983230072969 + 3 ^ 40 * 86645 * 2
def baseEnd_86645 : Nat := 1464708849676336946141

theorem tailTrace_86645 : CollatzResearch.WordTrace tailWord_86645 prefixEnd_86645 1464708849676336946141 := by
  unfold tailWord_86645
  simp only [CollatzResearch.WordTrace]
  refine ⟨3160202771107437632997389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2106801847404958421998259 3160202771107437632997389)
  ·
    refine ⟨1185076039165289112374021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3160202771107437632997389 1185076039165289112374021)
    ·
      refine ⟨222201757343491708570129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1185076039165289112374021 222201757343491708570129)
      ·
        refine ⟨166651318007618781427597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 222201757343491708570129 166651318007618781427597)
        ·
          refine ⟨62494244252857043035349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 166651318007618781427597 62494244252857043035349)
          ·
            refine ⟨1464708849676336946141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 62494244252857043035349 1464708849676336946141)
            ·
              rfl

theorem cell20_86645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 7].length) (baseStart_86645 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_86645 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_86645 prefixEnd_86645 := by exact prefixLift 86645
  have htrace : WordTrace (prefixWord ++ tailWord_86645) baseStart_86645 baseEnd_86645 := by
    simpa [prefixWord, tailWord_86645, baseEnd_86645] using wordTrace_append hprefix tailTrace_86645
  have hstable : (prefixWord ++ tailWord_86645).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86645).length < 2 ^ (prefixWord ++ tailWord_86645).sum := by decide
  have hdescent : baseEnd_86645 < baseStart_86645 := by decide
  rcases family_descends (prefixWord ++ tailWord_86645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86649 : List Nat := [1, 2, 1, 3, 3, 10]
def baseStart_86649 : Nat := 118140960795 + 86649 * 2 ^ 59
def prefixEnd_86649 : Nat := 4983230072969 + 3 ^ 40 * 86649 * 2
def baseEnd_86649 : Nat := 1464776468527957830091

theorem tailTrace_86649 : CollatzResearch.WordTrace tailWord_86649 prefixEnd_86649 1464776468527957830091 := by
  unfold tailWord_86649
  simp only [CollatzResearch.WordTrace]
  refine ⟨3160348663092946316143001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2106899108728630877428667 3160348663092946316143001)
  ·
    refine ⟨2370261497319709737107251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3160348663092946316143001 2370261497319709737107251)
    ·
      refine ⟨3555392245979564605660877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2370261497319709737107251 3555392245979564605660877)
      ·
        refine ⟨1333272092242336727122829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3555392245979564605660877 1333272092242336727122829)
        ·
          refine ⟨499977034590876272671061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1333272092242336727122829 499977034590876272671061)
          ·
            refine ⟨1464776468527957830091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 499977034590876272671061 1464776468527957830091)
            ·
              rfl

theorem cell20_86649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 10].length) (baseStart_86649 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_86649 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_86649 prefixEnd_86649 := by exact prefixLift 86649
  have htrace : WordTrace (prefixWord ++ tailWord_86649) baseStart_86649 baseEnd_86649 := by
    simpa [prefixWord, tailWord_86649, baseEnd_86649] using wordTrace_append hprefix tailTrace_86649
  have hstable : (prefixWord ++ tailWord_86649).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86649).length < 2 ^ (prefixWord ++ tailWord_86649).sum := by decide
  have hdescent : baseEnd_86649 < baseStart_86649 := by decide
  rcases family_descends (prefixWord ++ tailWord_86649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86658 : List Nat := [3, 4, 3, 1, 1, 2, 1, 5]
def baseStart_86658 : Nat := 118140960795 + 86658 * 2 ^ 59
def prefixEnd_86658 : Nat := 4983230072969 + 3 ^ 40 * 86658 * 2
def baseEnd_86658 : Nat := 13184357498496943370807

theorem tailTrace_86658 : CollatzResearch.WordTrace tailWord_86658 prefixEnd_86658 13184357498496943370807 := by
  unfold tailWord_86658
  simp only [CollatzResearch.WordTrace]
  refine ⟨790169230015085213305157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2107117946706893902147085 790169230015085213305157)
  ·
    refine ⟨148156730627828477494717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 790169230015085213305157 148156730627828477494717)
    ·
      refine ⟨55558773985435679060519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 148156730627828477494717 55558773985435679060519)
      ·
        refine ⟨83338160978153518590779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55558773985435679060519 83338160978153518590779)
        ·
          refine ⟨125007241467230277886169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83338160978153518590779 125007241467230277886169)
          ·
            refine ⟨93755431100422708414627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 125007241467230277886169 93755431100422708414627)
            ·
              refine ⟨140633146650634062621941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93755431100422708414627 140633146650634062621941)
              ·
                refine ⟨13184357498496943370807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 140633146650634062621941 13184357498496943370807)
                ·
                  rfl

theorem cell20_86658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 2, 1, 5].length) (baseStart_86658 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_86658 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_86658 prefixEnd_86658 := by exact prefixLift 86658
  have htrace : WordTrace (prefixWord ++ tailWord_86658) baseStart_86658 baseEnd_86658 := by
    simpa [prefixWord, tailWord_86658, baseEnd_86658] using wordTrace_append hprefix tailTrace_86658
  have hstable : (prefixWord ++ tailWord_86658).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86658).length < 2 ^ (prefixWord ++ tailWord_86658).sum := by decide
  have hdescent : baseEnd_86658 < baseStart_86658 := by decide
  rcases family_descends (prefixWord ++ tailWord_86658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86676 : List Nat := [2, 4, 2, 2, 1, 2, 1, 2, 4]
def baseStart_86676 : Nat := 118140960795 + 86676 * 2 ^ 59
def prefixEnd_86676 : Nat := 4983230072969 + 3 ^ 40 * 86676 * 2
def baseEnd_86676 : Nat := 39561288185962767512347

theorem tailTrace_86676 : CollatzResearch.WordTrace tailWord_86676 prefixEnd_86676 39561288185962767512347 := by
  unfold tailWord_86676
  simp only [CollatzResearch.WordTrace]
  refine ⟨1580666716997564963687941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2107555622663419951583921 1580666716997564963687941)
  ·
    refine ⟨296375009437043430691489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1580666716997564963687941 296375009437043430691489)
    ·
      refine ⟨222281257077782573018617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 296375009437043430691489 222281257077782573018617)
      ·
        refine ⟨166710942808336929763963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 222281257077782573018617 166710942808336929763963)
        ·
          refine ⟨250066414212505394645945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 166710942808336929763963 250066414212505394645945)
          ·
            refine ⟨187549810659379045984459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 250066414212505394645945 187549810659379045984459)
            ·
              refine ⟨281324715989068568976689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 187549810659379045984459 281324715989068568976689)
              ·
                refine ⟨210993536991801426732517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 281324715989068568976689 210993536991801426732517)
                ·
                  refine ⟨39561288185962767512347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 210993536991801426732517 39561288185962767512347)
                  ·
                    rfl

theorem cell20_86676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 1, 2, 4].length) (baseStart_86676 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_86676 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_86676 prefixEnd_86676 := by exact prefixLift 86676
  have htrace : WordTrace (prefixWord ++ tailWord_86676) baseStart_86676 baseEnd_86676 := by
    simpa [prefixWord, tailWord_86676, baseEnd_86676] using wordTrace_append hprefix tailTrace_86676
  have hstable : (prefixWord ++ tailWord_86676).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86676).length < 2 ^ (prefixWord ++ tailWord_86676).sum := by decide
  have hdescent : baseEnd_86676 < baseStart_86676 := by decide
  rcases family_descends (prefixWord ++ tailWord_86676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86697 : List Nat := [1, 2, 1, 1, 1, 1, 2, 9, 2]
def baseStart_86697 : Nat := 118140960795 + 86697 * 2 ^ 59
def prefixEnd_86697 : Nat := 4983230072969 + 3 ^ 40 * 86697 * 2
def baseEnd_86697 : Nat := 39570873158180027812261

theorem tailTrace_86697 : CollatzResearch.WordTrace tailWord_86697 prefixEnd_86697 39570873158180027812261 := by
  unfold tailWord_86697
  simp only [CollatzResearch.WordTrace]
  refine ⟨3162099366919050513890345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2108066244612700342593563 3162099366919050513890345)
  ·
    refine ⟨2371574525189287885417759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3162099366919050513890345 2371574525189287885417759)
    ·
      refine ⟨3557361787783931828126639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2371574525189287885417759 3557361787783931828126639)
      ·
        refine ⟨5336042681675897742189959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3557361787783931828126639 5336042681675897742189959)
        ·
          refine ⟨8004064022513846613284939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5336042681675897742189959 8004064022513846613284939)
          ·
            refine ⟨12006096033770769919927409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8004064022513846613284939 12006096033770769919927409)
            ·
              refine ⟨9004572025328077439945557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12006096033770769919927409 9004572025328077439945557)
              ·
                refine ⟨52761164210906703749681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 9004572025328077439945557 52761164210906703749681)
                ·
                  refine ⟨39570873158180027812261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52761164210906703749681 39570873158180027812261)
                  ·
                    rfl

theorem cell20_86697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 9, 2].length) (baseStart_86697 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_86697 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_86697 prefixEnd_86697 := by exact prefixLift 86697
  have htrace : WordTrace (prefixWord ++ tailWord_86697) baseStart_86697 baseEnd_86697 := by
    simpa [prefixWord, tailWord_86697, baseEnd_86697] using wordTrace_append hprefix tailTrace_86697
  have hstable : (prefixWord ++ tailWord_86697).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86697).length < 2 ^ (prefixWord ++ tailWord_86697).sum := by decide
  have hdescent : baseEnd_86697 < baseStart_86697 := by decide
  rcases family_descends (prefixWord ++ tailWord_86697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86738 : List Nat := [3, 2, 2, 2, 3, 2, 2, 4]
def baseStart_86738 : Nat := 118140960795 + 86738 * 2 ^ 59
def prefixEnd_86738 : Nat := 4983230072969 + 3 ^ 40 * 86738 * 2
def baseEnd_86738 : Nat := 13196528891788702481809

theorem tailTrace_86738 : CollatzResearch.WordTrace tailWord_86738 prefixEnd_86738 13196528891788702481809 := by
  unfold tailWord_86738
  simp only [CollatzResearch.WordTrace]
  refine ⟨790898689942628629033217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2109063173180343010755245 790898689942628629033217)
  ·
    refine ⟨593174017456971471774913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 790898689942628629033217 593174017456971471774913)
    ·
      refine ⟨444880513092728603831185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 593174017456971471774913 444880513092728603831185)
      ·
        refine ⟨333660384819546452873389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 444880513092728603831185 333660384819546452873389)
        ·
          refine ⟨125122644307329919827521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 333660384819546452873389 125122644307329919827521)
          ·
            refine ⟨93841983230497439870641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 125122644307329919827521 93841983230497439870641)
            ·
              refine ⟨70381487422873079902981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 93841983230497439870641 70381487422873079902981)
              ·
                refine ⟨13196528891788702481809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 70381487422873079902981 13196528891788702481809)
                ·
                  rfl

theorem cell20_86738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 2, 2, 4].length) (baseStart_86738 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_86738 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_86738 prefixEnd_86738 := by exact prefixLift 86738
  have htrace : WordTrace (prefixWord ++ tailWord_86738) baseStart_86738 baseEnd_86738 := by
    simpa [prefixWord, tailWord_86738, baseEnd_86738] using wordTrace_append hprefix tailTrace_86738
  have hstable : (prefixWord ++ tailWord_86738).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86738).length < 2 ^ (prefixWord ++ tailWord_86738).sum := by decide
  have hdescent : baseEnd_86738 < baseStart_86738 := by decide
  rcases family_descends (prefixWord ++ tailWord_86738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86748 : List Nat := [2, 2, 5, 1, 1, 3, 1, 3, 2]
def baseStart_86748 : Nat := 118140960795 + 86748 * 2 ^ 59
def prefixEnd_86748 : Nat := 4983230072969 + 3 ^ 40 * 86748 * 2
def baseEnd_86748 : Nat := 39594150947850517112053

theorem tailTrace_86748 : CollatzResearch.WordTrace tailWord_86748 prefixEnd_86748 39594150947850517112053 := by
  unfold tailWord_86748
  simp only [CollatzResearch.WordTrace]
  refine ⟨1581979744867143111998449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2109306326489524149331265 1581979744867143111998449)
  ·
    refine ⟨1186484808650357333998837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1581979744867143111998449 1186484808650357333998837)
    ·
      refine ⟨111232950810971000062391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1186484808650357333998837 111232950810971000062391)
      ·
        refine ⟨166849426216456500093587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111232950810971000062391 166849426216456500093587)
        ·
          refine ⟨250274139324684750140381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 166849426216456500093587 250274139324684750140381)
          ·
            refine ⟨93852802246756781302643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 250274139324684750140381 93852802246756781302643)
            ·
              refine ⟨140779203370135171953965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93852802246756781302643 140779203370135171953965)
              ·
                refine ⟨52792201263800689482737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 140779203370135171953965 52792201263800689482737)
                ·
                  refine ⟨39594150947850517112053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52792201263800689482737 39594150947850517112053)
                  ·
                    rfl

theorem cell20_86748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 3, 1, 3, 2].length) (baseStart_86748 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_86748 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_86748 prefixEnd_86748 := by exact prefixLift 86748
  have htrace : WordTrace (prefixWord ++ tailWord_86748) baseStart_86748 baseEnd_86748 := by
    simpa [prefixWord, tailWord_86748, baseEnd_86748] using wordTrace_append hprefix tailTrace_86748
  have hstable : (prefixWord ++ tailWord_86748).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86748).length < 2 ^ (prefixWord ++ tailWord_86748).sum := by decide
  have hdescent : baseEnd_86748 < baseStart_86748 := by decide
  rcases family_descends (prefixWord ++ tailWord_86748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86780 : List Nat := [2, 2, 2, 1, 3, 3, 2, 5]
def baseStart_86780 : Nat := 118140960795 + 86780 * 2 ^ 59
def prefixEnd_86780 : Nat := 4983230072969 + 3 ^ 40 * 86780 * 2
def baseEnd_86780 : Nat := 13202918873266876015085

theorem tailTrace_86780 : CollatzResearch.WordTrace tailWord_86780 prefixEnd_86780 13202918873266876015085 := by
  unfold tailWord_86780
  simp only [CollatzResearch.WordTrace]
  refine ⟨1582563312809177844580897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2110084417078903792774529 1582563312809177844580897)
  ·
    refine ⟨1186922484606883383435673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1582563312809177844580897 1186922484606883383435673)
    ·
      refine ⟨890191863455162537576755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1186922484606883383435673 890191863455162537576755)
      ·
        refine ⟨1335287795182743806365133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 890191863455162537576755 1335287795182743806365133)
        ·
          refine ⟨500732923193528927386925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1335287795182743806365133 500732923193528927386925)
          ·
            refine ⟨187774846197573347770097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 500732923193528927386925 187774846197573347770097)
            ·
              refine ⟨140831134648180010827573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 187774846197573347770097 140831134648180010827573)
              ·
                refine ⟨13202918873266876015085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 140831134648180010827573 13202918873266876015085)
                ·
                  rfl

theorem cell20_86780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 2, 5].length) (baseStart_86780 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_86780 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_86780 prefixEnd_86780 := by exact prefixLift 86780
  have htrace : WordTrace (prefixWord ++ tailWord_86780) baseStart_86780 baseEnd_86780 := by
    simpa [prefixWord, tailWord_86780, baseEnd_86780] using wordTrace_append hprefix tailTrace_86780
  have hstable : (prefixWord ++ tailWord_86780).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86780).length < 2 ^ (prefixWord ++ tailWord_86780).sum := by decide
  have hdescent : baseEnd_86780 < baseStart_86780 := by decide
  rcases family_descends (prefixWord ++ tailWord_86780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86794 : List Nat := [3, 1, 2, 2, 1, 2, 2, 1, 6]
def baseStart_86794 : Nat := 118140960795 + 86794 * 2 ^ 59
def prefixEnd_86794 : Nat := 4983230072969 + 3 ^ 40 * 86794 * 2
def baseEnd_86794 : Nat := 39615146601278801578531

theorem tailTrace_86794 : CollatzResearch.WordTrace tailWord_86794 prefixEnd_86794 39615146601278801578531 := by
  unfold tailWord_86794
  simp only [CollatzResearch.WordTrace]
  refine ⟨791409311891909020042859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2110424831711757386780957 791409311891909020042859)
  ·
    refine ⟨1187113967837863530064289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 791409311891909020042859 1187113967837863530064289)
    ·
      refine ⟨890335475878397647548217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1187113967837863530064289 890335475878397647548217)
      ·
        refine ⟨667751606908798235661163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 890335475878397647548217 667751606908798235661163)
        ·
          refine ⟨1001627410363197353491745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 667751606908798235661163 1001627410363197353491745)
          ·
            refine ⟨751220557772398015118809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1001627410363197353491745 751220557772398015118809)
            ·
              refine ⟨563415418329298511339107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 751220557772398015118809 563415418329298511339107)
              ·
                refine ⟨845123127493947767008661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 563415418329298511339107 845123127493947767008661)
                ·
                  refine ⟨39615146601278801578531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 845123127493947767008661 39615146601278801578531)
                  ·
                    rfl

theorem cell20_86794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 1, 6].length) (baseStart_86794 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_86794 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_86794 prefixEnd_86794 := by exact prefixLift 86794
  have htrace : WordTrace (prefixWord ++ tailWord_86794) baseStart_86794 baseEnd_86794 := by
    simpa [prefixWord, tailWord_86794, baseEnd_86794] using wordTrace_append hprefix tailTrace_86794
  have hstable : (prefixWord ++ tailWord_86794).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86794).length < 2 ^ (prefixWord ++ tailWord_86794).sum := by decide
  have hdescent : baseEnd_86794 < baseStart_86794 := by decide
  rcases family_descends (prefixWord ++ tailWord_86794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86801 : List Nat := [1, 2, 2, 1, 1, 3, 4, 6]
def baseStart_86801 : Nat := 118140960795 + 86801 * 2 ^ 59
def prefixEnd_86801 : Nat := 4983230072969 + 3 ^ 40 * 86801 * 2
def baseEnd_86801 : Nat := 13206113864005962781723

theorem tailTrace_86801 : CollatzResearch.WordTrace tailWord_86801 prefixEnd_86801 13206113864005962781723 := by
  unfold tailWord_86801
  simp only [CollatzResearch.WordTrace]
  refine ⟨3165892558542276275676257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2110595039028184183784171 3165892558542276275676257)
  ·
    refine ⟨2374419418906707206757193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3165892558542276275676257 2374419418906707206757193)
    ·
      refine ⟨1780814564180030405067895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2374419418906707206757193 1780814564180030405067895)
      ·
        refine ⟨2671221846270045607601843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1780814564180030405067895 2671221846270045607601843)
        ·
          refine ⟨4006832769405068411402765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2671221846270045607601843 4006832769405068411402765)
          ·
            refine ⟨1502562288526900654276037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4006832769405068411402765 1502562288526900654276037)
            ·
              refine ⟨281730429098793872676757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1502562288526900654276037 281730429098793872676757)
              ·
                refine ⟨13206113864005962781723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 281730429098793872676757 13206113864005962781723)
                ·
                  rfl

theorem cell20_86801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 4, 6].length) (baseStart_86801 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_86801 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_86801 prefixEnd_86801 := by exact prefixLift 86801
  have htrace : WordTrace (prefixWord ++ tailWord_86801) baseStart_86801 baseEnd_86801 := by
    simpa [prefixWord, tailWord_86801, baseEnd_86801] using wordTrace_append hprefix tailTrace_86801
  have hstable : (prefixWord ++ tailWord_86801).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86801).length < 2 ^ (prefixWord ++ tailWord_86801).sum := by decide
  have hdescent : baseEnd_86801 < baseStart_86801 := by decide
  rcases family_descends (prefixWord ++ tailWord_86801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86856 : List Nat := [2, 1, 3, 1, 1, 3, 5, 4]
def baseStart_86856 : Nat := 118140960795 + 86856 * 2 ^ 59
def prefixEnd_86856 : Nat := 4983230072969 + 3 ^ 40 * 86856 * 2
def baseEnd_86856 : Nat := 13214481696894047170537

theorem tailTrace_86856 : CollatzResearch.WordTrace tailWord_86856 prefixEnd_86856 13214481696894047170537 := by
  unfold tailWord_86856
  simp only [CollatzResearch.WordTrace]
  refine ⟨1583949286671510334464211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2111932382228680445952281 1583949286671510334464211)
  ·
    refine ⟨2375923930007265501696317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1583949286671510334464211 2375923930007265501696317)
    ·
      refine ⟨890971473752724563136119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2375923930007265501696317 890971473752724563136119)
      ·
        refine ⟨1336457210629086844704179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 890971473752724563136119 1336457210629086844704179)
        ·
          refine ⟨2004685815943630267056269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1336457210629086844704179 2004685815943630267056269)
          ·
            refine ⟨751757180978861350146101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2004685815943630267056269 751757180978861350146101)
            ·
              refine ⟨70477235716768251576197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 751757180978861350146101 70477235716768251576197)
              ·
                refine ⟨13214481696894047170537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 70477235716768251576197 13214481696894047170537)
                ·
                  rfl

theorem cell20_86856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 5, 4].length) (baseStart_86856 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_86856 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_86856 prefixEnd_86856 := by exact prefixLift 86856
  have htrace : WordTrace (prefixWord ++ tailWord_86856) baseStart_86856 baseEnd_86856 := by
    simpa [prefixWord, tailWord_86856, baseEnd_86856] using wordTrace_append hprefix tailTrace_86856
  have hstable : (prefixWord ++ tailWord_86856).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86856).length < 2 ^ (prefixWord ++ tailWord_86856).sum := by decide
  have hdescent : baseEnd_86856 < baseStart_86856 := by decide
  rcases family_descends (prefixWord ++ tailWord_86856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86866 : List Nat := [3, 2, 2, 1, 1, 2, 4, 3, 2]
def baseStart_86866 : Nat := 118140960795 + 86866 * 2 ^ 59
def prefixEnd_86866 : Nat := 4983230072969 + 3 ^ 40 * 86866 * 2
def baseEnd_86866 : Nat := 39648009363166551178237

theorem tailTrace_86866 : CollatzResearch.WordTrace tailWord_86866 prefixEnd_86866 39648009363166551178237 := by
  unfold tailWord_86866
  simp only [CollatzResearch.WordTrace]
  refine ⟨792065825826698094198113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2112175535537861584528301 792065825826698094198113)
  ·
    refine ⟨594049369370023570648585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 792065825826698094198113 594049369370023570648585)
    ·
      refine ⟨445537027027517677986439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 594049369370023570648585 445537027027517677986439)
      ·
        refine ⟨668305540541276516979659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 445537027027517677986439 668305540541276516979659)
        ·
          refine ⟨1002458310811914775469489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 668305540541276516979659 1002458310811914775469489)
          ·
            refine ⟨751843733108936081602117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1002458310811914775469489 751843733108936081602117)
            ·
              refine ⟨140970699957925515300397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 751843733108936081602117 140970699957925515300397)
              ·
                refine ⟨52864012484222068237649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 140970699957925515300397 52864012484222068237649)
                ·
                  refine ⟨39648009363166551178237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52864012484222068237649 39648009363166551178237)
                  ·
                    rfl

theorem cell20_86866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 4, 3, 2].length) (baseStart_86866 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_86866 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_86866 prefixEnd_86866 := by exact prefixLift 86866
  have htrace : WordTrace (prefixWord ++ tailWord_86866) baseStart_86866 baseEnd_86866 := by
    simpa [prefixWord, tailWord_86866, baseEnd_86866] using wordTrace_append hprefix tailTrace_86866
  have hstable : (prefixWord ++ tailWord_86866).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86866).length < 2 ^ (prefixWord ++ tailWord_86866).sum := by decide
  have hdescent : baseEnd_86866 < baseStart_86866 := by decide
  rcases family_descends (prefixWord ++ tailWord_86866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86887 : List Nat := [1, 1, 5, 1, 2, 3, 2, 1, 4]
def baseStart_86887 : Nat := 118140960795 + 86887 * 2 ^ 59
def prefixEnd_86887 : Nat := 4983230072969 + 3 ^ 40 * 86887 * 2
def baseEnd_86887 : Nat := 39657594335383811478151

theorem tailTrace_86887 : CollatzResearch.WordTrace tailWord_86887 prefixEnd_86887 39657594335383811478151 := by
  unfold tailWord_86887
  simp only [CollatzResearch.WordTrace]
  refine ⟨3169029236230712963306915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2112686157487141975537943 3169029236230712963306915)
  ·
    refine ⟨4753543854346069444960373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3169029236230712963306915 4753543854346069444960373)
    ·
      refine ⟨445644736344944010465035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4753543854346069444960373 445644736344944010465035)
      ·
        refine ⟨668467104517416015697553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 445644736344944010465035 668467104517416015697553)
        ·
          refine ⟨501350328388062011773165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 668467104517416015697553 501350328388062011773165)
          ·
            refine ⟨188006373145523254414937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 501350328388062011773165 188006373145523254414937)
            ·
              refine ⟨141004779859142440811203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 188006373145523254414937 141004779859142440811203)
              ·
                refine ⟨211507169788713661216805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 141004779859142440811203 211507169788713661216805)
                ·
                  refine ⟨39657594335383811478151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 211507169788713661216805 39657594335383811478151)
                  ·
                    rfl

theorem cell20_86887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 2, 1, 4].length) (baseStart_86887 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_86887 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_86887 prefixEnd_86887 := by exact prefixLift 86887
  have htrace : WordTrace (prefixWord ++ tailWord_86887) baseStart_86887 baseEnd_86887 := by
    simpa [prefixWord, tailWord_86887, baseEnd_86887] using wordTrace_append hprefix tailTrace_86887
  have hstable : (prefixWord ++ tailWord_86887).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86887).length < 2 ^ (prefixWord ++ tailWord_86887).sum := by decide
  have hdescent : baseEnd_86887 < baseStart_86887 := by decide
  rcases family_descends (prefixWord ++ tailWord_86887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86915 : List Nat := [1, 1, 1, 3, 4, 1, 3, 6]
def baseStart_86915 : Nat := 118140960795 + 86915 * 2 ^ 59
def prefixEnd_86915 : Nat := 4983230072969 + 3 ^ 40 * 86915 * 2
def baseEnd_86915 : Nat := 13223458099446719514901

theorem tailTrace_86915 : CollatzResearch.WordTrace tailWord_86915 prefixEnd_86915 13223458099446719514901 := by
  unfold tailWord_86915
  simp only [CollatzResearch.WordTrace]
  refine ⟨3170050480129273745326199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2113366986752849163550799 3170050480129273745326199)
  ·
    refine ⟨4755075720193910617989299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3170050480129273745326199 4755075720193910617989299)
    ·
      refine ⟨7132613580290865926983949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4755075720193910617989299 7132613580290865926983949)
      ·
        refine ⟨2674730092609074722618981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7132613580290865926983949 2674730092609074722618981)
        ·
          refine ⟨501511892364201510491059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2674730092609074722618981 501511892364201510491059)
          ·
            refine ⟨752267838546302265736589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 501511892364201510491059 752267838546302265736589)
            ·
              refine ⟨282100439454863349651221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 752267838546302265736589 282100439454863349651221)
              ·
                refine ⟨13223458099446719514901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 282100439454863349651221 13223458099446719514901)
                ·
                  rfl

theorem cell20_86915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 3, 6].length) (baseStart_86915 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_86915 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_86915 prefixEnd_86915 := by exact prefixLift 86915
  have htrace : WordTrace (prefixWord ++ tailWord_86915) baseStart_86915 baseEnd_86915 := by
    simpa [prefixWord, tailWord_86915, baseEnd_86915] using wordTrace_append hprefix tailTrace_86915
  have hstable : (prefixWord ++ tailWord_86915).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86915).length < 2 ^ (prefixWord ++ tailWord_86915).sum := by decide
  have hdescent : baseEnd_86915 < baseStart_86915 := by decide
  rcases family_descends (prefixWord ++ tailWord_86915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86953 : List Nat := [1, 2, 1, 1, 1, 1, 8, 5]
def baseStart_86953 : Nat := 118140960795 + 86953 * 2 ^ 59
def prefixEnd_86953 : Nat := 4983230072969 + 3 ^ 40 * 86953 * 2
def baseEnd_86953 : Nat := 13229239511260305092627

theorem tailTrace_86953 : CollatzResearch.WordTrace tailWord_86953 prefixEnd_86953 13229239511260305092627 := by
  unfold tailWord_86953
  simp only [CollatzResearch.WordTrace]
  refine ⟨3171436453991606235209513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2114290969327737490139675 3171436453991606235209513)
  ·
    refine ⟨2378577340493704676407135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3171436453991606235209513 2378577340493704676407135)
    ·
      refine ⟨3567866010740557014610703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2378577340493704676407135 3567866010740557014610703)
      ·
        refine ⟨5351799016110835521916055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3567866010740557014610703 5351799016110835521916055)
        ·
          refine ⟨8027698524166253282874083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5351799016110835521916055 8027698524166253282874083)
          ·
            refine ⟨12041547786249379924311125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8027698524166253282874083 12041547786249379924311125)
            ·
              refine ⟨141111888120109920988021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 12041547786249379924311125 141111888120109920988021)
              ·
                refine ⟨13229239511260305092627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 141111888120109920988021 13229239511260305092627)
                ·
                  rfl

theorem cell20_86953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 8, 5].length) (baseStart_86953 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_86953 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_86953 prefixEnd_86953 := by exact prefixLift 86953
  have htrace : WordTrace (prefixWord ++ tailWord_86953) baseStart_86953 baseEnd_86953 := by
    simpa [prefixWord, tailWord_86953, baseEnd_86953] using wordTrace_append hprefix tailTrace_86953
  have hstable : (prefixWord ++ tailWord_86953).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86953).length < 2 ^ (prefixWord ++ tailWord_86953).sum := by decide
  have hdescent : baseEnd_86953 < baseStart_86953 := by decide
  rcases family_descends (prefixWord ++ tailWord_86953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86989 : List Nat := [1, 6, 3, 1, 2, 1, 2, 2, 2]
def baseStart_86989 : Nat := 118140960795 + 86989 * 2 ^ 59
def prefixEnd_86989 : Nat := 4983230072969 + 3 ^ 40 * 86989 * 2
def baseEnd_86989 : Nat := 39704149914724790077735

theorem tailTrace_86989 : CollatzResearch.WordTrace tailWord_86989 prefixEnd_86989 39704149914724790077735 := by
  unfold tailWord_86989
  simp only [CollatzResearch.WordTrace]
  refine ⟨3172749481861184383520021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2115166321240789589013347 3172749481861184383520021)
  ·
    refine ⟨148722631962243017977501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 3172749481861184383520021 148722631962243017977501)
    ·
      refine ⟨55770986985841131741563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 148722631962243017977501 55770986985841131741563)
      ·
        refine ⟨83656480478761697612345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55770986985841131741563 83656480478761697612345)
        ·
          refine ⟨62742360359071273209259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83656480478761697612345 62742360359071273209259)
          ·
            refine ⟨94113540538606909813889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62742360359071273209259 94113540538606909813889)
            ·
              refine ⟨70585155403955182360417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94113540538606909813889 70585155403955182360417)
              ·
                refine ⟨52938866552966386770313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70585155403955182360417 52938866552966386770313)
                ·
                  refine ⟨39704149914724790077735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52938866552966386770313 39704149914724790077735)
                  ·
                    rfl

theorem cell20_86989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 1, 2, 2, 2].length) (baseStart_86989 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_86989 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_86989 prefixEnd_86989 := by exact prefixLift 86989
  have htrace : WordTrace (prefixWord ++ tailWord_86989) baseStart_86989 baseEnd_86989 := by
    simpa [prefixWord, tailWord_86989, baseEnd_86989] using wordTrace_append hprefix tailTrace_86989
  have hstable : (prefixWord ++ tailWord_86989).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86989).length < 2 ^ (prefixWord ++ tailWord_86989).sum := by decide
  have hdescent : baseEnd_86989 < baseStart_86989 := by decide
  rcases family_descends (prefixWord ++ tailWord_86989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86994 : List Nat := [3, 2, 2, 3, 1, 1, 1, 4, 3]
def baseStart_86994 : Nat := 118140960795 + 86994 * 2 ^ 59
def prefixEnd_86994 : Nat := 4983230072969 + 3 ^ 40 * 86994 * 2
def baseEnd_86994 : Nat := 39706432050966994911047

theorem tailTrace_86994 : CollatzResearch.WordTrace tailWord_86994 prefixEnd_86994 39706432050966994911047 := by
  unfold tailWord_86994
  simp only [CollatzResearch.WordTrace]
  refine ⟨793232961710767559363009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2115287897895380158301357 793232961710767559363009)
  ·
    refine ⟨594924721283075669522257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 793232961710767559363009 594924721283075669522257)
    ·
      refine ⟨446193540962306752141693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 594924721283075669522257 446193540962306752141693)
      ·
        refine ⟨167322577860865032053135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 446193540962306752141693 167322577860865032053135)
        ·
          refine ⟨250983866791297548079703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 167322577860865032053135 250983866791297548079703)
          ·
            refine ⟨376475800186946322119555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 250983866791297548079703 376475800186946322119555)
            ·
              refine ⟨564713700280419483179333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 376475800186946322119555 564713700280419483179333)
              ·
                refine ⟨105883818802578653096125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 564713700280419483179333 105883818802578653096125)
                ·
                  refine ⟨39706432050966994911047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 105883818802578653096125 39706432050966994911047)
                  ·
                    rfl

theorem cell20_86994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 4, 3].length) (baseStart_86994 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_86994 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_86994 prefixEnd_86994 := by exact prefixLift 86994
  have htrace : WordTrace (prefixWord ++ tailWord_86994) baseStart_86994 baseEnd_86994 := by
    simpa [prefixWord, tailWord_86994, baseEnd_86994] using wordTrace_append hprefix tailTrace_86994
  have hstable : (prefixWord ++ tailWord_86994).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86994).length < 2 ^ (prefixWord ++ tailWord_86994).sum := by decide
  have hdescent : baseEnd_86994 < baseStart_86994 := by decide
  rcases family_descends (prefixWord ++ tailWord_86994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_87112 : List Nat := [2, 1, 3, 1, 1, 1, 3, 3, 5]
def baseStart_87112 : Nat := 118140960795 + 87112 * 2 ^ 59
def prefixEnd_87112 : Nat := 4983230072969 + 3 ^ 40 * 87112 * 2
def baseEnd_87112 : Nat := 39760290466283028977231

theorem tailTrace_87112 : CollatzResearch.WordTrace tailWord_87112 prefixEnd_87112 39760290466283028977231 := by
  unfold tailWord_87112
  simp only [CollatzResearch.WordTrace]
  refine ⟨1588617830207788195123795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2118157106943717593498393 1588617830207788195123795)
  ·
    refine ⟨2382926745311682292685693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1588617830207788195123795 2382926745311682292685693)
    ·
      refine ⟨893597529491880859757135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2382926745311682292685693 893597529491880859757135)
      ·
        refine ⟨1340396294237821289635703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 893597529491880859757135 1340396294237821289635703)
        ·
          refine ⟨2010594441356731934453555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1340396294237821289635703 2010594441356731934453555)
          ·
            refine ⟨3015891662035097901680333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2010594441356731934453555 3015891662035097901680333)
            ·
              refine ⟨1130959373263161713130125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3015891662035097901680333 1130959373263161713130125)
              ·
                refine ⟨424109764973685642423797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1130959373263161713130125 424109764973685642423797)
                ·
                  refine ⟨39760290466283028977231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 424109764973685642423797 39760290466283028977231)
                  ·
                    rfl

theorem cell20_87112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 3, 5].length) (baseStart_87112 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_87112 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_87112 prefixEnd_87112 := by exact prefixLift 87112
  have htrace : WordTrace (prefixWord ++ tailWord_87112) baseStart_87112 baseEnd_87112 := by
    simpa [prefixWord, tailWord_87112, baseEnd_87112] using wordTrace_append hprefix tailTrace_87112
  have hstable : (prefixWord ++ tailWord_87112).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_87112).length < 2 ^ (prefixWord ++ tailWord_87112).sum := by decide
  have hdescent : baseEnd_87112 < baseStart_87112 := by decide
  rcases family_descends (prefixWord ++ tailWord_87112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_87122 : List Nat := [3, 2, 2, 1, 3, 2, 2, 5]
def baseStart_87122 : Nat := 118140960795 + 87122 * 2 ^ 59
def prefixEnd_87122 : Nat := 4983230072969 + 3 ^ 40 * 87122 * 2
def baseEnd_87122 : Nat := 13254951579589146214619

theorem tailTrace_87122 : CollatzResearch.WordTrace tailWord_87122 prefixEnd_87122 13254951579589146214619 := by
  unfold tailWord_87122
  simp only [CollatzResearch.WordTrace]
  refine ⟨794400097594837024527905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2118400260252898732074413 794400097594837024527905)
  ·
    refine ⟨595800073196127768395929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 794400097594837024527905 595800073196127768395929)
    ·
      refine ⟨446850054897095826296947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 595800073196127768395929 446850054897095826296947)
      ·
        refine ⟨670275082345643739445421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 446850054897095826296947 670275082345643739445421)
        ·
          refine ⟨251353155879616402292033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 670275082345643739445421 251353155879616402292033)
          ·
            refine ⟨188514866909712301719025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 251353155879616402292033 188514866909712301719025)
            ·
              refine ⟨141386150182284226289269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 188514866909712301719025 141386150182284226289269)
              ·
                refine ⟨13254951579589146214619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 141386150182284226289269 13254951579589146214619)
                ·
                  rfl

theorem cell20_87122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 2, 5].length) (baseStart_87122 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_87122 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_87122 prefixEnd_87122 := by exact prefixLift 87122
  have htrace : WordTrace (prefixWord ++ tailWord_87122) baseStart_87122 baseEnd_87122 := by
    simpa [prefixWord, tailWord_87122, baseEnd_87122] using wordTrace_append hprefix tailTrace_87122
  have hstable : (prefixWord ++ tailWord_87122).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_87122).length < 2 ^ (prefixWord ++ tailWord_87122).sum := by decide
  have hdescent : baseEnd_87122 < baseStart_87122 := by decide
  rcases family_descends (prefixWord ++ tailWord_87122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_87143 : List Nat := [1, 1, 5, 1, 1, 3, 2, 6]
def baseStart_87143 : Nat := 118140960795 + 87143 * 2 ^ 59
def prefixEnd_87143 : Nat := 4983230072969 + 3 ^ 40 * 87143 * 2
def baseEnd_87143 : Nat := 13258146570328232981257

theorem tailTrace_87143 : CollatzResearch.WordTrace tailWord_87143 prefixEnd_87143 13258146570328232981257 := by
  unfold tailWord_87143
  simp only [CollatzResearch.WordTrace]
  refine ⟨3178366323303268684626083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2118910882202179123084055 3178366323303268684626083)
  ·
    refine ⟨4767549484954903026939125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3178366323303268684626083 4767549484954903026939125)
    ·
      refine ⟨446957764214522158775543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4767549484954903026939125 446957764214522158775543)
      ·
        refine ⟨670436646321783238163315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 446957764214522158775543 670436646321783238163315)
        ·
          refine ⟨1005654969482674857244973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 670436646321783238163315 1005654969482674857244973)
          ·
            refine ⟨377120613556003071466865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1005654969482674857244973 377120613556003071466865)
            ·
              refine ⟨282840460167002303600149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 377120613556003071466865 282840460167002303600149)
              ·
                refine ⟨13258146570328232981257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 282840460167002303600149 13258146570328232981257)
                ·
                  rfl

theorem cell20_87143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 2, 6].length) (baseStart_87143 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_87143 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_87143 prefixEnd_87143 := by exact prefixLift 87143
  have htrace : WordTrace (prefixWord ++ tailWord_87143) baseStart_87143 baseEnd_87143 := by
    simpa [prefixWord, tailWord_87143, baseEnd_87143] using wordTrace_append hprefix tailTrace_87143
  have hstable : (prefixWord ++ tailWord_87143).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_87143).length < 2 ^ (prefixWord ++ tailWord_87143).sum := by decide
  have hdescent : baseEnd_87143 < baseStart_87143 := by decide
  rcases family_descends (prefixWord ++ tailWord_87143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_87229 : List Nat := [1, 4, 1, 2, 1, 1, 4, 4, 2]
def baseStart_87229 : Nat := 118140960795 + 87229 * 2 ^ 59
def prefixEnd_87229 : Nat := 4983230072969 + 3 ^ 40 * 87229 * 2
def baseEnd_87229 : Nat := 39813692454350622076753

theorem tailTrace_87229 : CollatzResearch.WordTrace tailWord_87229 prefixEnd_87229 39813692454350622076753 := by
  unfold tailWord_87229
  simp only [CollatzResearch.WordTrace]
  refine ⟨3181503000991705372256741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2121002000661136914837827 3181503000991705372256741)
  ·
    refine ⟨596531812685944757298139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3181503000991705372256741 596531812685944757298139)
    ·
      refine ⟨894797719028917135947209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 596531812685944757298139 894797719028917135947209)
      ·
        refine ⟨671098289271687851960407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 894797719028917135947209 671098289271687851960407)
        ·
          refine ⟨1006647433907531777940611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 671098289271687851960407 1006647433907531777940611)
          ·
            refine ⟨1509971150861297666910917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1006647433907531777940611 1509971150861297666910917)
            ·
              refine ⟨283119590786493312545797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1509971150861297666910917 283119590786493312545797)
              ·
                refine ⟨53084923272467496102337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 283119590786493312545797 53084923272467496102337)
                ·
                  refine ⟨39813692454350622076753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53084923272467496102337 39813692454350622076753)
                  ·
                    rfl

theorem cell20_87229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 4, 4, 2].length) (baseStart_87229 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_87229 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_87229 prefixEnd_87229 := by exact prefixLift 87229
  have htrace : WordTrace (prefixWord ++ tailWord_87229) baseStart_87229 baseEnd_87229 := by
    simpa [prefixWord, tailWord_87229, baseEnd_87229] using wordTrace_append hprefix tailTrace_87229
  have hstable : (prefixWord ++ tailWord_87229).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_87229).length < 2 ^ (prefixWord ++ tailWord_87229).sum := by decide
  have hdescent : baseEnd_87229 < baseStart_87229 := by decide
  rcases family_descends (prefixWord ++ tailWord_87229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_87250 : List Nat := [3, 2, 2, 2, 1, 1, 1, 4, 4]
def baseStart_87250 : Nat := 118140960795 + 87250 * 2 ^ 59
def prefixEnd_87250 : Nat := 4983230072969 + 3 ^ 40 * 87250 * 2
def baseEnd_87250 : Nat := 39823277426567882376667

theorem tailTrace_87250 : CollatzResearch.WordTrace tailWord_87250 prefixEnd_87250 39823277426567882376667 := by
  unfold tailWord_87250
  simp only [CollatzResearch.WordTrace]
  refine ⟨795567233478906489692801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2121512622610417305847469 795567233478906489692801)
  ·
    refine ⟨596675425109179867269601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 795567233478906489692801 596675425109179867269601)
    ·
      refine ⟨447506568831884900452201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 596675425109179867269601 447506568831884900452201)
      ·
        refine ⟨335629926623913675339151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 447506568831884900452201 335629926623913675339151)
        ·
          refine ⟨503444889935870513008727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 335629926623913675339151 503444889935870513008727)
          ·
            refine ⟨755167334903805769513091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 503444889935870513008727 755167334903805769513091)
            ·
              refine ⟨1132751002355708654269637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 755167334903805769513091 1132751002355708654269637)
              ·
                refine ⟨212390812941695372675557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1132751002355708654269637 212390812941695372675557)
                ·
                  refine ⟨39823277426567882376667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 212390812941695372675557 39823277426567882376667)
                  ·
                    rfl

theorem cell20_87250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 4, 4].length) (baseStart_87250 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_87250 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_87250 prefixEnd_87250 := by exact prefixLift 87250
  have htrace : WordTrace (prefixWord ++ tailWord_87250) baseStart_87250 baseEnd_87250 := by
    simpa [prefixWord, tailWord_87250, baseEnd_87250] using wordTrace_append hprefix tailTrace_87250
  have hstable : (prefixWord ++ tailWord_87250).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_87250).length < 2 ^ (prefixWord ++ tailWord_87250).sum := by decide
  have hdescent : baseEnd_87250 < baseStart_87250 := by decide
  rcases family_descends (prefixWord ++ tailWord_87250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_87253 : List Nat := [1, 3, 2, 4, 1, 3, 2, 4]
def baseStart_87253 : Nat := 118140960795 + 87253 * 2 ^ 59
def prefixEnd_87253 : Nat := 4983230072969 + 3 ^ 40 * 87253 * 2
def baseEnd_87253 : Nat := 13274882236104401758885

theorem tailTrace_87253 : CollatzResearch.WordTrace tailWord_87253 prefixEnd_87253 13274882236104401758885 := by
  unfold tailWord_87253
  simp only [CollatzResearch.WordTrace]
  refine ⟨3182378352904757471130413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2121585568603171647420275 3182378352904757471130413)
  ·
    refine ⟨1193391882339284051673905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3182378352904757471130413 1193391882339284051673905)
    ·
      refine ⟨895043911754463038755429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1193391882339284051673905 895043911754463038755429)
      ·
        refine ⟨167820733453961819766643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 895043911754463038755429 167820733453961819766643)
        ·
          refine ⟨251731100180942729649965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 167820733453961819766643 251731100180942729649965)
          ·
            refine ⟨94399162567853523618737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 251731100180942729649965 94399162567853523618737)
            ·
              refine ⟨70799371925890142714053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94399162567853523618737 70799371925890142714053)
              ·
                refine ⟨13274882236104401758885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 70799371925890142714053 13274882236104401758885)
                ·
                  rfl

theorem cell20_87253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 3, 2, 4].length) (baseStart_87253 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_87253 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_87253 prefixEnd_87253 := by exact prefixLift 87253
  have htrace : WordTrace (prefixWord ++ tailWord_87253) baseStart_87253 baseEnd_87253 := by
    simpa [prefixWord, tailWord_87253, baseEnd_87253] using wordTrace_append hprefix tailTrace_87253
  have hstable : (prefixWord ++ tailWord_87253).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_87253).length < 2 ^ (prefixWord ++ tailWord_87253).sum := by decide
  have hdescent : baseEnd_87253 < baseStart_87253 := by decide
  rcases family_descends (prefixWord ++ tailWord_87253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_87264 : List Nat := [2, 1, 1, 3, 1, 4, 1, 2, 5]
def baseStart_87264 : Nat := 118140960795 + 87264 * 2 ^ 59
def prefixEnd_87264 : Nat := 4983230072969 + 3 ^ 40 * 87264 * 2
def baseEnd_87264 : Nat := 39829667408046055909943

theorem tailTrace_87264 : CollatzResearch.WordTrace tailWord_87264 prefixEnd_87264 39829667408046055909943 := by
  unfold tailWord_87264
  simp only [CollatzResearch.WordTrace]
  refine ⟨1591389777932453174890423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2121853037243270899853897 1591389777932453174890423)
  ·
    refine ⟨2387084666898679762335635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1591389777932453174890423 2387084666898679762335635)
    ·
      refine ⟨3580627000348019643503453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2387084666898679762335635 3580627000348019643503453)
      ·
        refine ⟨1342735125130507366313795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3580627000348019643503453 1342735125130507366313795)
        ·
          refine ⟨2014102687695761049470693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1342735125130507366313795 2014102687695761049470693)
          ·
            refine ⟨377644253942955196775755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2014102687695761049470693 377644253942955196775755)
            ·
              refine ⟨566466380914432795163633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 377644253942955196775755 566466380914432795163633)
              ·
                refine ⟨424849785685824596372725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 566466380914432795163633 424849785685824596372725)
                ·
                  refine ⟨39829667408046055909943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 424849785685824596372725 39829667408046055909943)
                  ·
                    rfl

theorem cell20_87264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 2, 5].length) (baseStart_87264 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_87264 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_87264 prefixEnd_87264 := by exact prefixLift 87264
  have htrace : WordTrace (prefixWord ++ tailWord_87264) baseStart_87264 baseEnd_87264 := by
    simpa [prefixWord, tailWord_87264, baseEnd_87264] using wordTrace_append hprefix tailTrace_87264
  have hstable : (prefixWord ++ tailWord_87264).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_87264).length < 2 ^ (prefixWord ++ tailWord_87264).sum := by decide
  have hdescent : baseEnd_87264 < baseStart_87264 := by decide
  rcases family_descends (prefixWord ++ tailWord_87264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_87295 : List Nat := [1, 1, 2, 2, 1, 6, 2, 5]
def baseStart_87295 : Nat := 118140960795 + 87295 * 2 ^ 59
def prefixEnd_87295 : Nat := 4983230072969 + 3 ^ 40 * 87295 * 2
def baseEnd_87295 : Nat := 13281272217582575292161

theorem tailTrace_87295 : CollatzResearch.WordTrace tailWord_87295 prefixEnd_87295 13281272217582575292161 := by
  unfold tailWord_87295
  simp only [CollatzResearch.WordTrace]
  refine ⟨3183910218752598644159339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2122606812501732429439559 3183910218752598644159339)
  ·
    refine ⟨4775865328128897966239009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3183910218752598644159339 4775865328128897966239009)
    ·
      refine ⟨3581898996096673474679257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4775865328128897966239009 3581898996096673474679257)
      ·
        refine ⟨2686424247072505106009443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3581898996096673474679257 2686424247072505106009443)
        ·
          refine ⟨4029636370608757659014165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2686424247072505106009443 4029636370608757659014165)
          ·
            refine ⟨188889204872285515266289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 4029636370608757659014165 188889204872285515266289)
            ·
              refine ⟨141666903654214136449717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 188889204872285515266289 141666903654214136449717)
              ·
                refine ⟨13281272217582575292161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 141666903654214136449717 13281272217582575292161)
                ·
                  rfl

theorem cell20_87295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 2, 5].length) (baseStart_87295 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_87295 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_87295 prefixEnd_87295 := by exact prefixLift 87295
  have htrace : WordTrace (prefixWord ++ tailWord_87295) baseStart_87295 baseEnd_87295 := by
    simpa [prefixWord, tailWord_87295, baseEnd_87295] using wordTrace_append hprefix tailTrace_87295
  have hstable : (prefixWord ++ tailWord_87295).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_87295).length < 2 ^ (prefixWord ++ tailWord_87295).sum := by decide
  have hdescent : baseEnd_87295 < baseStart_87295 := by decide
  rcases family_descends (prefixWord ++ tailWord_87295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_87336 : List Nat := [2, 1, 5, 1, 2, 2, 2, 2, 3]
def baseStart_87336 : Nat := 118140960795 + 87336 * 2 ^ 59
def prefixEnd_87336 : Nat := 4983230072969 + 3 ^ 40 * 87336 * 2
def baseEnd_87336 : Nat := 39862530169933805509649

theorem tailTrace_87336 : CollatzResearch.WordTrace tailWord_87336 prefixEnd_87336 39862530169933805509649 := by
  unfold tailWord_87336
  simp only [CollatzResearch.WordTrace]
  refine ⟨1592702805802031323200931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2123603741069375097601241 1592702805802031323200931)
  ·
    refine ⟨2389054208703046984801397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1592702805802031323200931 2389054208703046984801397)
    ·
      refine ⟨223973832065910654825131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2389054208703046984801397 223973832065910654825131)
      ·
        refine ⟨335960748098865982237697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 223973832065910654825131 335960748098865982237697)
        ·
          refine ⟨251970561074149486678273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 335960748098865982237697 251970561074149486678273)
          ·
            refine ⟨188977920805612115008705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 251970561074149486678273 188977920805612115008705)
            ·
              refine ⟨141733440604209086256529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 188977920805612115008705 141733440604209086256529)
              ·
                refine ⟨106300080453156814692397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 141733440604209086256529 106300080453156814692397)
                ·
                  refine ⟨39862530169933805509649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 106300080453156814692397 39862530169933805509649)
                  ·
                    rfl

theorem cell20_87336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 2, 2, 3].length) (baseStart_87336 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_87336 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_87336 prefixEnd_87336 := by exact prefixLift 87336
  have htrace : WordTrace (prefixWord ++ tailWord_87336) baseStart_87336 baseEnd_87336 := by
    simpa [prefixWord, tailWord_87336, baseEnd_87336] using wordTrace_append hprefix tailTrace_87336
  have hstable : (prefixWord ++ tailWord_87336).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_87336).length < 2 ^ (prefixWord ++ tailWord_87336).sum := by decide
  have hdescent : baseEnd_87336 < baseStart_87336 := by decide
  rcases family_descends (prefixWord ++ tailWord_87336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_87378 : List Nat := [3, 2, 2, 1, 1, 1, 1, 4, 5]
def baseStart_87378 : Nat := 118140960795 + 87378 * 2 ^ 59
def prefixEnd_87378 : Nat := 4983230072969 + 3 ^ 40 * 87378 * 2
def baseEnd_87378 : Nat := 39881700114368326109477

theorem tailTrace_87378 : CollatzResearch.WordTrace tailWord_87378 prefixEnd_87378 39881700114368326109477 := by
  unfold tailWord_87378
  simp only [CollatzResearch.WordTrace]
  refine ⟨796734369362975954857697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2124624984967935879620525 796734369362975954857697)
  ·
    refine ⟨597550777022231966143273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 796734369362975954857697 597550777022231966143273)
    ·
      refine ⟨448163082766673974607455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 597550777022231966143273 448163082766673974607455)
      ·
        refine ⟨672244624150010961911183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 448163082766673974607455 672244624150010961911183)
        ·
          refine ⟨1008366936225016442866775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 672244624150010961911183 1008366936225016442866775)
          ·
            refine ⟨1512550404337524664300163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1008366936225016442866775 1512550404337524664300163)
            ·
              refine ⟨2268825606506286996450245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1512550404337524664300163 2268825606506286996450245)
              ·
                refine ⟨425404801219928811834421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2268825606506286996450245 425404801219928811834421)
                ·
                  refine ⟨39881700114368326109477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 425404801219928811834421 39881700114368326109477)
                  ·
                    rfl

theorem cell20_87378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 4, 5].length) (baseStart_87378 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_87378 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_87378 prefixEnd_87378 := by exact prefixLift 87378
  have htrace : WordTrace (prefixWord ++ tailWord_87378) baseStart_87378 baseEnd_87378 := by
    simpa [prefixWord, tailWord_87378, baseEnd_87378] using wordTrace_append hprefix tailTrace_87378
  have hstable : (prefixWord ++ tailWord_87378).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_87378).length < 2 ^ (prefixWord ++ tailWord_87378).sum := by decide
  have hdescent : baseEnd_87378 < baseStart_87378 := by decide
  rcases family_descends (prefixWord ++ tailWord_87378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_87381 : List Nat := [1, 3, 2, 2, 3, 1, 1, 5, 2]
def baseStart_87381 : Nat := 118140960795 + 87381 * 2 ^ 59
def prefixEnd_87381 : Nat := 4983230072969 + 3 ^ 40 * 87381 * 2
def baseEnd_87381 : Nat := 39883069396113649009465

theorem tailTrace_87381 : CollatzResearch.WordTrace tailWord_87381 prefixEnd_87381 39883069396113649009465 := by
  unfold tailWord_87381
  simp only [CollatzResearch.WordTrace]
  refine ⟨3187046896441035331789997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2124697930960690221193331 3187046896441035331789997)
  ·
    refine ⟨1195142586165388249421249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3187046896441035331789997 1195142586165388249421249)
    ·
      refine ⟨896356939624041187065937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1195142586165388249421249 896356939624041187065937)
      ·
        refine ⟨672267704718030890299453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 896356939624041187065937 672267704718030890299453)
        ·
          refine ⟨252100389269261583862295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 672267704718030890299453 252100389269261583862295)
          ·
            refine ⟨378150583903892375793443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 252100389269261583862295 378150583903892375793443)
            ·
              refine ⟨567225875855838563690165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 378150583903892375793443 567225875855838563690165)
              ·
                refine ⟨53177425861484865345953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 567225875855838563690165 53177425861484865345953)
                ·
                  refine ⟨39883069396113649009465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53177425861484865345953 39883069396113649009465)
                  ·
                    rfl

theorem cell20_87381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 5, 2].length) (baseStart_87381 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_87381 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_87381 prefixEnd_87381 := by exact prefixLift 87381
  have htrace : WordTrace (prefixWord ++ tailWord_87381) baseStart_87381 baseEnd_87381 := by
    simpa [prefixWord, tailWord_87381, baseEnd_87381] using wordTrace_append hprefix tailTrace_87381
  have hstable : (prefixWord ++ tailWord_87381).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_87381).length < 2 ^ (prefixWord ++ tailWord_87381).sum := by decide
  have hdescent : baseEnd_87381 < baseStart_87381 := by decide
  rcases family_descends (prefixWord ++ tailWord_87381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_87395 : List Nat := [1, 1, 1, 5, 2, 2, 3, 2, 3]
def baseStart_87395 : Nat := 118140960795 + 87395 * 2 ^ 59
def prefixEnd_87395 : Nat := 4983230072969 + 3 ^ 40 * 87395 * 2
def baseEnd_87395 : Nat := 39889459377591822542741

theorem tailTrace_87395 : CollatzResearch.WordTrace tailWord_87395 prefixEnd_87395 39889459377591822542741 := by
  unfold tailWord_87395
  simp only [CollatzResearch.WordTrace]
  refine ⟨3187557518390315722799639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2125038345593543815199759 3187557518390315722799639)
  ·
    refine ⟨4781336277585473584199459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3187557518390315722799639 4781336277585473584199459)
    ·
      refine ⟨7172004416378210376299189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4781336277585473584199459 7172004416378210376299189)
      ·
        refine ⟨672375414035457222778049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7172004416378210376299189 672375414035457222778049)
        ·
          refine ⟨504281560526592917083537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 672375414035457222778049 504281560526592917083537)
          ·
            refine ⟨378211170394944687812653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 504281560526592917083537 378211170394944687812653)
            ·
              refine ⟨141829188898104257929745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 378211170394944687812653 141829188898104257929745)
              ·
                refine ⟨106371891673578193447309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 141829188898104257929745 106371891673578193447309)
                ·
                  refine ⟨39889459377591822542741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 106371891673578193447309 39889459377591822542741)
                  ·
                    rfl

theorem cell20_87395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 3, 2, 3].length) (baseStart_87395 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_87395 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_87395 prefixEnd_87395 := by exact prefixLift 87395
  have htrace : WordTrace (prefixWord ++ tailWord_87395) baseStart_87395 baseEnd_87395 := by
    simpa [prefixWord, tailWord_87395, baseEnd_87395] using wordTrace_append hprefix tailTrace_87395
  have hstable : (prefixWord ++ tailWord_87395).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_87395).length < 2 ^ (prefixWord ++ tailWord_87395).sum := by decide
  have hdescent : baseEnd_87395 < baseStart_87395 := by decide
  rcases family_descends (prefixWord ++ tailWord_87395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_87461 : List Nat := [1, 3, 1, 2, 1, 1, 2, 5, 4]
def baseStart_87461 : Nat := 118140960795 + 87461 * 2 ^ 59
def prefixEnd_87461 : Nat := 4983230072969 + 3 ^ 40 * 87461 * 2
def baseEnd_87461 : Nat := 39919583575988926342471

theorem tailTrace_87461 : CollatzResearch.WordTrace tailWord_87461 prefixEnd_87461 39919583575988926342471 := by
  unfold tailWord_87461
  simp only [CollatzResearch.WordTrace]
  refine ⟨3189964736151208994702237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2126643157434139329801491 3189964736151208994702237)
  ·
    refine ⟨1196236776056703373013339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3189964736151208994702237 1196236776056703373013339)
    ·
      refine ⟨1794355164085055059520009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1196236776056703373013339 1794355164085055059520009)
      ·
        refine ⟨1345766373063791294640007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1794355164085055059520009 1345766373063791294640007)
        ·
          refine ⟨2018649559595686941960011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1345766373063791294640007 2018649559595686941960011)
          ·
            refine ⟨3027974339393530412940017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2018649559595686941960011 3027974339393530412940017)
            ·
              refine ⟨2270980754545147809705013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3027974339393530412940017 2270980754545147809705013)
              ·
                refine ⟨212904445738607607159845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2270980754545147809705013 212904445738607607159845)
                ·
                  refine ⟨39919583575988926342471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 212904445738607607159845 39919583575988926342471)
                  ·
                    rfl

theorem cell20_87461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 5, 4].length) (baseStart_87461 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_87461 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_87461 prefixEnd_87461 := by exact prefixLift 87461
  have htrace : WordTrace (prefixWord ++ tailWord_87461) baseStart_87461 baseEnd_87461 := by
    simpa [prefixWord, tailWord_87461, baseEnd_87461] using wordTrace_append hprefix tailTrace_87461
  have hstable : (prefixWord ++ tailWord_87461).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_87461).length < 2 ^ (prefixWord ++ tailWord_87461).sum := by decide
  have hdescent : baseEnd_87461 < baseStart_87461 := by decide
  rcases family_descends (prefixWord ++ tailWord_87461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_87468 : List Nat := [2, 2, 1, 1, 1, 1, 5, 7]
def baseStart_87468 : Nat := 118140960795 + 87468 * 2 ^ 59
def prefixEnd_87468 : Nat := 4983230072969 + 3 ^ 40 * 87468 * 2
def baseEnd_87468 : Nat := 13307592855576004369703

theorem tailTrace_87468 : CollatzResearch.WordTrace tailWord_87468 prefixEnd_87468 13307592855576004369703 := by
  unfold tailWord_87468
  simp only [CollatzResearch.WordTrace]
  refine ⟨1595110023562924595103529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2126813364750566126804705 1595110023562924595103529)
  ·
    refine ⟨1196332517672193446327647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1595110023562924595103529 1196332517672193446327647)
    ·
      refine ⟨1794498776508290169491471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1196332517672193446327647 1794498776508290169491471)
      ·
        refine ⟨2691748164762435254237207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1794498776508290169491471 2691748164762435254237207)
        ·
          refine ⟨4037622247143652881355811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2691748164762435254237207 4037622247143652881355811)
          ·
            refine ⟨6056433370715479322033717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4037622247143652881355811 6056433370715479322033717)
            ·
              refine ⟨567790628504576186440661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6056433370715479322033717 567790628504576186440661)
              ·
                refine ⟨13307592855576004369703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 567790628504576186440661 13307592855576004369703)
                ·
                  rfl

theorem cell20_87468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 7].length) (baseStart_87468 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_87468 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_87468 prefixEnd_87468 := by exact prefixLift 87468
  have htrace : WordTrace (prefixWord ++ tailWord_87468) baseStart_87468 baseEnd_87468 := by
    simpa [prefixWord, tailWord_87468, baseEnd_87468] using wordTrace_append hprefix tailTrace_87468
  have hstable : (prefixWord ++ tailWord_87468).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_87468).length < 2 ^ (prefixWord ++ tailWord_87468).sum := by decide
  have hdescent : baseEnd_87468 < baseStart_87468 := by decide
  rcases family_descends (prefixWord ++ tailWord_87468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_87506 : List Nat := [3, 2, 2, 13]
def baseStart_87506 : Nat := 118140960795 + 87506 * 2 ^ 59
def prefixEnd_87506 : Nat := 4983230072969 + 3 ^ 40 * 87506 * 2
def baseEnd_87506 : Nat := 164362645276414690709

theorem tailTrace_87506 : CollatzResearch.WordTrace tailWord_87506 prefixEnd_87506 164362645276414690709 := by
  unfold tailWord_87506
  simp only [CollatzResearch.WordTrace]
  refine ⟨797901505247045420022593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2127737347325454453393581 797901505247045420022593)
  ·
    refine ⟨598426128935284065016945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 797901505247045420022593 598426128935284065016945)
    ·
      refine ⟨448819596701463048762709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 598426128935284065016945 448819596701463048762709)
      ·
        refine ⟨164362645276414690709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 13 448819596701463048762709 164362645276414690709)
        ·
          rfl

theorem cell20_87506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 13].length) (baseStart_87506 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_87506 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_87506 prefixEnd_87506 := by exact prefixLift 87506
  have htrace : WordTrace (prefixWord ++ tailWord_87506) baseStart_87506 baseEnd_87506 := by
    simpa [prefixWord, tailWord_87506, baseEnd_87506] using wordTrace_append hprefix tailTrace_87506
  have hstable : (prefixWord ++ tailWord_87506).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_87506).length < 2 ^ (prefixWord ++ tailWord_87506).sum := by decide
  have hdescent : baseEnd_87506 < baseStart_87506 := by decide
  rcases family_descends (prefixWord ++ tailWord_87506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_87508 : List Nat := [2, 4, 1, 2, 4, 1, 2, 2, 2]
def baseStart_87508 : Nat := 118140960795 + 87508 * 2 ^ 59
def prefixEnd_87508 : Nat := 4983230072969 + 3 ^ 40 * 87508 * 2
def baseEnd_87508 : Nat := 39941035656665651775613

theorem tailTrace_87508 : CollatzResearch.WordTrace tailWord_87508 prefixEnd_87508 39941035656665651775613 := by
  unfold tailWord_87508
  simp only [CollatzResearch.WordTrace]
  refine ⟨1595839483490468010831589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2127785977987290681108785 1595839483490468010831589)
  ·
    refine ⟨299219903154462752030923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1595839483490468010831589 299219903154462752030923)
    ·
      refine ⟨448829854731694128046385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 299219903154462752030923 448829854731694128046385)
      ·
        refine ⟨336622391048770596034789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 448829854731694128046385 336622391048770596034789)
        ·
          refine ⟨63116698321644486756523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 336622391048770596034789 63116698321644486756523)
          ·
            refine ⟨94675047482466730134785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63116698321644486756523 94675047482466730134785)
            ·
              refine ⟨71006285611850047601089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94675047482466730134785 71006285611850047601089)
              ·
                refine ⟨53254714208887535700817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 71006285611850047601089 53254714208887535700817)
                ·
                  refine ⟨39941035656665651775613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53254714208887535700817 39941035656665651775613)
                  ·
                    rfl

theorem cell20_87508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 1, 2, 2, 2].length) (baseStart_87508 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_87508 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_87508 prefixEnd_87508 := by exact prefixLift 87508
  have htrace : WordTrace (prefixWord ++ tailWord_87508) baseStart_87508 baseEnd_87508 := by
    simpa [prefixWord, tailWord_87508, baseEnd_87508] using wordTrace_append hprefix tailTrace_87508
  have hstable : (prefixWord ++ tailWord_87508).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_87508).length < 2 ^ (prefixWord ++ tailWord_87508).sum := by decide
  have hdescent : baseEnd_87508 < baseStart_87508 := by decide
  rcases family_descends (prefixWord ++ tailWord_87508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_87509 : List Nat := [1, 3, 2, 3, 1, 1, 4, 2, 3]
def baseStart_87509 : Nat := 118140960795 + 87509 * 2 ^ 59
def prefixEnd_87509 : Nat := 4983230072969 + 3 ^ 40 * 87509 * 2
def baseEnd_87509 : Nat := 39941492083914092742275

theorem tailTrace_87509 : CollatzResearch.WordTrace tailWord_87509 prefixEnd_87509 39941492083914092742275 := by
  unfold tailWord_87509
  simp only [CollatzResearch.WordTrace]
  refine ⟨3191715439977313192449581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2127810293318208794966387 3191715439977313192449581)
  ·
    refine ⟨1196893289991492447168593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3191715439977313192449581 1196893289991492447168593)
    ·
      refine ⟨897669967493619335376445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1196893289991492447168593 897669967493619335376445)
      ·
        refine ⟨336626237810107250766167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 897669967493619335376445 336626237810107250766167)
        ·
          refine ⟨504939356715160876149251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 336626237810107250766167 504939356715160876149251)
          ·
            refine ⟨757409035072741314223877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 504939356715160876149251 757409035072741314223877)
            ·
              refine ⟨142014194076138996416977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 757409035072741314223877 142014194076138996416977)
              ·
                refine ⟨106510645557104247312733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 142014194076138996416977 106510645557104247312733)
                ·
                  refine ⟨39941492083914092742275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 106510645557104247312733 39941492083914092742275)
                  ·
                    rfl

theorem cell20_87509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 4, 2, 3].length) (baseStart_87509 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_87509 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_87509 prefixEnd_87509 := by exact prefixLift 87509
  have htrace : WordTrace (prefixWord ++ tailWord_87509) baseStart_87509 baseEnd_87509 := by
    simpa [prefixWord, tailWord_87509, baseEnd_87509] using wordTrace_append hprefix tailTrace_87509
  have hstable : (prefixWord ++ tailWord_87509).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_87509).length < 2 ^ (prefixWord ++ tailWord_87509).sum := by decide
  have hdescent : baseEnd_87509 < baseStart_87509 := by decide
  rcases family_descends (prefixWord ++ tailWord_87509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_87523 : List Nat := [1, 1, 1, 6, 2, 1, 3, 5]
def baseStart_87523 : Nat := 118140960795 + 87523 * 2 ^ 59
def prefixEnd_87523 : Nat := 4983230072969 + 3 ^ 40 * 87523 * 2
def baseEnd_87523 : Nat := 13315960688464088758517

theorem tailTrace_87523 : CollatzResearch.WordTrace tailWord_87523 prefixEnd_87523 13315960688464088758517 := by
  unfold tailWord_87523
  simp only [CollatzResearch.WordTrace]
  refine ⟨3192226061926593583459223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2128150707951062388972815 3192226061926593583459223)
  ·
    refine ⟨4788339092889890375188835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3192226061926593583459223 4788339092889890375188835)
    ·
      refine ⟨7182508639334835562783253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4788339092889890375188835 7182508639334835562783253)
      ·
        refine ⟨336680092468820417005465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 7182508639334835562783253 336680092468820417005465)
        ·
          refine ⟨252510069351615312754099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 336680092468820417005465 252510069351615312754099)
          ·
            refine ⟨378765104027422969131149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 252510069351615312754099 378765104027422969131149)
            ·
              refine ⟨142036914010283613424181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 378765104027422969131149 142036914010283613424181)
              ·
                refine ⟨13315960688464088758517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 142036914010283613424181 13315960688464088758517)
                ·
                  rfl

theorem cell20_87523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 3, 5].length) (baseStart_87523 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_87523 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_87523 prefixEnd_87523 := by exact prefixLift 87523
  have htrace : WordTrace (prefixWord ++ tailWord_87523) baseStart_87523 baseEnd_87523 := by
    simpa [prefixWord, tailWord_87523, baseEnd_87523] using wordTrace_append hprefix tailTrace_87523
  have hstable : (prefixWord ++ tailWord_87523).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_87523).length < 2 ^ (prefixWord ++ tailWord_87523).sum := by decide
  have hdescent : baseEnd_87523 < baseStart_87523 := by decide
  rcases family_descends (prefixWord ++ tailWord_87523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_87533 : List Nat := [1, 5, 1, 3, 2, 1, 1, 2, 4]
def baseStart_87533 : Nat := 118140960795 + 87533 * 2 ^ 59
def prefixEnd_87533 : Nat := 4983230072969 + 3 ^ 40 * 87533 * 2
def baseEnd_87533 : Nat := 39952446337876675942177

theorem tailTrace_87533 : CollatzResearch.WordTrace tailWord_87533 prefixEnd_87533 39952446337876675942177 := by
  unfold tailWord_87533
  simp only [CollatzResearch.WordTrace]
  refine ⟨3192590791890365291323253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2128393861260243527548835 3192590791890365291323253)
  ·
    refine ⟨299305386739721746061555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3192590791890365291323253 299305386739721746061555)
    ·
      refine ⟨448958080109582619092333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 299305386739721746061555 448958080109582619092333)
      ·
        refine ⟨168359280041093482159625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 448958080109582619092333 168359280041093482159625)
        ·
          refine ⟨126269460030820111619719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 168359280041093482159625 126269460030820111619719)
          ·
            refine ⟨189404190046230167429579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126269460030820111619719 189404190046230167429579)
            ·
              refine ⟨284106285069345251144369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 189404190046230167429579 284106285069345251144369)
              ·
                refine ⟨213079713802008938358277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 284106285069345251144369 213079713802008938358277)
                ·
                  refine ⟨39952446337876675942177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 213079713802008938358277 39952446337876675942177)
                  ·
                    rfl

theorem cell20_87533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 1, 2, 4].length) (baseStart_87533 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_87533 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_87533 prefixEnd_87533 := by exact prefixLift 87533
  have htrace : WordTrace (prefixWord ++ tailWord_87533) baseStart_87533 baseEnd_87533 := by
    simpa [prefixWord, tailWord_87533, baseEnd_87533] using wordTrace_append hprefix tailTrace_87533
  have hstable : (prefixWord ++ tailWord_87533).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_87533).length < 2 ^ (prefixWord ++ tailWord_87533).sum := by decide
  have hdescent : baseEnd_87533 < baseStart_87533 := by decide
  rcases family_descends (prefixWord ++ tailWord_87533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_87537 : List Nat := [1, 2, 2, 2, 3, 2, 1, 1, 6]
def baseStart_87537 : Nat := 118140960795 + 87537 * 2 ^ 59
def prefixEnd_87537 : Nat := 4983230072969 + 3 ^ 40 * 87537 * 2
def baseEnd_87537 : Nat := 39954272046870439808827

theorem tailTrace_87537 : CollatzResearch.WordTrace tailWord_87537 prefixEnd_87537 39954272046870439808827 := by
  unfold tailWord_87537
  simp only [CollatzResearch.WordTrace]
  refine ⟨3192736683875873974468865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2128491122583915982979243 3192736683875873974468865)
  ·
    refine ⟨2394552512906905480851649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3192736683875873974468865 2394552512906905480851649)
    ·
      refine ⟨1795914384680179110638737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2394552512906905480851649 1795914384680179110638737)
      ·
        refine ⟨1346935788510134332979053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1795914384680179110638737 1346935788510134332979053)
        ·
          refine ⟨505100920691300374867145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1346935788510134332979053 505100920691300374867145)
          ·
            refine ⟨378825690518475281150359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 505100920691300374867145 378825690518475281150359)
            ·
              refine ⟨568238535777712921725539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 378825690518475281150359 568238535777712921725539)
              ·
                refine ⟨852357803666569382588309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 568238535777712921725539 852357803666569382588309)
                ·
                  refine ⟨39954272046870439808827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 852357803666569382588309 39954272046870439808827)
                  ·
                    rfl

theorem cell20_87537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 1, 6].length) (baseStart_87537 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_87537 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_87537 prefixEnd_87537 := by exact prefixLift 87537
  have htrace : WordTrace (prefixWord ++ tailWord_87537) baseStart_87537 baseEnd_87537 := by
    simpa [prefixWord, tailWord_87537, baseEnd_87537] using wordTrace_append hprefix tailTrace_87537
  have hstable : (prefixWord ++ tailWord_87537).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_87537).length < 2 ^ (prefixWord ++ tailWord_87537).sum := by decide
  have hdescent : baseEnd_87537 < baseStart_87537 := by decide
  rcases family_descends (prefixWord ++ tailWord_87537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_87564 : List Nat := [2, 2, 1, 2, 5, 2, 1, 2, 3]
def baseStart_87564 : Nat := 118140960795 + 87564 * 2 ^ 59
def prefixEnd_87564 : Nat := 4983230072969 + 3 ^ 40 * 87564 * 2
def baseEnd_87564 : Nat := 39966595582578345908717

theorem tailTrace_87564 : CollatzResearch.WordTrace tailWord_87564 prefixEnd_87564 39966595582578345908717 := by
  unfold tailWord_87564
  simp only [CollatzResearch.WordTrace]
  refine ⟨1596860727389028792850873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2129147636518705057134497 1596860727389028792850873)
  ·
    refine ⟨1197645545541771594638155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1596860727389028792850873 1197645545541771594638155)
    ·
      refine ⟨1796468318312657391957233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1197645545541771594638155 1796468318312657391957233)
      ·
        refine ⟨1347351238734493043967925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1796468318312657391957233 1347351238734493043967925)
        ·
          refine ⟨126314178631358722871993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1347351238734493043967925 126314178631358722871993)
          ·
            refine ⟨94735633973519042153995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 126314178631358722871993 94735633973519042153995)
            ·
              refine ⟨142103450960278563230993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94735633973519042153995 142103450960278563230993)
              ·
                refine ⟨106577588220208922423245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 142103450960278563230993 106577588220208922423245)
                ·
                  refine ⟨39966595582578345908717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 106577588220208922423245 39966595582578345908717)
                  ·
                    rfl

theorem cell20_87564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 2, 1, 2, 3].length) (baseStart_87564 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_87564 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_87564 prefixEnd_87564 := by exact prefixLift 87564
  have htrace : WordTrace (prefixWord ++ tailWord_87564) baseStart_87564 baseEnd_87564 := by
    simpa [prefixWord, tailWord_87564, baseEnd_87564] using wordTrace_append hprefix tailTrace_87564
  have hstable : (prefixWord ++ tailWord_87564).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_87564).length < 2 ^ (prefixWord ++ tailWord_87564).sum := by decide
  have hdescent : baseEnd_87564 < baseStart_87564 := by decide
  rcases family_descends (prefixWord ++ tailWord_87564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_87609 : List Nat := [1, 2, 1, 5, 1, 2, 3, 3, 2]
def baseStart_87609 : Nat := 118140960795 + 87609 * 2 ^ 59
def prefixEnd_87609 : Nat := 4983230072969 + 3 ^ 40 * 87609 * 2
def baseEnd_87609 : Nat := 39987134808758189408533

theorem tailTrace_87609 : CollatzResearch.WordTrace tailWord_87609 prefixEnd_87609 39987134808758189408533 := by
  unfold tailWord_87609
  simp only [CollatzResearch.WordTrace]
  refine ⟨3195362739615030271089881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2130241826410020180726587 3195362739615030271089881)
  ·
    refine ⟨2396522054711272703317411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3195362739615030271089881 2396522054711272703317411)
    ·
      refine ⟨3594783082066909054976117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2396522054711272703317411 3594783082066909054976117)
      ·
        refine ⟨337010913943772723904011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3594783082066909054976117 337010913943772723904011)
        ·
          refine ⟨505516370915659085856017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 337010913943772723904011 505516370915659085856017)
          ·
            refine ⟨379137278186744314392013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 505516370915659085856017 379137278186744314392013)
            ·
              refine ⟨142176479320029117897005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 379137278186744314392013 142176479320029117897005)
              ·
                refine ⟨53316179745010919211377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 142176479320029117897005 53316179745010919211377)
                ·
                  refine ⟨39987134808758189408533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53316179745010919211377 39987134808758189408533)
                  ·
                    rfl

theorem cell20_87609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 3, 3, 2].length) (baseStart_87609 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_87609 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_87609 prefixEnd_87609 := by exact prefixLift 87609
  have htrace : WordTrace (prefixWord ++ tailWord_87609) baseStart_87609 baseEnd_87609 := by
    simpa [prefixWord, tailWord_87609, baseEnd_87609] using wordTrace_append hprefix tailTrace_87609
  have hstable : (prefixWord ++ tailWord_87609).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_87609).length < 2 ^ (prefixWord ++ tailWord_87609).sum := by decide
  have hdescent : baseEnd_87609 < baseStart_87609 := by decide
  rcases family_descends (prefixWord ++ tailWord_87609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_87622 : List Nat := [6, 1, 1, 1, 3, 1, 3, 2, 2]
def baseStart_87622 : Nat := 118140960795 + 87622 * 2 ^ 59
def prefixEnd_87622 : Nat := 4983230072969 + 3 ^ 40 * 87622 * 2
def baseEnd_87622 : Nat := 39993068362987921975147

theorem tailTrace_87622 : CollatzResearch.WordTrace tailWord_87622 prefixEnd_87622 39993068362987921975147 := by
  unfold tailWord_87622
  simp only [CollatzResearch.WordTrace]
  refine ⟨99869902767747921603535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 2130557925711955660875413 99869902767747921603535)
  ·
    refine ⟨149804854151621882405303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99869902767747921603535 149804854151621882405303)
    ·
      refine ⟨224707281227432823607955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149804854151621882405303 224707281227432823607955)
      ·
        refine ⟨337060921841149235411933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 224707281227432823607955 337060921841149235411933)
        ·
          refine ⟨126397845690430963279475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 337060921841149235411933 126397845690430963279475)
          ·
            refine ⟨189596768535646444919213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126397845690430963279475 189596768535646444919213)
            ·
              refine ⟨71098788200867416844705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 189596768535646444919213 71098788200867416844705)
              ·
                refine ⟨53324091150650562633529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 71098788200867416844705 53324091150650562633529)
                ·
                  refine ⟨39993068362987921975147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53324091150650562633529 39993068362987921975147)
                  ·
                    rfl

theorem cell20_87622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 3, 2, 2].length) (baseStart_87622 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_87622 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_87622 prefixEnd_87622 := by exact prefixLift 87622
  have htrace : WordTrace (prefixWord ++ tailWord_87622) baseStart_87622 baseEnd_87622 := by
    simpa [prefixWord, tailWord_87622, baseEnd_87622] using wordTrace_append hprefix tailTrace_87622
  have hstable : (prefixWord ++ tailWord_87622).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_87622).length < 2 ^ (prefixWord ++ tailWord_87622).sum := by decide
  have hdescent : baseEnd_87622 < baseStart_87622 := by decide
  rcases family_descends (prefixWord ++ tailWord_87622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_87665 : List Nat := [1, 2, 2, 2, 1, 1, 1, 3, 7]
def baseStart_87665 : Nat := 118140960795 + 87665 * 2 ^ 59
def prefixEnd_87665 : Nat := 4983230072969 + 3 ^ 40 * 87665 * 2
def baseEnd_87665 : Nat := 40012694734670883541637

theorem tailTrace_87665 : CollatzResearch.WordTrace tailWord_87665 prefixEnd_87665 40012694734670883541637 := by
  unfold tailWord_87665
  simp only [CollatzResearch.WordTrace]
  refine ⟨3197405227412151835128449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2131603484941434556752299 3197405227412151835128449)
  ·
    refine ⟨2398053920559113876346337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3197405227412151835128449 2398053920559113876346337)
    ·
      refine ⟨1798540440419335407259753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2398053920559113876346337 1798540440419335407259753)
      ·
        refine ⟨1348905330314501555444815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1798540440419335407259753 1348905330314501555444815)
        ·
          refine ⟨2023357995471752333167223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1348905330314501555444815 2023357995471752333167223)
          ·
            refine ⟨3035036993207628499750835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2023357995471752333167223 3035036993207628499750835)
            ·
              refine ⟨4552555489811442749626253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3035036993207628499750835 4552555489811442749626253)
              ·
                refine ⟨1707208308679291031109845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4552555489811442749626253 1707208308679291031109845)
                ·
                  refine ⟨40012694734670883541637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1707208308679291031109845 40012694734670883541637)
                  ·
                    rfl

theorem cell20_87665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 3, 7].length) (baseStart_87665 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_87665 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_87665 prefixEnd_87665 := by exact prefixLift 87665
  have htrace : WordTrace (prefixWord ++ tailWord_87665) baseStart_87665 baseEnd_87665 := by
    simpa [prefixWord, tailWord_87665, baseEnd_87665] using wordTrace_append hprefix tailTrace_87665
  have hstable : (prefixWord ++ tailWord_87665).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_87665).length < 2 ^ (prefixWord ++ tailWord_87665).sum := by decide
  have hdescent : baseEnd_87665 < baseStart_87665 := by decide
  rcases family_descends (prefixWord ++ tailWord_87665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_87733 : List Nat := [1, 3, 3, 3, 3, 1, 1, 2, 3]
def baseStart_87733 : Nat := 118140960795 + 87733 * 2 ^ 59
def prefixEnd_87733 : Nat := 4983230072969 + 3 ^ 40 * 87733 * 2
def baseEnd_87733 : Nat := 40043731787564869274693

theorem tailTrace_87733 : CollatzResearch.WordTrace tailWord_87733 prefixEnd_87733 40043731787564869274693 := by
  unfold tailWord_87733
  simp only [CollatzResearch.WordTrace]
  refine ⟨3199885391165799448603853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2133256927443866299069235 3199885391165799448603853)
  ·
    refine ⟨1199957021687174793226445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3199885391165799448603853 1199957021687174793226445)
    ·
      refine ⟨449983883132690547459917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1199957021687174793226445 449983883132690547459917)
      ·
        refine ⟨168743956174758955297469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 449983883132690547459917 168743956174758955297469)
        ·
          refine ⟨63278983565534608236551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 168743956174758955297469 63278983565534608236551)
          ·
            refine ⟨94918475348301912354827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63278983565534608236551 94918475348301912354827)
            ·
              refine ⟨142377713022452868532241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94918475348301912354827 142377713022452868532241)
              ·
                refine ⟨106783284766839651399181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 142377713022452868532241 106783284766839651399181)
                ·
                  refine ⟨40043731787564869274693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 106783284766839651399181 40043731787564869274693)
                  ·
                    rfl

theorem cell20_87733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 1, 1, 2, 3].length) (baseStart_87733 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_87733 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_87733 prefixEnd_87733 := by exact prefixLift 87733
  have htrace : WordTrace (prefixWord ++ tailWord_87733) baseStart_87733 baseEnd_87733 := by
    simpa [prefixWord, tailWord_87733, baseEnd_87733] using wordTrace_append hprefix tailTrace_87733
  have hstable : (prefixWord ++ tailWord_87733).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_87733).length < 2 ^ (prefixWord ++ tailWord_87733).sum := by decide
  have hdescent : baseEnd_87733 < baseStart_87733 := by decide
  rcases family_descends (prefixWord ++ tailWord_87733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_87744 : List Nat := [2, 1, 1, 2, 4, 1, 1, 6, 2]
def baseStart_87744 : Nat := 118140960795 + 87744 * 2 ^ 59
def prefixEnd_87744 : Nat := 4983230072969 + 3 ^ 40 * 87744 * 2
def baseEnd_87744 : Nat := 40048752487297719907981

theorem tailTrace_87744 : CollatzResearch.WordTrace tailWord_87744 prefixEnd_87744 40048752487297719907981 := by
  unfold tailWord_87744
  simp only [CollatzResearch.WordTrace]
  refine ⟨1600143297062974163627143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2133524396083965551502857 1600143297062974163627143)
  ·
    refine ⟨2400214945594461245440715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1600143297062974163627143 2400214945594461245440715)
    ·
      refine ⟨3600322418391691868161073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2400214945594461245440715 3600322418391691868161073)
      ·
        refine ⟨2700241813793768901120805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3600322418391691868161073 2700241813793768901120805)
        ·
          refine ⟨506295340086331668960151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2700241813793768901120805 506295340086331668960151)
          ·
            refine ⟨759443010129497503440227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 506295340086331668960151 759443010129497503440227)
            ·
              refine ⟨1139164515194246255160341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 759443010129497503440227 1139164515194246255160341)
              ·
                refine ⟨53398336649730293210641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1139164515194246255160341 53398336649730293210641)
                ·
                  refine ⟨40048752487297719907981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53398336649730293210641 40048752487297719907981)
                  ·
                    rfl

theorem cell20_87744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 6, 2].length) (baseStart_87744 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_87744 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_87744 prefixEnd_87744 := by exact prefixLift 87744
  have htrace : WordTrace (prefixWord ++ tailWord_87744) baseStart_87744 baseEnd_87744 := by
    simpa [prefixWord, tailWord_87744, baseEnd_87744] using wordTrace_append hprefix tailTrace_87744
  have hstable : (prefixWord ++ tailWord_87744).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_87744).length < 2 ^ (prefixWord ++ tailWord_87744).sum := by decide
  have hdescent : baseEnd_87744 < baseStart_87744 := by decide
  rcases family_descends (prefixWord ++ tailWord_87744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_87750 : List Nat := [6, 1, 2, 1, 1, 2, 3, 1, 3]
def baseStart_87750 : Nat := 118140960795 + 87750 * 2 ^ 59
def prefixEnd_87750 : Nat := 4983230072969 + 3 ^ 40 * 87750 * 2
def baseEnd_87750 : Nat := 40051491050788365707957

theorem tailTrace_87750 : CollatzResearch.WordTrace tailWord_87750 prefixEnd_87750 40051491050788365707957 := by
  unfold tailWord_87750
  simp only [CollatzResearch.WordTrace]
  refine ⟨100015794753256604749147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 2133670288069474234648469 100015794753256604749147)
  ·
    refine ⟨150023692129884907123721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100015794753256604749147 150023692129884907123721)
    ·
      refine ⟨112517769097413680342791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150023692129884907123721 112517769097413680342791)
      ·
        refine ⟨168776653646120520514187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112517769097413680342791 168776653646120520514187)
        ·
          refine ⟨253164980469180780771281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 168776653646120520514187 253164980469180780771281)
          ·
            refine ⟨189873735351885585578461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 253164980469180780771281 189873735351885585578461)
            ·
              refine ⟨71202650756957094591923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 189873735351885585578461 71202650756957094591923)
              ·
                refine ⟨106803976135435641887885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71202650756957094591923 106803976135435641887885)
                ·
                  refine ⟨40051491050788365707957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 106803976135435641887885 40051491050788365707957)
                  ·
                    rfl

theorem cell20_87750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 3, 1, 3].length) (baseStart_87750 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_87750 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_87750 prefixEnd_87750 := by exact prefixLift 87750
  have htrace : WordTrace (prefixWord ++ tailWord_87750) baseStart_87750 baseEnd_87750 := by
    simpa [prefixWord, tailWord_87750, baseEnd_87750] using wordTrace_append hprefix tailTrace_87750
  have hstable : (prefixWord ++ tailWord_87750).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_87750).length < 2 ^ (prefixWord ++ tailWord_87750).sum := by decide
  have hdescent : baseEnd_87750 < baseStart_87750 := by decide
  rcases family_descends (prefixWord ++ tailWord_87750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_87754 : List Nat := [3, 1, 2, 1, 5, 1, 3, 1, 3]
def baseStart_87754 : Nat := 118140960795 + 87754 * 2 ^ 59
def prefixEnd_87754 : Nat := 4983230072969 + 3 ^ 40 * 87754 * 2
def baseEnd_87754 : Nat := 40053316759782129574607

theorem tailTrace_87754 : CollatzResearch.WordTrace tailWord_87754 prefixEnd_87754 40053316759782129574607 := by
  unfold tailWord_87754
  simp only [CollatzResearch.WordTrace]
  refine ⟨800162831022430008779579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2133767549393146690078877 800162831022430008779579)
  ·
    refine ⟨1200244246533645013169369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 800162831022430008779579 1200244246533645013169369)
    ·
      refine ⟨900183184900233759877027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1200244246533645013169369 900183184900233759877027)
      ·
        refine ⟨1350274777350350639815541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 900183184900233759877027 1350274777350350639815541)
        ·
          refine ⟨126588260376595372482707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1350274777350350639815541 126588260376595372482707)
          ·
            refine ⟨189882390564893058724061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126588260376595372482707 189882390564893058724061)
            ·
              refine ⟨71205896461834897021523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 189882390564893058724061 71205896461834897021523)
              ·
                refine ⟨106808844692752345532285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71205896461834897021523 106808844692752345532285)
                ·
                  refine ⟨40053316759782129574607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 106808844692752345532285 40053316759782129574607)
                  ·
                    rfl

theorem cell20_87754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 3, 1, 3].length) (baseStart_87754 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_87754 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_87754 prefixEnd_87754 := by exact prefixLift 87754
  have htrace : WordTrace (prefixWord ++ tailWord_87754) baseStart_87754 baseEnd_87754 := by
    simpa [prefixWord, tailWord_87754, baseEnd_87754] using wordTrace_append hprefix tailTrace_87754
  have hstable : (prefixWord ++ tailWord_87754).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_87754).length < 2 ^ (prefixWord ++ tailWord_87754).sum := by decide
  have hdescent : baseEnd_87754 < baseStart_87754 := by decide
  rcases family_descends (prefixWord ++ tailWord_87754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_87789 : List Nat := [1, 5, 1, 2, 1, 4, 6]
def baseStart_87789 : Nat := 118140960795 + 87789 * 2 ^ 59
def prefixEnd_87789 : Nat := 4983230072969 + 3 ^ 40 * 87789 * 2
def baseEnd_87789 : Nat := 4452143523719729267533

theorem tailTrace_87789 : CollatzResearch.WordTrace tailWord_87789 prefixEnd_87789 4452143523719729267533 := by
  unfold tailWord_87789
  simp only [CollatzResearch.WordTrace]
  refine ⟨3201927878962921012642421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2134618585975280675094947 3201927878962921012642421)
  ·
    refine ⟨300180738652773844935227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3201927878962921012642421 300180738652773844935227)
    ·
      refine ⟨450271107979160767402841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 300180738652773844935227 450271107979160767402841)
      ·
        refine ⟨337703330984370575552131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 450271107979160767402841 337703330984370575552131)
        ·
          refine ⟨506554996476555863328197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 337703330984370575552131 506554996476555863328197)
          ·
            refine ⟨94979061839354224374037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 506554996476555863328197 94979061839354224374037)
            ·
              refine ⟨4452143523719729267533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 94979061839354224374037 4452143523719729267533)
              ·
                rfl

theorem cell20_87789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 4, 6].length) (baseStart_87789 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_87789 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_87789 prefixEnd_87789 := by exact prefixLift 87789
  have htrace : WordTrace (prefixWord ++ tailWord_87789) baseStart_87789 baseEnd_87789 := by
    simpa [prefixWord, tailWord_87789, baseEnd_87789] using wordTrace_append hprefix tailTrace_87789
  have hstable : (prefixWord ++ tailWord_87789).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_87789).length < 2 ^ (prefixWord ++ tailWord_87789).sum := by decide
  have hdescent : baseEnd_87789 < baseStart_87789 := by decide
  rcases family_descends (prefixWord ++ tailWord_87789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_87806 : List Nat := [4, 2, 2, 1, 3, 1, 2, 5]
def baseStart_87806 : Nat := 118140960795 + 87806 * 2 ^ 59
def prefixEnd_87806 : Nat := 4983230072969 + 3 ^ 40 * 87806 * 2
def baseEnd_87806 : Nat := 13359016992233686613687

theorem tailTrace_87806 : CollatzResearch.WordTrace tailWord_87806 prefixEnd_87806 13359016992233686613687 := by
  unfold tailWord_87806
  simp only [CollatzResearch.WordTrace]
  refine ⟨400318489987666614501409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2135031946600888610674181 400318489987666614501409)
  ·
    refine ⟨300238867490749960876057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 400318489987666614501409 300238867490749960876057)
    ·
      refine ⟨225179150618062470657043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 300238867490749960876057 225179150618062470657043)
      ·
        refine ⟨337768725927093705985565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 225179150618062470657043 337768725927093705985565)
        ·
          refine ⟨126663272222660139744587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 337768725927093705985565 126663272222660139744587)
          ·
            refine ⟨189994908333990209616881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126663272222660139744587 189994908333990209616881)
            ·
              refine ⟨142496181250492657212661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 189994908333990209616881 142496181250492657212661)
              ·
                refine ⟨13359016992233686613687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 142496181250492657212661 13359016992233686613687)
                ·
                  rfl

theorem cell20_87806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 2, 5].length) (baseStart_87806 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_87806 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_87806 prefixEnd_87806 := by exact prefixLift 87806
  have htrace : WordTrace (prefixWord ++ tailWord_87806) baseStart_87806 baseEnd_87806 := by
    simpa [prefixWord, tailWord_87806, baseEnd_87806] using wordTrace_append hprefix tailTrace_87806
  have hstable : (prefixWord ++ tailWord_87806).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_87806).length < 2 ^ (prefixWord ++ tailWord_87806).sum := by decide
  have hdescent : baseEnd_87806 < baseStart_87806 := by decide
  rcases family_descends (prefixWord ++ tailWord_87806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_87848 : List Nat := [2, 1, 5, 1, 1, 10]
def baseStart_87848 : Nat := 118140960795 + 87848 * 2 ^ 59
def prefixEnd_87848 : Nat := 4983230072969 + 3 ^ 40 * 87848 * 2
def baseEnd_87848 : Nat := 1485045219301317794107

theorem tailTrace_87848 : CollatzResearch.WordTrace tailWord_87848 prefixEnd_87848 1485045219301317794107 := by
  unfold tailWord_87848
  simp only [CollatzResearch.WordTrace]
  refine ⟨1602039892874587044520099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2136053190499449392693465 1602039892874587044520099)
  ·
    refine ⟨2403059839311880566780149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1602039892874587044520099 2403059839311880566780149)
    ·
      refine ⟨225286859935488803135639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2403059839311880566780149 225286859935488803135639)
      ·
        refine ⟨337930289903233204703459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 225286859935488803135639 337930289903233204703459)
        ·
          refine ⟨506895434854849807055189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 337930289903233204703459 506895434854849807055189)
          ·
            refine ⟨1485045219301317794107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 506895434854849807055189 1485045219301317794107)
            ·
              rfl

theorem cell20_87848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 10].length) (baseStart_87848 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_87848 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_87848 prefixEnd_87848 := by exact prefixLift 87848
  have htrace : WordTrace (prefixWord ++ tailWord_87848) baseStart_87848 baseEnd_87848 := by
    simpa [prefixWord, tailWord_87848, baseEnd_87848] using wordTrace_append hprefix tailTrace_87848
  have hstable : (prefixWord ++ tailWord_87848).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_87848).length < 2 ^ (prefixWord ++ tailWord_87848).sum := by decide
  have hdescent : baseEnd_87848 < baseStart_87848 := by decide
  rcases family_descends (prefixWord ++ tailWord_87848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_87854 : List Nat := [4, 1, 3, 2, 2, 1, 1, 4, 2]
def baseStart_87854 : Nat := 118140960795 + 87854 * 2 ^ 59
def prefixEnd_87854 : Nat := 4983230072969 + 3 ^ 40 * 87854 * 2
def baseEnd_87854 : Nat := 40098959484626226240865

theorem tailTrace_87854 : CollatzResearch.WordTrace tailWord_87854 prefixEnd_87854 40098959484626226240865 := by
  unfold tailWord_87854
  simp only [CollatzResearch.WordTrace]
  refine ⟨400537327965929639219827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2136199082484958075839077 400537327965929639219827)
  ·
    refine ⟨600805991948894458829741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 400537327965929639219827 600805991948894458829741)
    ·
      refine ⟨225302246980835422061153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 600805991948894458829741 225302246980835422061153)
      ·
        refine ⟨168976685235626566545865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 225302246980835422061153 168976685235626566545865)
        ·
          refine ⟨126732513926719924909399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 168976685235626566545865 126732513926719924909399)
          ·
            refine ⟨190098770890079887364099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126732513926719924909399 190098770890079887364099)
            ·
              refine ⟨285148156335119831046149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 190098770890079887364099 285148156335119831046149)
              ·
                refine ⟨53465279312834968321153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 285148156335119831046149 53465279312834968321153)
                ·
                  refine ⟨40098959484626226240865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53465279312834968321153 40098959484626226240865)
                  ·
                    rfl

theorem cell20_87854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 1, 4, 2].length) (baseStart_87854 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_87854 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_87854 prefixEnd_87854 := by exact prefixLift 87854
  have htrace : WordTrace (prefixWord ++ tailWord_87854) baseStart_87854 baseEnd_87854 := by
    simpa [prefixWord, tailWord_87854, baseEnd_87854] using wordTrace_append hprefix tailTrace_87854
  have hstable : (prefixWord ++ tailWord_87854).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_87854).length < 2 ^ (prefixWord ++ tailWord_87854).sum := by decide
  have hdescent : baseEnd_87854 < baseStart_87854 := by decide
  rcases family_descends (prefixWord ++ tailWord_87854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_87906 : List Nat := [3, 3, 2, 1, 2, 3, 1, 2, 3]
def baseStart_87906 : Nat := 118140960795 + 87906 * 2 ^ 59
def prefixEnd_87906 : Nat := 4983230072969 + 3 ^ 40 * 87906 * 2
def baseEnd_87906 : Nat := 40122693701545156507319

theorem tailTrace_87906 : CollatzResearch.WordTrace tailWord_87906 prefixEnd_87906 40122693701545156507319 := by
  unfold tailWord_87906
  simp only [CollatzResearch.WordTrace]
  refine ⟨801548804884762498662893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2137463479692699996434381 801548804884762498662893)
  ·
    refine ⟨300580801831785936998585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 801548804884762498662893 300580801831785936998585)
    ·
      refine ⟨225435601373839452748939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 300580801831785936998585 225435601373839452748939)
      ·
        refine ⟨338153402060759179123409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 225435601373839452748939 338153402060759179123409)
        ·
          refine ⟨253615051545569384342557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 338153402060759179123409 253615051545569384342557)
          ·
            refine ⟨95105644329588519128459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 253615051545569384342557 95105644329588519128459)
            ·
              refine ⟨142658466494382778692689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95105644329588519128459 142658466494382778692689)
              ·
                refine ⟨106993849870787084019517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 142658466494382778692689 106993849870787084019517)
                ·
                  refine ⟨40122693701545156507319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 106993849870787084019517 40122693701545156507319)
                  ·
                    rfl

theorem cell20_87906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 3, 1, 2, 3].length) (baseStart_87906 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_87906 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_87906 prefixEnd_87906 := by exact prefixLift 87906
  have htrace : WordTrace (prefixWord ++ tailWord_87906) baseStart_87906 baseEnd_87906 := by
    simpa [prefixWord, tailWord_87906, baseEnd_87906] using wordTrace_append hprefix tailTrace_87906
  have hstable : (prefixWord ++ tailWord_87906).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_87906).length < 2 ^ (prefixWord ++ tailWord_87906).sum := by decide
  have hdescent : baseEnd_87906 < baseStart_87906 := by decide
  rcases family_descends (prefixWord ++ tailWord_87906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_87917 : List Nat := [1, 5, 1, 1, 1, 1, 3, 3, 4]
def baseStart_87917 : Nat := 118140960795 + 87917 * 2 ^ 59
def prefixEnd_87917 : Nat := 4983230072969 + 3 ^ 40 * 87917 * 2
def baseEnd_87917 : Nat := 40127714401278007140607

theorem tailTrace_87917 : CollatzResearch.WordTrace tailWord_87917 prefixEnd_87917 40127714401278007140607 := by
  unfold tailWord_87917
  simp only [CollatzResearch.WordTrace]
  refine ⟨3206596422499198873302005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2137730948332799248868003 3206596422499198873302005)
  ·
    refine ⟨300618414609299894372063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3206596422499198873302005 300618414609299894372063)
    ·
      refine ⟨450927621913949841558095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 300618414609299894372063 450927621913949841558095)
      ·
        refine ⟨676391432870924762337143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 450927621913949841558095 676391432870924762337143)
        ·
          refine ⟨1014587149306387143505715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 676391432870924762337143 1014587149306387143505715)
          ·
            refine ⟨1521880723959580715258573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1014587149306387143505715 1521880723959580715258573)
            ·
              refine ⟨570705271484842768221965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1521880723959580715258573 570705271484842768221965)
              ·
                refine ⟨214014476806816038083237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 570705271484842768221965 214014476806816038083237)
                ·
                  refine ⟨40127714401278007140607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 214014476806816038083237 40127714401278007140607)
                  ·
                    rfl

theorem cell20_87917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 3, 4].length) (baseStart_87917 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_87917 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_87917 prefixEnd_87917 := by exact prefixLift 87917
  have htrace : WordTrace (prefixWord ++ tailWord_87917) baseStart_87917 baseEnd_87917 := by
    simpa [prefixWord, tailWord_87917, baseEnd_87917] using wordTrace_append hprefix tailTrace_87917
  have hstable : (prefixWord ++ tailWord_87917).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_87917).length < 2 ^ (prefixWord ++ tailWord_87917).sum := by decide
  have hdescent : baseEnd_87917 < baseStart_87917 := by decide
  rcases family_descends (prefixWord ++ tailWord_87917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_87937 : List Nat := [1, 2, 4, 4, 1, 2, 2, 4]
def baseStart_87937 : Nat := 118140960795 + 87937 * 2 ^ 59
def prefixEnd_87937 : Nat := 4983230072969 + 3 ^ 40 * 87937 * 2
def baseEnd_87937 : Nat := 13378947648748942157953

theorem tailTrace_87937 : CollatzResearch.WordTrace tailWord_87937 prefixEnd_87937 13378947648748942157953 := by
  unfold tailWord_87937
  simp only [CollatzResearch.WordTrace]
  refine ⟨3207325882426742289030065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2138217254951161526020043 3207325882426742289030065)
  ·
    refine ⟨2405494411820056716772549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3207325882426742289030065 2405494411820056716772549)
    ·
      refine ⟨451030202216260634394853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2405494411820056716772549 451030202216260634394853)
      ·
        refine ⟨84568162915548868949035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 451030202216260634394853 84568162915548868949035)
        ·
          refine ⟨126852244373323303423553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84568162915548868949035 126852244373323303423553)
          ·
            refine ⟨95139183279992477567665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 126852244373323303423553 95139183279992477567665)
            ·
              refine ⟨71354387459994358175749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 95139183279992477567665 71354387459994358175749)
              ·
                refine ⟨13378947648748942157953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 71354387459994358175749 13378947648748942157953)
                ·
                  rfl

theorem cell20_87937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 2, 2, 4].length) (baseStart_87937 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_87937 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_87937 prefixEnd_87937 := by exact prefixLift 87937
  have htrace : WordTrace (prefixWord ++ tailWord_87937) baseStart_87937 baseEnd_87937 := by
    simpa [prefixWord, tailWord_87937, baseEnd_87937] using wordTrace_append hprefix tailTrace_87937
  have hstable : (prefixWord ++ tailWord_87937).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_87937).length < 2 ^ (prefixWord ++ tailWord_87937).sum := by decide
  have hdescent : baseEnd_87937 < baseStart_87937 := by decide
  rcases family_descends (prefixWord ++ tailWord_87937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_87962 : List Nat := [3, 1, 1, 4, 2, 1, 8]
def baseStart_87962 : Nat := 118140960795 + 87962 * 2 ^ 59
def prefixEnd_87962 : Nat := 4983230072969 + 3 ^ 40 * 87962 * 2
def baseEnd_87962 : Nat := 4460917069717538960047

theorem tailTrace_87962 : CollatzResearch.WordTrace tailWord_87962 prefixEnd_87962 4460917069717538960047 := by
  unfold tailWord_87962
  simp only [CollatzResearch.WordTrace]
  refine ⟨802059426834042889672535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2138825138224114372460093 802059426834042889672535)
  ·
    refine ⟨1203089140251064334508803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 802059426834042889672535 1203089140251064334508803)
    ·
      refine ⟨1804633710376596501763205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1203089140251064334508803 1804633710376596501763205)
      ·
        refine ⟨338368820695611844080601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1804633710376596501763205 338368820695611844080601)
        ·
          refine ⟨253776615521708883060451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 338368820695611844080601 253776615521708883060451)
          ·
            refine ⟨380664923282563324590677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 253776615521708883060451 380664923282563324590677)
            ·
              refine ⟨4460917069717538960047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 380664923282563324590677 4460917069717538960047)
              ·
                rfl

theorem cell20_87962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 8].length) (baseStart_87962 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_87962 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_87962 prefixEnd_87962 := by exact prefixLift 87962
  have htrace : WordTrace (prefixWord ++ tailWord_87962) baseStart_87962 baseEnd_87962 := by
    simpa [prefixWord, tailWord_87962, baseEnd_87962] using wordTrace_append hprefix tailTrace_87962
  have hstable : (prefixWord ++ tailWord_87962).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_87962).length < 2 ^ (prefixWord ++ tailWord_87962).sum := by decide
  have hdescent : baseEnd_87962 < baseStart_87962 := by decide
  rcases family_descends (prefixWord ++ tailWord_87962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_87972 : List Nat := [2, 3, 1, 2, 1, 5, 1, 1, 4]
def baseStart_87972 : Nat := 118140960795 + 87972 * 2 ^ 59
def prefixEnd_87972 : Nat := 4983230072969 + 3 ^ 40 * 87972 * 2
def baseEnd_87972 : Nat := 40152817899942260307049

theorem tailTrace_87972 : CollatzResearch.WordTrace tailWord_87972 prefixEnd_87972 40152817899942260307049 := by
  unfold tailWord_87972
  simp only [CollatzResearch.WordTrace]
  refine ⟨1604301218649971633277085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2139068291533295511036113 1604301218649971633277085)
  ·
    refine ⟨601612956993739362478907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1604301218649971633277085 601612956993739362478907)
    ·
      refine ⟨902419435490609043718361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 601612956993739362478907 902419435490609043718361)
      ·
        refine ⟨676814576617956782788771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 902419435490609043718361 676814576617956782788771)
        ·
          refine ⟨1015221864926935174183157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 676814576617956782788771 1015221864926935174183157)
          ·
            refine ⟨95177049836900172579671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1015221864926935174183157 95177049836900172579671)
            ·
              refine ⟨142765574755350258869507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95177049836900172579671 142765574755350258869507)
              ·
                refine ⟨214148362133025388304261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 142765574755350258869507 214148362133025388304261)
                ·
                  refine ⟨40152817899942260307049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 214148362133025388304261 40152817899942260307049)
                  ·
                    rfl

theorem cell20_87972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 5, 1, 1, 4].length) (baseStart_87972 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_87972 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_87972 prefixEnd_87972 := by exact prefixLift 87972
  have htrace : WordTrace (prefixWord ++ tailWord_87972) baseStart_87972 baseEnd_87972 := by
    simpa [prefixWord, tailWord_87972, baseEnd_87972] using wordTrace_append hprefix tailTrace_87972
  have hstable : (prefixWord ++ tailWord_87972).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_87972).length < 2 ^ (prefixWord ++ tailWord_87972).sum := by decide
  have hdescent : baseEnd_87972 < baseStart_87972 := by decide
  rcases family_descends (prefixWord ++ tailWord_87972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_88024 : List Nat := [2, 1, 2, 2, 2, 2, 4, 2, 3]
def baseStart_88024 : Nat := 118140960795 + 88024 * 2 ^ 59
def prefixEnd_88024 : Nat := 4983230072969 + 3 ^ 40 * 88024 * 2
def baseEnd_88024 : Nat := 40176552116861190573503

theorem tailTrace_88024 : CollatzResearch.WordTrace tailWord_88024 prefixEnd_88024 40176552116861190573503 := by
  unfold tailWord_88024
  simp only [CollatzResearch.WordTrace]
  refine ⟨1605249516555778073723563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2140332688741037431631417 1605249516555778073723563)
  ·
    refine ⟨2407874274833667110585345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1605249516555778073723563 2407874274833667110585345)
    ·
      refine ⟨1805905706125250332939009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2407874274833667110585345 1805905706125250332939009)
      ·
        refine ⟨1354429279593937749704257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1805905706125250332939009 1354429279593937749704257)
        ·
          refine ⟨1015821959695453312278193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1354429279593937749704257 1015821959695453312278193)
          ·
            refine ⟨761866469771589984208645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1015821959695453312278193 761866469771589984208645)
            ·
              refine ⟨142849963082173122039121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 761866469771589984208645 142849963082173122039121)
              ·
                refine ⟨107137472311629841529341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 142849963082173122039121 107137472311629841529341)
                ·
                  refine ⟨40176552116861190573503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 107137472311629841529341 40176552116861190573503)
                  ·
                    rfl

theorem cell20_88024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 4, 2, 3].length) (baseStart_88024 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_88024 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_88024 prefixEnd_88024 := by exact prefixLift 88024
  have htrace : WordTrace (prefixWord ++ tailWord_88024) baseStart_88024 baseEnd_88024 := by
    simpa [prefixWord, tailWord_88024, baseEnd_88024] using wordTrace_append hprefix tailTrace_88024
  have hstable : (prefixWord ++ tailWord_88024).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_88024).length < 2 ^ (prefixWord ++ tailWord_88024).sum := by decide
  have hdescent : baseEnd_88024 < baseStart_88024 := by decide
  rcases family_descends (prefixWord ++ tailWord_88024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_88059 : List Nat := [1, 1, 1, 1, 1, 3, 4, 8]
def baseStart_88059 : Nat := 118140960795 + 88059 * 2 ^ 59
def prefixEnd_88059 : Nat := 4983230072969 + 3 ^ 40 * 88059 * 2
def baseEnd_88059 : Nat := 13397509023518874802231

theorem tailTrace_88059 : CollatzResearch.WordTrace tailWord_88059 prefixEnd_88059 13397509023518874802231 := by
  unfold tailWord_88059
  simp only [CollatzResearch.WordTrace]
  refine ⟨3211775587984757124971231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2141183725323171416647487 3211775587984757124971231)
  ·
    refine ⟨4817663381977135687456847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3211775587984757124971231 4817663381977135687456847)
    ·
      refine ⟨7226495072965703531185271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4817663381977135687456847 7226495072965703531185271)
      ·
        refine ⟨10839742609448555296777907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7226495072965703531185271 10839742609448555296777907)
        ·
          refine ⟨16259613914172832945166861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10839742609448555296777907 16259613914172832945166861)
          ·
            refine ⟨6097355217814812354437573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16259613914172832945166861 6097355217814812354437573)
            ·
              refine ⟨1143254103340277316457045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6097355217814812354437573 1143254103340277316457045)
              ·
                refine ⟨13397509023518874802231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1143254103340277316457045 13397509023518874802231)
                ·
                  rfl

theorem cell20_88059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 8].length) (baseStart_88059 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_88059 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_88059 prefixEnd_88059 := by exact prefixLift 88059
  have htrace : WordTrace (prefixWord ++ tailWord_88059) baseStart_88059 baseEnd_88059 := by
    simpa [prefixWord, tailWord_88059, baseEnd_88059] using wordTrace_append hprefix tailTrace_88059
  have hstable : (prefixWord ++ tailWord_88059).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_88059).length < 2 ^ (prefixWord ++ tailWord_88059).sum := by decide
  have hdescent : baseEnd_88059 < baseStart_88059 := by decide
  rcases family_descends (prefixWord ++ tailWord_88059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_88110 : List Nat := [4, 1, 3, 1, 1, 4, 2, 4]
def baseStart_88110 : Nat := 118140960795 + 88110 * 2 ^ 59
def prefixEnd_88110 : Nat := 4983230072969 + 3 ^ 40 * 88110 * 2
def baseEnd_88110 : Nat := 13405268286742371235495

theorem tailTrace_88110 : CollatzResearch.WordTrace tailWord_88110 prefixEnd_88110 13405268286742371235495 := by
  unfold tailWord_88110
  simp only [CollatzResearch.WordTrace]
  refine ⟨401704463849999104384723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2142423807199995223385189 401704463849999104384723)
  ·
    refine ⟨602556695774998656577085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 401704463849999104384723 602556695774998656577085)
    ·
      refine ⟨225958760915624496216407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 602556695774998656577085 225958760915624496216407)
      ·
        refine ⟨338938141373436744324611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 225958760915624496216407 338938141373436744324611)
        ·
          refine ⟨508407212060155116486917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 338938141373436744324611 508407212060155116486917)
          ·
            refine ⟨95326352261279084341297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 508407212060155116486917 95326352261279084341297)
            ·
              refine ⟨71494764195959313255973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 95326352261279084341297 71494764195959313255973)
              ·
                refine ⟨13405268286742371235495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 71494764195959313255973 13405268286742371235495)
                ·
                  rfl

theorem cell20_88110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 4, 2, 4].length) (baseStart_88110 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_88110 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_88110 prefixEnd_88110 := by exact prefixLift 88110
  have htrace : WordTrace (prefixWord ++ tailWord_88110) baseStart_88110 baseEnd_88110 := by
    simpa [prefixWord, tailWord_88110, baseEnd_88110] using wordTrace_append hprefix tailTrace_88110
  have hstable : (prefixWord ++ tailWord_88110).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_88110).length < 2 ^ (prefixWord ++ tailWord_88110).sum := by decide
  have hdescent : baseEnd_88110 < baseStart_88110 := by decide
  rcases family_descends (prefixWord ++ tailWord_88110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_88114 : List Nat := [3, 2, 1, 1, 2, 4, 1, 6]
def baseStart_88114 : Nat := 118140960795 + 88114 * 2 ^ 59
def prefixEnd_88114 : Nat := 4983230072969 + 3 ^ 40 * 88114 * 2
def baseEnd_88114 : Nat := 13405876856406959191045

theorem tailTrace_88114 : CollatzResearch.WordTrace tailWord_88114 prefixEnd_88114 13405876856406959191045 := by
  unfold tailWord_88114
  simp only [CollatzResearch.WordTrace]
  refine ⟨803445400696375379555849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2142521068523667678815597 803445400696375379555849)
  ·
    refine ⟨602584050522281534666887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 803445400696375379555849 602584050522281534666887)
    ·
      refine ⟨903876075783422302000331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 602584050522281534666887 903876075783422302000331)
      ·
        refine ⟨1355814113675133453000497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 903876075783422302000331 1355814113675133453000497)
        ·
          refine ⟨1016860585256350089750373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1355814113675133453000497 1016860585256350089750373)
          ·
            refine ⟨190661359735565641828195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1016860585256350089750373 190661359735565641828195)
            ·
              refine ⟨285992039603348462742293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 190661359735565641828195 285992039603348462742293)
              ·
                refine ⟨13405876856406959191045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 285992039603348462742293 13405876856406959191045)
                ·
                  rfl

theorem cell20_88114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 1, 6].length) (baseStart_88114 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_88114 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_88114 prefixEnd_88114 := by exact prefixLift 88114
  have htrace : WordTrace (prefixWord ++ tailWord_88114) baseStart_88114 baseEnd_88114 := by
    simpa [prefixWord, tailWord_88114, baseEnd_88114] using wordTrace_append hprefix tailTrace_88114
  have hstable : (prefixWord ++ tailWord_88114).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_88114).length < 2 ^ (prefixWord ++ tailWord_88114).sum := by decide
  have hdescent : baseEnd_88114 < baseStart_88114 := by decide
  rcases family_descends (prefixWord ++ tailWord_88114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_88120 : List Nat := [2, 1, 2, 1, 7, 1, 1, 3, 2]
def baseStart_88120 : Nat := 118140960795 + 88120 * 2 ^ 59
def prefixEnd_88120 : Nat := 4983230072969 + 3 ^ 40 * 88120 * 2
def baseEnd_88120 : Nat := 40220369132711523373111

theorem tailTrace_88120 : CollatzResearch.WordTrace tailWord_88120 prefixEnd_88120 40220369132711523373111 := by
  unfold tailWord_88120
  simp only [CollatzResearch.WordTrace]
  refine ⟨1607000220381882271470907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2142666960509176361961209 1607000220381882271470907)
  ·
    refine ⟨2410500330572823407206361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1607000220381882271470907 2410500330572823407206361)
    ·
      refine ⟨1807875247929617555404771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2410500330572823407206361 1807875247929617555404771)
      ·
        refine ⟨2711812871894426333107157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1807875247929617555404771 2711812871894426333107157)
        ·
          refine ⟨63558114185025617182199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 2711812871894426333107157 63558114185025617182199)
          ·
            refine ⟨95337171277538425773299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63558114185025617182199 95337171277538425773299)
            ·
              refine ⟨143005756916307638659949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95337171277538425773299 143005756916307638659949)
              ·
                refine ⟨53627158843615364497481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 143005756916307638659949 53627158843615364497481)
                ·
                  refine ⟨40220369132711523373111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53627158843615364497481 40220369132711523373111)
                  ·
                    rfl

theorem cell20_88120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 1, 1, 3, 2].length) (baseStart_88120 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_88120 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_88120 prefixEnd_88120 := by exact prefixLift 88120
  have htrace : WordTrace (prefixWord ++ tailWord_88120) baseStart_88120 baseEnd_88120 := by
    simpa [prefixWord, tailWord_88120, baseEnd_88120] using wordTrace_append hprefix tailTrace_88120
  have hstable : (prefixWord ++ tailWord_88120).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_88120).length < 2 ^ (prefixWord ++ tailWord_88120).sum := by decide
  have hdescent : baseEnd_88120 < baseStart_88120 := by decide
  rcases family_descends (prefixWord ++ tailWord_88120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_88152 : List Nat := [2, 1, 2, 2, 1, 5, 2, 5]
def baseStart_88152 : Nat := 118140960795 + 88152 * 2 ^ 59
def prefixEnd_88152 : Nat := 4983230072969 + 3 ^ 40 * 88152 * 2
def baseEnd_88152 : Nat := 13411658268220544768771

theorem tailTrace_88152 : CollatzResearch.WordTrace tailWord_88152 prefixEnd_88152 13411658268220544768771 := by
  unfold tailWord_88152
  simp only [CollatzResearch.WordTrace]
  refine ⟨1607583788323917004053355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2143445051098556005404473 1607583788323917004053355)
  ·
    refine ⟨2411375682485875506080033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1607583788323917004053355 2411375682485875506080033)
    ·
      refine ⟨1808531761864406629560025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2411375682485875506080033 1808531761864406629560025)
      ·
        refine ⟨1356398821398304972170019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1808531761864406629560025 1356398821398304972170019)
        ·
          refine ⟨2034598232097457458255029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1356398821398304972170019 2034598232097457458255029)
          ·
            refine ⟨190743584259136636711409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2034598232097457458255029 190743584259136636711409)
            ·
              refine ⟨143057688194352477533557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 190743584259136636711409 143057688194352477533557)
              ·
                refine ⟨13411658268220544768771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 143057688194352477533557 13411658268220544768771)
                ·
                  rfl

theorem cell20_88152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 2, 5].length) (baseStart_88152 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_88152 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_88152 prefixEnd_88152 := by exact prefixLift 88152
  have htrace : WordTrace (prefixWord ++ tailWord_88152) baseStart_88152 baseEnd_88152 := by
    simpa [prefixWord, tailWord_88152, baseEnd_88152] using wordTrace_append hprefix tailTrace_88152
  have hstable : (prefixWord ++ tailWord_88152).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_88152).length < 2 ^ (prefixWord ++ tailWord_88152).sum := by decide
  have hdescent : baseEnd_88152 < baseStart_88152 := by decide
  rcases family_descends (prefixWord ++ tailWord_88152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_88193 : List Nat := [1, 2, 4, 2, 3, 1, 2, 2, 3]
def baseStart_88193 : Nat := 118140960795 + 88193 * 2 ^ 59
def prefixEnd_88193 : Nat := 4983230072969 + 3 ^ 40 * 88193 * 2
def baseEnd_88193 : Nat := 40253688321847713939479

theorem tailTrace_88193 : CollatzResearch.WordTrace tailWord_88193 prefixEnd_88193 40253688321847713939479 := by
  unfold tailWord_88193
  simp only [CollatzResearch.WordTrace]
  refine ⟨3216662969499298010349233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2144441979666198673566155 3216662969499298010349233)
  ·
    refine ⟨2412497227124473507761925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3216662969499298010349233 2412497227124473507761925)
    ·
      refine ⟨452343230085838782705361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2412497227124473507761925 452343230085838782705361)
      ·
        refine ⟨339257422564379087029021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 452343230085838782705361 339257422564379087029021)
        ·
          refine ⟨127221533461642157635883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 339257422564379087029021 127221533461642157635883)
          ·
            refine ⟨190832300192463236453825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127221533461642157635883 190832300192463236453825)
            ·
              refine ⟨143124225144347427340369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 190832300192463236453825 143124225144347427340369)
              ·
                refine ⟨107343168858260570505277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 143124225144347427340369 107343168858260570505277)
                ·
                  refine ⟨40253688321847713939479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 107343168858260570505277 40253688321847713939479)
                  ·
                    rfl

theorem cell20_88193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 2, 2, 3].length) (baseStart_88193 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_88193 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_88193 prefixEnd_88193 := by exact prefixLift 88193
  have htrace : WordTrace (prefixWord ++ tailWord_88193) baseStart_88193 baseEnd_88193 := by
    simpa [prefixWord, tailWord_88193, baseEnd_88193] using wordTrace_append hprefix tailTrace_88193
  have hstable : (prefixWord ++ tailWord_88193).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_88193).length < 2 ^ (prefixWord ++ tailWord_88193).sum := by decide
  have hdescent : baseEnd_88193 < baseStart_88193 := by decide
  rcases family_descends (prefixWord ++ tailWord_88193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_88221 : List Nat := [1, 4, 2, 1, 1, 4, 1, 2, 4]
def baseStart_88221 : Nat := 118140960795 + 88221 * 2 ^ 59
def prefixEnd_88221 : Nat := 4983230072969 + 3 ^ 40 * 88221 * 2
def baseEnd_88221 : Nat := 40266468284804061006031

theorem tailTrace_88221 : CollatzResearch.WordTrace tailWord_88221 prefixEnd_88221 40266468284804061006031 := by
  unfold tailWord_88221
  simp only [CollatzResearch.WordTrace]
  refine ⟨3217684213397858792368517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2145122808931905861579011 3217684213397858792368517)
  ·
    refine ⟨603315790012098523569097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3217684213397858792368517 603315790012098523569097)
    ·
      refine ⟨452486842509073892676823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 603315790012098523569097 452486842509073892676823)
      ·
        refine ⟨678730263763610839015235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 452486842509073892676823 678730263763610839015235)
        ·
          refine ⟨1018095395645416258522853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 678730263763610839015235 1018095395645416258522853)
          ·
            refine ⟨190892886683515548473035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1018095395645416258522853 190892886683515548473035)
            ·
              refine ⟨286339330025273322709553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 190892886683515548473035 286339330025273322709553)
              ·
                refine ⟨214754497518954992032165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 286339330025273322709553 214754497518954992032165)
                ·
                  refine ⟨40266468284804061006031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 214754497518954992032165 40266468284804061006031)
                  ·
                    rfl

theorem cell20_88221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 1, 2, 4].length) (baseStart_88221 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_88221 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_88221 prefixEnd_88221 := by exact prefixLift 88221
  have htrace : WordTrace (prefixWord ++ tailWord_88221) baseStart_88221 baseEnd_88221 := by
    simpa [prefixWord, tailWord_88221, baseEnd_88221] using wordTrace_append hprefix tailTrace_88221
  have hstable : (prefixWord ++ tailWord_88221).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_88221).length < 2 ^ (prefixWord ++ tailWord_88221).sum := by decide
  have hdescent : baseEnd_88221 < baseStart_88221 := by decide
  rcases family_descends (prefixWord ++ tailWord_88221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_88234 : List Nat := [3, 1, 5, 1, 2, 1, 2, 3, 2]
def baseStart_88234 : Nat := 118140960795 + 88234 * 2 ^ 59
def prefixEnd_88234 : Nat := 4983230072969 + 3 ^ 40 * 88234 * 2
def baseEnd_88234 : Nat := 40272401839033793572645

theorem tailTrace_88234 : CollatzResearch.WordTrace tailWord_88234 prefixEnd_88234 40272401839033793572645 := by
  unfold tailWord_88234
  simp only [CollatzResearch.WordTrace]
  refine ⟨804539590587690503147939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2145438908233841341727837 804539590587690503147939)
  ·
    refine ⟨1206809385881535754721909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 804539590587690503147939 1206809385881535754721909)
    ·
      refine ⟨113138379926393977005179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1206809385881535754721909 113138379926393977005179)
      ·
        refine ⟨169707569889590965507769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113138379926393977005179 169707569889590965507769)
        ·
          refine ⟨127280677417193224130827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 169707569889590965507769 127280677417193224130827)
          ·
            refine ⟨190921016125789836196241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127280677417193224130827 190921016125789836196241)
            ·
              refine ⟨143190762094342377147181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 190921016125789836196241 143190762094342377147181)
              ·
                refine ⟨53696535785378391430193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 143190762094342377147181 53696535785378391430193)
                ·
                  refine ⟨40272401839033793572645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53696535785378391430193 40272401839033793572645)
                  ·
                    rfl

theorem cell20_88234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 2, 3, 2].length) (baseStart_88234 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_88234 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_88234 prefixEnd_88234 := by exact prefixLift 88234
  have htrace : WordTrace (prefixWord ++ tailWord_88234) baseStart_88234 baseEnd_88234 := by
    simpa [prefixWord, tailWord_88234, baseEnd_88234] using wordTrace_append hprefix tailTrace_88234
  have hstable : (prefixWord ++ tailWord_88234).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_88234).length < 2 ^ (prefixWord ++ tailWord_88234).sum := by decide
  have hdescent : baseEnd_88234 < baseStart_88234 := by decide
  rcases family_descends (prefixWord ++ tailWord_88234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_88242 : List Nat := [3, 2, 1, 1, 1, 3, 1, 2, 6]
def baseStart_88242 : Nat := 118140960795 + 88242 * 2 ^ 59
def prefixEnd_88242 : Nat := 4983230072969 + 3 ^ 40 * 88242 * 2
def baseEnd_88242 : Nat := 40276053257021321305945

theorem tailTrace_88242 : CollatzResearch.WordTrace tailWord_88242 prefixEnd_88242 40276053257021321305945 := by
  unfold tailWord_88242
  simp only [CollatzResearch.WordTrace]
  refine ⟨804612536580444844720745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2145633430881186252588653 804612536580444844720745)
  ·
    refine ⟨603459402435333633540559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 804612536580444844720745 603459402435333633540559)
    ·
      refine ⟨905189103653000450310839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 603459402435333633540559 905189103653000450310839)
      ·
        refine ⟨1357783655479500675466259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 905189103653000450310839 1357783655479500675466259)
        ·
          refine ⟨2036675483219251013199389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1357783655479500675466259 2036675483219251013199389)
          ·
            refine ⟨763753306207219129949771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2036675483219251013199389 763753306207219129949771)
            ·
              refine ⟨1145629959310828694924657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 763753306207219129949771 1145629959310828694924657)
              ·
                refine ⟨859222469483121521193493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1145629959310828694924657 859222469483121521193493)
                ·
                  refine ⟨40276053257021321305945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 859222469483121521193493 40276053257021321305945)
                  ·
                    rfl

theorem cell20_88242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 2, 6].length) (baseStart_88242 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_88242 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_88242 prefixEnd_88242 := by exact prefixLift 88242
  have htrace : WordTrace (prefixWord ++ tailWord_88242) baseStart_88242 baseEnd_88242 := by
    simpa [prefixWord, tailWord_88242, baseEnd_88242] using wordTrace_append hprefix tailTrace_88242
  have hstable : (prefixWord ++ tailWord_88242).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_88242).length < 2 ^ (prefixWord ++ tailWord_88242).sum := by decide
  have hdescent : baseEnd_88242 < baseStart_88242 := by decide
  rcases family_descends (prefixWord ++ tailWord_88242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_88244 : List Nat := [2, 5, 3, 1, 1, 2, 1, 2, 3]
def baseStart_88244 : Nat := 118140960795 + 88244 * 2 ^ 59
def prefixEnd_88244 : Nat := 4983230072969 + 3 ^ 40 * 88244 * 2
def baseEnd_88244 : Nat := 40276966111518203239271

theorem tailTrace_88244 : CollatzResearch.WordTrace tailWord_88244 prefixEnd_88244 40276966111518203239271 := by
  unfold tailWord_88244
  simp only [CollatzResearch.WordTrace]
  refine ⟨1609261546157266860227893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2145682061543022480303857 1609261546157266860227893)
  ·
    refine ⟨150868269952243768146365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1609261546157266860227893 150868269952243768146365)
    ·
      refine ⟨56575601232091413054887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 150868269952243768146365 56575601232091413054887)
      ·
        refine ⟨84863401848137119582331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56575601232091413054887 84863401848137119582331)
        ·
          refine ⟨127295102772205679373497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84863401848137119582331 127295102772205679373497)
          ·
            refine ⟨95471327079154259530123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 127295102772205679373497 95471327079154259530123)
            ·
              refine ⟨143206990618731389295185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95471327079154259530123 143206990618731389295185)
              ·
                refine ⟨107405242964048541971389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 143206990618731389295185 107405242964048541971389)
                ·
                  refine ⟨40276966111518203239271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 107405242964048541971389 40276966111518203239271)
                  ·
                    rfl

theorem cell20_88244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 2, 1, 2, 3].length) (baseStart_88244 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_88244 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_88244 prefixEnd_88244 := by exact prefixLift 88244
  have htrace : WordTrace (prefixWord ++ tailWord_88244) baseStart_88244 baseEnd_88244 := by
    simpa [prefixWord, tailWord_88244, baseEnd_88244] using wordTrace_append hprefix tailTrace_88244
  have hstable : (prefixWord ++ tailWord_88244).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_88244).length < 2 ^ (prefixWord ++ tailWord_88244).sum := by decide
  have hdescent : baseEnd_88244 < baseStart_88244 := by decide
  rcases family_descends (prefixWord ++ tailWord_88244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_88245 : List Nat := [1, 3, 3, 4, 1, 1, 7]
def baseStart_88245 : Nat := 118140960795 + 88245 * 2 ^ 59
def prefixEnd_88245 : Nat := 4983230072969 + 3 ^ 40 * 88245 * 2
def baseEnd_88245 : Nat := 4475269170974071578437

theorem tailTrace_88245 : CollatzResearch.WordTrace tailWord_88245 prefixEnd_88245 4475269170974071578437 := by
  unfold tailWord_88245
  simp only [CollatzResearch.WordTrace]
  refine ⟨3218559565310910891242189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2145706376873940594161459 3218559565310910891242189)
  ·
    refine ⟨1206959836991591584215821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3218559565310910891242189 1206959836991591584215821)
    ·
      refine ⟨452609938871846844080933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1206959836991591584215821 452609938871846844080933)
      ·
        refine ⟨84864363538471283265175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 452609938871846844080933 84864363538471283265175)
        ·
          refine ⟨127296545307706924897763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84864363538471283265175 127296545307706924897763)
          ·
            refine ⟨190944817961560387346645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127296545307706924897763 190944817961560387346645)
            ·
              refine ⟨4475269170974071578437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 190944817961560387346645 4475269170974071578437)
              ·
                rfl

theorem cell20_88245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 7].length) (baseStart_88245 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_88245 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_88245 prefixEnd_88245 := by exact prefixLift 88245
  have htrace : WordTrace (prefixWord ++ tailWord_88245) baseStart_88245 baseEnd_88245 := by
    simpa [prefixWord, tailWord_88245, baseEnd_88245] using wordTrace_append hprefix tailTrace_88245
  have hstable : (prefixWord ++ tailWord_88245).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_88245).length < 2 ^ (prefixWord ++ tailWord_88245).sum := by decide
  have hdescent : baseEnd_88245 < baseStart_88245 := by decide
  rcases family_descends (prefixWord ++ tailWord_88245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_88249 : List Nat := [1, 2, 1, 4, 1, 2, 9]
def baseStart_88249 : Nat := 118140960795 + 88249 * 2 ^ 59
def prefixEnd_88249 : Nat := 4983230072969 + 3 ^ 40 * 88249 * 2
def baseEnd_88249 : Nat := 4475472027528934230287

theorem tailTrace_88249 : CollatzResearch.WordTrace tailWord_88249 prefixEnd_88249 4475472027528934230287 := by
  unfold tailWord_88249
  simp only [CollatzResearch.WordTrace]
  refine ⟨3218705457296419574387801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2145803638197613049591867 3218705457296419574387801)
  ·
    refine ⟨2414029092972314680790851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3218705457296419574387801 2414029092972314680790851)
    ·
      refine ⟨3621043639458472021186277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2414029092972314680790851 3621043639458472021186277)
      ·
        refine ⟨678945682398463503972427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3621043639458472021186277 678945682398463503972427)
        ·
          refine ⟨1018418523597695255958641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 678945682398463503972427 1018418523597695255958641)
          ·
            refine ⟨763813892698271441968981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1018418523597695255958641 763813892698271441968981)
            ·
              refine ⟨4475472027528934230287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 763813892698271441968981 4475472027528934230287)
              ·
                rfl

theorem cell20_88249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 9].length) (baseStart_88249 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_88249 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_88249 prefixEnd_88249 := by exact prefixLift 88249
  have htrace : WordTrace (prefixWord ++ tailWord_88249) baseStart_88249 baseEnd_88249 := by
    simpa [prefixWord, tailWord_88249, baseEnd_88249] using wordTrace_append hprefix tailTrace_88249
  have hstable : (prefixWord ++ tailWord_88249).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_88249).length < 2 ^ (prefixWord ++ tailWord_88249).sum := by decide
  have hdescent : baseEnd_88249 < baseStart_88249 := by decide
  rcases family_descends (prefixWord ++ tailWord_88249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_88252 : List Nat := [2, 2, 2, 3, 3, 1, 1, 1, 5]
def baseStart_88252 : Nat := 118140960795 + 88252 * 2 ^ 59
def prefixEnd_88252 : Nat := 4983230072969 + 3 ^ 40 * 88252 * 2
def baseEnd_88252 : Nat := 40280617529505730972571

theorem tailTrace_88252 : CollatzResearch.WordTrace tailWord_88252 prefixEnd_88252 40280617529505730972571 := by
  unfold tailWord_88252
  simp only [CollatzResearch.WordTrace]
  refine ⟨1609407438142775543373505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2145876584190367391164673 1609407438142775543373505)
  ·
    refine ⟨1207055578607081657530129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1609407438142775543373505 1207055578607081657530129)
    ·
      refine ⟨905291683955311243147597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1207055578607081657530129 905291683955311243147597)
      ·
        refine ⟨339484381483241716180349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 905291683955311243147597 339484381483241716180349)
        ·
          refine ⟨127306643056215643567631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 339484381483241716180349 127306643056215643567631)
          ·
            refine ⟨190959964584323465351447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127306643056215643567631 190959964584323465351447)
            ·
              refine ⟨286439946876485198027171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 190959964584323465351447 286439946876485198027171)
              ·
                refine ⟨429659920314727797040757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 286439946876485198027171 429659920314727797040757)
                ·
                  refine ⟨40280617529505730972571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 429659920314727797040757 40280617529505730972571)
                  ·
                    rfl

theorem cell20_88252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 1, 1, 5].length) (baseStart_88252 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_88252 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_88252 prefixEnd_88252 := by exact prefixLift 88252
  have htrace : WordTrace (prefixWord ++ tailWord_88252) baseStart_88252 baseEnd_88252 := by
    simpa [prefixWord, tailWord_88252, baseEnd_88252] using wordTrace_append hprefix tailTrace_88252
  have hstable : (prefixWord ++ tailWord_88252).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_88252).length < 2 ^ (prefixWord ++ tailWord_88252).sum := by decide
  have hdescent : baseEnd_88252 < baseStart_88252 := by decide
  rcases family_descends (prefixWord ++ tailWord_88252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_88273 : List Nat := [1, 2, 2, 1, 2, 2, 2, 5, 3]
def baseStart_88273 : Nat := 118140960795 + 88273 * 2 ^ 59
def prefixEnd_88273 : Nat := 4983230072969 + 3 ^ 40 * 88273 * 2
def baseEnd_88273 : Nat := 40290202501722991272485

theorem tailTrace_88273 : CollatzResearch.WordTrace tailWord_88273 prefixEnd_88273 40290202501722991272485 := by
  unfold tailWord_88273
  simp only [CollatzResearch.WordTrace]
  refine ⟨3219580809209471673261473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2146387206139647782174315 3219580809209471673261473)
  ·
    refine ⟨2414685606907103754946105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3219580809209471673261473 2414685606907103754946105)
    ·
      refine ⟨1811014205180327816209579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2414685606907103754946105 1811014205180327816209579)
      ·
        refine ⟨2716521307770491724314369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1811014205180327816209579 2716521307770491724314369)
        ·
          refine ⟨2037390980827868793235777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2716521307770491724314369 2037390980827868793235777)
          ·
            refine ⟨1528043235620901594926833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2037390980827868793235777 1528043235620901594926833)
            ·
              refine ⟨1146032426715676196195125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1528043235620901594926833 1146032426715676196195125)
              ·
                refine ⟨107440540004594643393293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1146032426715676196195125 107440540004594643393293)
                ·
                  refine ⟨40290202501722991272485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 107440540004594643393293 40290202501722991272485)
                  ·
                    rfl

theorem cell20_88273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 5, 3].length) (baseStart_88273 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_88273 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_88273 prefixEnd_88273 := by exact prefixLift 88273
  have htrace : WordTrace (prefixWord ++ tailWord_88273) baseStart_88273 baseEnd_88273 := by
    simpa [prefixWord, tailWord_88273, baseEnd_88273] using wordTrace_append hprefix tailTrace_88273
  have hstable : (prefixWord ++ tailWord_88273).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_88273).length < 2 ^ (prefixWord ++ tailWord_88273).sum := by decide
  have hdescent : baseEnd_88273 < baseStart_88273 := by decide
  rcases family_descends (prefixWord ++ tailWord_88273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_88293 : List Nat := [1, 3, 1, 4, 2, 3, 1, 3, 2]
def baseStart_88293 : Nat := 118140960795 + 88293 * 2 ^ 59
def prefixEnd_88293 : Nat := 4983230072969 + 3 ^ 40 * 88293 * 2
def baseEnd_88293 : Nat := 40299331046691810605737

theorem tailTrace_88293 : CollatzResearch.WordTrace tailWord_88293 prefixEnd_88293 40299331046691810605737 := by
  unfold tailWord_88293
  simp only [CollatzResearch.WordTrace]
  refine ⟨3220310269137015088989533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2146873512758010059326355 3220310269137015088989533)
  ·
    refine ⟨1207616350926380658371075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3220310269137015088989533 1207616350926380658371075)
    ·
      refine ⟨1811424526389570987556613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1207616350926380658371075 1811424526389570987556613)
      ·
        refine ⟨339642098698044560166865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1811424526389570987556613 339642098698044560166865)
        ·
          refine ⟨254731574023533420125149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 339642098698044560166865 254731574023533420125149)
          ·
            refine ⟨95524340258825032546931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 254731574023533420125149 95524340258825032546931)
            ·
              refine ⟨143286510388237548820397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95524340258825032546931 143286510388237548820397)
              ·
                refine ⟨53732441395589080807649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 143286510388237548820397 53732441395589080807649)
                ·
                  refine ⟨40299331046691810605737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53732441395589080807649 40299331046691810605737)
                  ·
                    rfl

theorem cell20_88293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 3, 1, 3, 2].length) (baseStart_88293 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_88293 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_88293 prefixEnd_88293 := by exact prefixLift 88293
  have htrace : WordTrace (prefixWord ++ tailWord_88293) baseStart_88293 baseEnd_88293 := by
    simpa [prefixWord, tailWord_88293, baseEnd_88293] using wordTrace_append hprefix tailTrace_88293
  have hstable : (prefixWord ++ tailWord_88293).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_88293).length < 2 ^ (prefixWord ++ tailWord_88293).sum := by decide
  have hdescent : baseEnd_88293 < baseStart_88293 := by decide
  rcases family_descends (prefixWord ++ tailWord_88293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_88324 : List Nat := [2, 3, 2, 2, 3, 2, 2, 1, 3]
def baseStart_88324 : Nat := 118140960795 + 88324 * 2 ^ 59
def prefixEnd_88324 : Nat := 4983230072969 + 3 ^ 40 * 88324 * 2
def baseEnd_88324 : Nat := 40313480291393480572277

theorem tailTrace_88324 : CollatzResearch.WordTrace tailWord_88324 prefixEnd_88324 40313480291393480572277 := by
  unfold tailWord_88324
  simp only [CollatzResearch.WordTrace]
  refine ⟨1610720466012353691684013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2147627288016471588912017 1610720466012353691684013)
  ·
    refine ⟨604020174754632634381505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1610720466012353691684013 604020174754632634381505)
    ·
      refine ⟨453015131065974475786129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 604020174754632634381505 453015131065974475786129)
      ·
        refine ⟨339761348299480856839597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 453015131065974475786129 339761348299480856839597)
        ·
          refine ⟨127410505612305321314849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 339761348299480856839597 127410505612305321314849)
          ·
            refine ⟨95557879209228990986137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 127410505612305321314849 95557879209228990986137)
            ·
              refine ⟨71668409406921743239603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 95557879209228990986137 71668409406921743239603)
              ·
                refine ⟨107502614110382614859405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71668409406921743239603 107502614110382614859405)
                ·
                  refine ⟨40313480291393480572277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 107502614110382614859405 40313480291393480572277)
                  ·
                    rfl

theorem cell20_88324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 2, 2, 1, 3].length) (baseStart_88324 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_88324 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_88324 prefixEnd_88324 := by exact prefixLift 88324
  have htrace : WordTrace (prefixWord ++ tailWord_88324) baseStart_88324 baseEnd_88324 := by
    simpa [prefixWord, tailWord_88324, baseEnd_88324] using wordTrace_append hprefix tailTrace_88324
  have hstable : (prefixWord ++ tailWord_88324).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_88324).length < 2 ^ (prefixWord ++ tailWord_88324).sum := by decide
  have hdescent : baseEnd_88324 < baseStart_88324 := by decide
  rcases family_descends (prefixWord ++ tailWord_88324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_88328 : List Nat := [2, 1, 3, 2, 3, 2, 1, 3, 3]
def baseStart_88328 : Nat := 118140960795 + 88328 * 2 ^ 59
def prefixEnd_88328 : Nat := 4983230072969 + 3 ^ 40 * 88328 * 2
def baseEnd_88328 : Nat := 40315306000387244438927

theorem tailTrace_88328 : CollatzResearch.WordTrace tailWord_88328 prefixEnd_88328 40315306000387244438927 := by
  unfold tailWord_88328
  simp only [CollatzResearch.WordTrace]
  refine ⟨1610793412005108033256819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2147724549340144044342425 1610793412005108033256819)
  ·
    refine ⟨2416190118007662049885229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1610793412005108033256819 2416190118007662049885229)
    ·
      refine ⟨906071294252873268706961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2416190118007662049885229 906071294252873268706961)
      ·
        refine ⟨679553470689654951530221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 906071294252873268706961 679553470689654951530221)
        ·
          refine ⟨254832551508620606823833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 679553470689654951530221 254832551508620606823833)
          ·
            refine ⟨191124413631465455117875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 254832551508620606823833 191124413631465455117875)
            ·
              refine ⟨286686620447198182676813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 191124413631465455117875 286686620447198182676813)
              ·
                refine ⟨107507482667699318503805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 286686620447198182676813 107507482667699318503805)
                ·
                  refine ⟨40315306000387244438927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 107507482667699318503805 40315306000387244438927)
                  ·
                    rfl

theorem cell20_88328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 1, 3, 3].length) (baseStart_88328 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_88328 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_88328 prefixEnd_88328 := by exact prefixLift 88328
  have htrace : WordTrace (prefixWord ++ tailWord_88328) baseStart_88328 baseEnd_88328 := by
    simpa [prefixWord, tailWord_88328, baseEnd_88328] using wordTrace_append hprefix tailTrace_88328
  have hstable : (prefixWord ++ tailWord_88328).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_88328).length < 2 ^ (prefixWord ++ tailWord_88328).sum := by decide
  have hdescent : baseEnd_88328 < baseStart_88328 := by decide
  rcases family_descends (prefixWord ++ tailWord_88328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_88359 : List Nat := [1, 1, 8, 1, 9]
def baseStart_88359 : Nat := 118140960795 + 88359 * 2 ^ 59
def prefixEnd_88359 : Nat := 4983230072969 + 3 ^ 40 * 88359 * 2
def baseEnd_88359 : Nat := 497894509198628572907

theorem tailTrace_88359 : CollatzResearch.WordTrace tailWord_88359 prefixEnd_88359 497894509198628572907 := by
  unfold tailWord_88359
  simp only [CollatzResearch.WordTrace]
  refine ⟨3222717486897908360892131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2148478324598605573928087 3222717486897908360892131)
  ·
    refine ⟨4834076230346862541338197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3222717486897908360892131 4834076230346862541338197)
    ·
      refine ⟨56649330824377295406307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 4834076230346862541338197 56649330824377295406307)
      ·
        refine ⟨84973996236565943109461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56649330824377295406307 84973996236565943109461)
        ·
          refine ⟨497894509198628572907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 84973996236565943109461 497894509198628572907)
          ·
            rfl

theorem cell20_88359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 9].length) (baseStart_88359 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_88359 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_88359 prefixEnd_88359 := by exact prefixLift 88359
  have htrace : WordTrace (prefixWord ++ tailWord_88359) baseStart_88359 baseEnd_88359 := by
    simpa [prefixWord, tailWord_88359, baseEnd_88359] using wordTrace_append hprefix tailTrace_88359
  have hstable : (prefixWord ++ tailWord_88359).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_88359).length < 2 ^ (prefixWord ++ tailWord_88359).sum := by decide
  have hdescent : baseEnd_88359 < baseStart_88359 := by decide
  rcases family_descends (prefixWord ++ tailWord_88359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_88365 : List Nat := [1, 5, 3, 1, 2, 2, 2, 2, 2]
def baseStart_88365 : Nat := 118140960795 + 88365 * 2 ^ 59
def prefixEnd_88365 : Nat := 4983230072969 + 3 ^ 40 * 88365 * 2
def baseEnd_88365 : Nat := 40332193808579560205443

theorem tailTrace_88365 : CollatzResearch.WordTrace tailWord_88365 prefixEnd_88365 40332193808579560205443 := by
  unfold tailWord_88365
  simp only [CollatzResearch.WordTrace]
  refine ⟨3222936324876171385610549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2148624216584114257073699 3222936324876171385610549)
  ·
    refine ⟨302150280457141067400989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3222936324876171385610549 302150280457141067400989)
    ·
      refine ⟨113306355171427900275371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 302150280457141067400989 113306355171427900275371)
      ·
        refine ⟨169959532757141850413057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113306355171427900275371 169959532757141850413057)
        ·
          refine ⟨127469649567856387809793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 169959532757141850413057 127469649567856387809793)
          ·
            refine ⟨95602237175892290857345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 127469649567856387809793 95602237175892290857345)
            ·
              refine ⟨71701677881919218143009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 95602237175892290857345 71701677881919218143009)
              ·
                refine ⟨53776258411439413607257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 71701677881919218143009 53776258411439413607257)
                ·
                  refine ⟨40332193808579560205443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53776258411439413607257 40332193808579560205443)
                  ·
                    rfl

theorem cell20_88365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 2, 2, 2, 2].length) (baseStart_88365 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_88365 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_88365 prefixEnd_88365 := by exact prefixLift 88365
  have htrace : WordTrace (prefixWord ++ tailWord_88365) baseStart_88365 baseEnd_88365 := by
    simpa [prefixWord, tailWord_88365, baseEnd_88365] using wordTrace_append hprefix tailTrace_88365
  have hstable : (prefixWord ++ tailWord_88365).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_88365).length < 2 ^ (prefixWord ++ tailWord_88365).sum := by decide
  have hdescent : baseEnd_88365 < baseStart_88365 := by decide
  rcases family_descends (prefixWord ++ tailWord_88365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_88387 : List Nat := [1, 1, 1, 3, 1, 3, 4, 3, 3]
def baseStart_88387 : Nat := 118140960795 + 88387 * 2 ^ 59
def prefixEnd_88387 : Nat := 4983230072969 + 3 ^ 40 * 88387 * 2
def baseEnd_88387 : Nat := 40342235208045261472019

theorem tailTrace_88387 : CollatzResearch.WordTrace tailWord_88387 prefixEnd_88387 40342235208045261472019 := by
  unfold tailWord_88387
  simp only [CollatzResearch.WordTrace]
  refine ⟨3223738730796469142911415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2149159153864312761940943 3223738730796469142911415)
  ·
    refine ⟨4835608096194703714367123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3223738730796469142911415 4835608096194703714367123)
    ·
      refine ⟨7253412144292055571550685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4835608096194703714367123 7253412144292055571550685)
      ·
        refine ⟨2720029554109520839331507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7253412144292055571550685 2720029554109520839331507)
        ·
          refine ⟨4080044331164281258997261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2720029554109520839331507 4080044331164281258997261)
          ·
            refine ⟨1530016624186605472123973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4080044331164281258997261 1530016624186605472123973)
            ·
              refine ⟨286878117034988526023245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1530016624186605472123973 286878117034988526023245)
              ·
                refine ⟨107579293888120697258717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 286878117034988526023245 107579293888120697258717)
                ·
                  refine ⟨40342235208045261472019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 107579293888120697258717 40342235208045261472019)
                  ·
                    rfl

theorem cell20_88387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 4, 3, 3].length) (baseStart_88387 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_88387 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_88387 prefixEnd_88387 := by exact prefixLift 88387
  have htrace : WordTrace (prefixWord ++ tailWord_88387) baseStart_88387 baseEnd_88387 := by
    simpa [prefixWord, tailWord_88387, baseEnd_88387] using wordTrace_append hprefix tailTrace_88387
  have hstable : (prefixWord ++ tailWord_88387).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_88387).length < 2 ^ (prefixWord ++ tailWord_88387).sum := by decide
  have hdescent : baseEnd_88387 < baseStart_88387 := by decide
  rcases family_descends (prefixWord ++ tailWord_88387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_88418 : List Nat := [3, 3, 2, 1, 1, 3, 7]
def baseStart_88418 : Nat := 118140960795 + 88418 * 2 ^ 59
def prefixEnd_88418 : Nat := 4983230072969 + 3 ^ 40 * 88418 * 2
def baseEnd_88418 : Nat := 4484042716971881270951

theorem tailTrace_88418 : CollatzResearch.WordTrace tailWord_88418 prefixEnd_88418 4484042716971881270951 := by
  unfold tailWord_88418
  simp only [CollatzResearch.WordTrace]
  refine ⟨806217348421040359322477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2149912929122774291526605 806217348421040359322477)
  ·
    refine ⟨302331505657890134745929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 806217348421040359322477 302331505657890134745929)
    ·
      refine ⟨226748629243417601059447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 302331505657890134745929 226748629243417601059447)
      ·
        refine ⟨340122943865126401589171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 226748629243417601059447 340122943865126401589171)
        ·
          refine ⟨510184415797689602383757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 340122943865126401589171 510184415797689602383757)
          ·
            refine ⟨191319155924133600893909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 510184415797689602383757 191319155924133600893909)
            ·
              refine ⟨4484042716971881270951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 191319155924133600893909 4484042716971881270951)
              ·
                rfl

theorem cell20_88418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 7].length) (baseStart_88418 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_88418 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_88418 prefixEnd_88418 := by exact prefixLift 88418
  have htrace : WordTrace (prefixWord ++ tailWord_88418) baseStart_88418 baseEnd_88418 := by
    simpa [prefixWord, tailWord_88418, baseEnd_88418] using wordTrace_append hprefix tailTrace_88418
  have hstable : (prefixWord ++ tailWord_88418).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_88418).length < 2 ^ (prefixWord ++ tailWord_88418).sum := by decide
  have hdescent : baseEnd_88418 < baseStart_88418 := by decide
  rcases family_descends (prefixWord ++ tailWord_88418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_88432 : List Nat := [2, 1, 1, 1, 4, 3, 1, 3, 4]
def baseStart_88432 : Nat := 118140960795 + 88432 * 2 ^ 59
def prefixEnd_88432 : Nat := 4983230072969 + 3 ^ 40 * 88432 * 2
def baseEnd_88432 : Nat := 40362774434225104971835

theorem tailTrace_88432 : CollatzResearch.WordTrace tailWord_88432 prefixEnd_88432 40362774434225104971835 := by
  unfold tailWord_88432
  simp only [CollatzResearch.WordTrace]
  refine ⟨1612690007816720914149775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2150253343755627885533033 1612690007816720914149775)
  ·
    refine ⟨2419035011725081371224663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1612690007816720914149775 2419035011725081371224663)
    ·
      refine ⟨3628552517587622056836995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2419035011725081371224663 3628552517587622056836995)
      ·
        refine ⟨5442828776381433085255493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3628552517587622056836995 5442828776381433085255493)
        ·
          refine ⟨1020530395571518703485405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5442828776381433085255493 1020530395571518703485405)
          ·
            refine ⟨382698898339319513807027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1020530395571518703485405 382698898339319513807027)
            ·
              refine ⟨574048347508979270710541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 382698898339319513807027 574048347508979270710541)
              ·
                refine ⟨215268130315867226516453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 574048347508979270710541 215268130315867226516453)
                ·
                  refine ⟨40362774434225104971835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 215268130315867226516453 40362774434225104971835)
                  ·
                    rfl

theorem cell20_88432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 3, 4].length) (baseStart_88432 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_88432 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_88432 prefixEnd_88432 := by exact prefixLift 88432
  have htrace : WordTrace (prefixWord ++ tailWord_88432) baseStart_88432 baseEnd_88432 := by
    simpa [prefixWord, tailWord_88432, baseEnd_88432] using wordTrace_append hprefix tailTrace_88432
  have hstable : (prefixWord ++ tailWord_88432).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_88432).length < 2 ^ (prefixWord ++ tailWord_88432).sum := by decide
  have hdescent : baseEnd_88432 < baseStart_88432 := by decide
  rcases family_descends (prefixWord ++ tailWord_88432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_88449 : List Nat := [1, 2, 4, 3, 1, 1, 2, 2, 4]
def baseStart_88449 : Nat := 118140960795 + 88449 * 2 ^ 59
def prefixEnd_88449 : Nat := 4983230072969 + 3 ^ 40 * 88449 * 2
def baseEnd_88449 : Nat := 40370533697448601405099

theorem tailTrace_88449 : CollatzResearch.WordTrace tailWord_88449 prefixEnd_88449 40370533697448601405099 := by
  unfold tailWord_88449
  simp only [CollatzResearch.WordTrace]
  refine ⟨3226000056571853731668401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2150666704381235821112267 3226000056571853731668401)
  ·
    refine ⟨2419500042428890298751301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3226000056571853731668401 2419500042428890298751301)
    ·
      refine ⟨453656257955416931015869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2419500042428890298751301 453656257955416931015869)
      ·
        refine ⟨170121096733281349130951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 453656257955416931015869 170121096733281349130951)
        ·
          refine ⟨255181645099922023696427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170121096733281349130951 255181645099922023696427)
          ·
            refine ⟨382772467649883035544641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 255181645099922023696427 382772467649883035544641)
            ·
              refine ⟨287079350737412276658481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 382772467649883035544641 287079350737412276658481)
              ·
                refine ⟨215309513053059207493861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 287079350737412276658481 215309513053059207493861)
                ·
                  refine ⟨40370533697448601405099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 215309513053059207493861 40370533697448601405099)
                  ·
                    rfl

theorem cell20_88449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 2, 2, 4].length) (baseStart_88449 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_88449 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_88449 prefixEnd_88449 := by exact prefixLift 88449
  have htrace : WordTrace (prefixWord ++ tailWord_88449) baseStart_88449 baseEnd_88449 := by
    simpa [prefixWord, tailWord_88449, baseEnd_88449] using wordTrace_append hprefix tailTrace_88449
  have hstable : (prefixWord ++ tailWord_88449).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_88449).length < 2 ^ (prefixWord ++ tailWord_88449).sum := by decide
  have hdescent : baseEnd_88449 < baseStart_88449 := by decide
  rcases family_descends (prefixWord ++ tailWord_88449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_88487 : List Nat := [1, 1, 6, 1, 1, 2, 3, 1, 4]
def baseStart_88487 : Nat := 118140960795 + 88487 * 2 ^ 59
def prefixEnd_88487 : Nat := 4983230072969 + 3 ^ 40 * 88487 * 2
def baseEnd_88487 : Nat := 40387877932889358138277

theorem tailTrace_88487 : CollatzResearch.WordTrace tailWord_88487 prefixEnd_88487 40387877932889358138277 := by
  unfold tailWord_88487
  simp only [CollatzResearch.WordTrace]
  refine ⟨3227386030434186221551715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2151590686956124147701143 3227386030434186221551715)
  ·
    refine ⟨4841079045651279332327573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3227386030434186221551715 4841079045651279332327573)
    ·
      refine ⟨226925580264903718702855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 4841079045651279332327573 226925580264903718702855)
      ·
        refine ⟨340388370397355578054283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 226925580264903718702855 340388370397355578054283)
        ·
          refine ⟨510582555596033367081425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 340388370397355578054283 510582555596033367081425)
          ·
            refine ⟨382936916697025025311069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 510582555596033367081425 382936916697025025311069)
            ·
              refine ⟨143601343761384384491651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 382936916697025025311069 143601343761384384491651)
              ·
                refine ⟨215402015642076576737477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 143601343761384384491651 215402015642076576737477)
                ·
                  refine ⟨40387877932889358138277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 215402015642076576737477 40387877932889358138277)
                  ·
                    rfl

theorem cell20_88487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 3, 1, 4].length) (baseStart_88487 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_88487 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_88487 prefixEnd_88487 := by exact prefixLift 88487
  have htrace : WordTrace (prefixWord ++ tailWord_88487) baseStart_88487 baseEnd_88487 := by
    simpa [prefixWord, tailWord_88487, baseEnd_88487] using wordTrace_append hprefix tailTrace_88487
  have hstable : (prefixWord ++ tailWord_88487).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_88487).length < 2 ^ (prefixWord ++ tailWord_88487).sum := by decide
  have hdescent : baseEnd_88487 < baseStart_88487 := by decide
  rcases family_descends (prefixWord ++ tailWord_88487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_88493 : List Nat := [1, 5, 2, 2, 3, 1, 2, 1, 3]
def baseStart_88493 : Nat := 118140960795 + 88493 * 2 ^ 59
def prefixEnd_88493 : Nat := 4983230072969 + 3 ^ 40 * 88493 * 2
def baseEnd_88493 : Nat := 40390616496380003938253

theorem tailTrace_88493 : CollatzResearch.WordTrace tailWord_88493 prefixEnd_88493 40390616496380003938253 := by
  unfold tailWord_88493
  simp only [CollatzResearch.WordTrace]
  refine ⟨3227604868412449246270133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2151736578941632830846755 3227604868412449246270133)
  ·
    refine ⟨302587956413667116837825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3227604868412449246270133 302587956413667116837825)
    ·
      refine ⟨226940967310250337628369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 302587956413667116837825 226940967310250337628369)
      ·
        refine ⟨170205725482687753221277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 226940967310250337628369 170205725482687753221277)
        ·
          refine ⟨63827147056007907457979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 170205725482687753221277 63827147056007907457979)
          ·
            refine ⟨95740720584011861186969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63827147056007907457979 95740720584011861186969)
            ·
              refine ⟨71805540438008895890227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 95740720584011861186969 71805540438008895890227)
              ·
                refine ⟨107708310657013343835341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71805540438008895890227 107708310657013343835341)
                ·
                  refine ⟨40390616496380003938253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 107708310657013343835341 40390616496380003938253)
                  ·
                    rfl

theorem cell20_88493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 1, 2, 1, 3].length) (baseStart_88493 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_88493 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_88493 prefixEnd_88493 := by exact prefixLift 88493
  have htrace : WordTrace (prefixWord ++ tailWord_88493) baseStart_88493 baseEnd_88493 := by
    simpa [prefixWord, tailWord_88493, baseEnd_88493] using wordTrace_append hprefix tailTrace_88493
  have hstable : (prefixWord ++ tailWord_88493).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_88493).length < 2 ^ (prefixWord ++ tailWord_88493).sum := by decide
  have hdescent : baseEnd_88493 < baseStart_88493 := by decide
  rcases family_descends (prefixWord ++ tailWord_88493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_88497 : List Nat := [1, 2, 2, 4, 1, 4, 2, 1, 3]
def baseStart_88497 : Nat := 118140960795 + 88497 * 2 ^ 59
def prefixEnd_88497 : Nat := 4983230072969 + 3 ^ 40 * 88497 * 2
def baseEnd_88497 : Nat := 40392442205373767804903

theorem tailTrace_88497 : CollatzResearch.WordTrace tailWord_88497 prefixEnd_88497 40392442205373767804903 := by
  unfold tailWord_88497
  simp only [CollatzResearch.WordTrace]
  refine ⟨3227750760397957929415745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2151833840265305286277163 3227750760397957929415745)
  ·
    refine ⟨2420813070298468447061809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3227750760397957929415745 2420813070298468447061809)
    ·
      refine ⟨1815609802723851335296357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2420813070298468447061809 1815609802723851335296357)
      ·
        refine ⟨340426838010722125368067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1815609802723851335296357 340426838010722125368067)
        ·
          refine ⟨510640257016083188052101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 340426838010722125368067 510640257016083188052101)
          ·
            refine ⟨95745048190515597759769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 510640257016083188052101 95745048190515597759769)
            ·
              refine ⟨71808786142886698319827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 95745048190515597759769 71808786142886698319827)
              ·
                refine ⟨107713179214330047479741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71808786142886698319827 107713179214330047479741)
                ·
                  refine ⟨40392442205373767804903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 107713179214330047479741 40392442205373767804903)
                  ·
                    rfl

theorem cell20_88497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 4, 2, 1, 3].length) (baseStart_88497 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_88497 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_88497 prefixEnd_88497 := by exact prefixLift 88497
  have htrace : WordTrace (prefixWord ++ tailWord_88497) baseStart_88497 baseEnd_88497 := by
    simpa [prefixWord, tailWord_88497, baseEnd_88497] using wordTrace_append hprefix tailTrace_88497
  have hstable : (prefixWord ++ tailWord_88497).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_88497).length < 2 ^ (prefixWord ++ tailWord_88497).sum := by decide
  have hdescent : baseEnd_88497 < baseStart_88497 := by decide
  rcases family_descends (prefixWord ++ tailWord_88497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_88549 : List Nat := [1, 3, 1, 5, 2, 2, 1, 5]
def baseStart_88549 : Nat := 118140960795 + 88549 * 2 ^ 59
def prefixEnd_88549 : Nat := 4983230072969 + 3 ^ 40 * 88549 * 2
def baseEnd_88549 : Nat := 13472058807430899357119

theorem tailTrace_88549 : CollatzResearch.WordTrace tailWord_88549 prefixEnd_88549 13472058807430899357119 := by
  unfold tailWord_88549
  simp only [CollatzResearch.WordTrace]
  refine ⟨3229647356209570810308701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2153098237473047206872467 3229647356209570810308701)
  ·
    refine ⟨1211117758578589053865763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3229647356209570810308701 1211117758578589053865763)
    ·
      refine ⟨1816676637867883580798645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1211117758578589053865763 1816676637867883580798645)
      ·
        refine ⟨170313434800114085699873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1816676637867883580798645 170313434800114085699873)
        ·
          refine ⟨127735076100085564274905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 170313434800114085699873 127735076100085564274905)
          ·
            refine ⟨95801307075064173206179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 127735076100085564274905 95801307075064173206179)
            ·
              refine ⟨143701960612596259809269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95801307075064173206179 143701960612596259809269)
              ·
                refine ⟨13472058807430899357119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 143701960612596259809269 13472058807430899357119)
                ·
                  rfl

theorem cell20_88549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 2, 1, 5].length) (baseStart_88549 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_88549 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_88549 prefixEnd_88549 := by exact prefixLift 88549
  have htrace : WordTrace (prefixWord ++ tailWord_88549) baseStart_88549 baseEnd_88549 := by
    simpa [prefixWord, tailWord_88549, baseEnd_88549] using wordTrace_append hprefix tailTrace_88549
  have hstable : (prefixWord ++ tailWord_88549).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_88549).length < 2 ^ (prefixWord ++ tailWord_88549).sum := by decide
  have hdescent : baseEnd_88549 < baseStart_88549 := by decide
  rcases family_descends (prefixWord ++ tailWord_88549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_88580 : List Nat := [2, 3, 2, 3, 1, 1, 1, 5, 2]
def baseStart_88580 : Nat := 118140960795 + 88580 * 2 ^ 59
def prefixEnd_88580 : Nat := 4983230072969 + 3 ^ 40 * 88580 * 2
def baseEnd_88580 : Nat := 40430325666994368037897

theorem tailTrace_88580 : CollatzResearch.WordTrace tailWord_88580 prefixEnd_88580 40430325666994368037897 := by
  unfold tailWord_88580
  simp only [CollatzResearch.WordTrace]
  refine ⟨1615389009548631552343597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2153852012731508736458129 1615389009548631552343597)
  ·
    refine ⟨605770878580736832128849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1615389009548631552343597 605770878580736832128849)
    ·
      refine ⟨454328158935552624096637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 605770878580736832128849 454328158935552624096637)
      ·
        refine ⟨170373059600832234036239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 454328158935552624096637 170373059600832234036239)
        ·
          refine ⟨255559589401248351054359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170373059600832234036239 255559589401248351054359)
          ·
            refine ⟨383339384101872526581539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 255559589401248351054359 383339384101872526581539)
            ·
              refine ⟨575009076152808789872309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 383339384101872526581539 575009076152808789872309)
              ·
                refine ⟨53907100889325824050529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 575009076152808789872309 53907100889325824050529)
                ·
                  refine ⟨40430325666994368037897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53907100889325824050529 40430325666994368037897)
                  ·
                    rfl

theorem cell20_88580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 5, 2].length) (baseStart_88580 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_88580 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_88580 prefixEnd_88580 := by exact prefixLift 88580
  have htrace : WordTrace (prefixWord ++ tailWord_88580) baseStart_88580 baseEnd_88580 := by
    simpa [prefixWord, tailWord_88580, baseEnd_88580] using wordTrace_append hprefix tailTrace_88580
  have hstable : (prefixWord ++ tailWord_88580).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_88580).length < 2 ^ (prefixWord ++ tailWord_88580).sum := by decide
  have hdescent : baseEnd_88580 < baseStart_88580 := by decide
  rcases family_descends (prefixWord ++ tailWord_88580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_88629 : List Nat := [1, 3, 3, 1, 1, 2, 3, 6]
def baseStart_88629 : Nat := 118140960795 + 88629 * 2 ^ 59
def prefixEnd_88629 : Nat := 4983230072969 + 3 ^ 40 * 88629 * 2
def baseEnd_88629 : Nat := 13484230200722658468121

theorem tailTrace_88629 : CollatzResearch.WordTrace tailWord_88629 prefixEnd_88629 13484230200722658468121 := by
  unfold tailWord_88629
  simp only [CollatzResearch.WordTrace]
  refine ⟨3232565195919744473220941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2155043463946496315480627 3232565195919744473220941)
  ·
    refine ⟨1212211948469904177457853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3232565195919744473220941 1212211948469904177457853)
    ·
      refine ⟨454579480676214066546695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1212211948469904177457853 454579480676214066546695)
      ·
        refine ⟨681869221014321099820043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 454579480676214066546695 681869221014321099820043)
        ·
          refine ⟨1022803831521481649730065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 681869221014321099820043 1022803831521481649730065)
          ·
            refine ⟨767102873641111237297549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1022803831521481649730065 767102873641111237297549)
            ·
              refine ⟨287663577615416713986581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 767102873641111237297549 287663577615416713986581)
              ·
                refine ⟨13484230200722658468121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 287663577615416713986581 13484230200722658468121)
                ·
                  rfl

theorem cell20_88629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 3, 6].length) (baseStart_88629 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_88629 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_88629 prefixEnd_88629 := by exact prefixLift 88629
  have htrace : WordTrace (prefixWord ++ tailWord_88629) baseStart_88629 baseEnd_88629 := by
    simpa [prefixWord, tailWord_88629, baseEnd_88629] using wordTrace_append hprefix tailTrace_88629
  have hstable : (prefixWord ++ tailWord_88629).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_88629).length < 2 ^ (prefixWord ++ tailWord_88629).sum := by decide
  have hdescent : baseEnd_88629 < baseStart_88629 := by decide
  rcases family_descends (prefixWord ++ tailWord_88629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_88643 : List Nat := [1, 1, 1, 3, 1, 2, 1, 4, 6]
def baseStart_88643 : Nat := 118140960795 + 88643 * 2 ^ 59
def prefixEnd_88643 : Nat := 4983230072969 + 3 ^ 40 * 88643 * 2
def baseEnd_88643 : Nat := 40459080583646148937639

theorem tailTrace_88643 : CollatzResearch.WordTrace tailWord_88643 prefixEnd_88643 40459080583646148937639 := by
  unfold tailWord_88643
  simp only [CollatzResearch.WordTrace]
  refine ⟨3233075817869024864230583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2155383878579349909487055 3233075817869024864230583)
  ·
    refine ⟨4849613726803537296345875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3233075817869024864230583 4849613726803537296345875)
    ·
      refine ⟨7274420590205305944518813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4849613726803537296345875 7274420590205305944518813)
      ·
        refine ⟨2727907721326989729194555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7274420590205305944518813 2727907721326989729194555)
        ·
          refine ⟨4091861581990484593791833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2727907721326989729194555 4091861581990484593791833)
          ·
            refine ⟨3068896186492863445343875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4091861581990484593791833 3068896186492863445343875)
            ·
              refine ⟨4603344279739295168015813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3068896186492863445343875 4603344279739295168015813)
              ·
                refine ⟨863127052451117844002965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4603344279739295168015813 863127052451117844002965)
                ·
                  refine ⟨40459080583646148937639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 863127052451117844002965 40459080583646148937639)
                  ·
                    rfl

theorem cell20_88643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 4, 6].length) (baseStart_88643 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_88643 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_88643 prefixEnd_88643 := by exact prefixLift 88643
  have htrace : WordTrace (prefixWord ++ tailWord_88643) baseStart_88643 baseEnd_88643 := by
    simpa [prefixWord, tailWord_88643, baseEnd_88643] using wordTrace_append hprefix tailTrace_88643
  have hstable : (prefixWord ++ tailWord_88643).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_88643).length < 2 ^ (prefixWord ++ tailWord_88643).sum := by decide
  have hdescent : baseEnd_88643 < baseStart_88643 := by decide
  rcases family_descends (prefixWord ++ tailWord_88643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_88681 : List Nat := [1, 2, 1, 1, 1, 4, 1, 3, 6]
def baseStart_88681 : Nat := 118140960795 + 88681 * 2 ^ 59
def prefixEnd_88681 : Nat := 4983230072969 + 3 ^ 40 * 88681 * 2
def baseEnd_88681 : Nat := 40476424819086905670817

theorem tailTrace_88681 : CollatzResearch.WordTrace tailWord_88681 prefixEnd_88681 40476424819086905670817 := by
  unfold tailWord_88681
  simp only [CollatzResearch.WordTrace]
  refine ⟨3234461791731357354113897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2156307861154238236075931 3234461791731357354113897)
  ·
    refine ⟨2425846343798518015585423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3234461791731357354113897 2425846343798518015585423)
    ·
      refine ⟨3638769515697777023378135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2425846343798518015585423 3638769515697777023378135)
      ·
        refine ⟨5458154273546665535067203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3638769515697777023378135 5458154273546665535067203)
        ·
          refine ⟨8187231410319998302600805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5458154273546665535067203 8187231410319998302600805)
          ·
            refine ⟨1535105889434999681737651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8187231410319998302600805 1535105889434999681737651)
            ·
              refine ⟨2302658834152499522606477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1535105889434999681737651 2302658834152499522606477)
              ·
                refine ⟨863497062807187320977429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2302658834152499522606477 863497062807187320977429)
                ·
                  refine ⟨40476424819086905670817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 863497062807187320977429 40476424819086905670817)
                  ·
                    rfl

theorem cell20_88681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 3, 6].length) (baseStart_88681 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_88681 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_88681 prefixEnd_88681 := by exact prefixLift 88681
  have htrace : WordTrace (prefixWord ++ tailWord_88681) baseStart_88681 baseEnd_88681 := by
    simpa [prefixWord, tailWord_88681, baseEnd_88681] using wordTrace_append hprefix tailTrace_88681
  have hstable : (prefixWord ++ tailWord_88681).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_88681).length < 2 ^ (prefixWord ++ tailWord_88681).sum := by decide
  have hdescent : baseEnd_88681 < baseStart_88681 := by decide
  rcases family_descends (prefixWord ++ tailWord_88681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_88708 : List Nat := [2, 3, 2, 1, 3, 2, 2, 2, 3]
def baseStart_88708 : Nat := 118140960795 + 88708 * 2 ^ 59
def prefixEnd_88708 : Nat := 4983230072969 + 3 ^ 40 * 88708 * 2
def baseEnd_88708 : Nat := 40488748354794811770707

theorem tailTrace_88708 : CollatzResearch.WordTrace tailWord_88708 prefixEnd_88708 40488748354794811770707 := by
  unfold tailWord_88708
  simp only [CollatzResearch.WordTrace]
  refine ⟨1617723281316770482673389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2156964375089027310231185 1617723281316770482673389)
  ·
    refine ⟨606646230493788931002521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1617723281316770482673389 606646230493788931002521)
    ·
      refine ⟨454984672870341698251891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 606646230493788931002521 454984672870341698251891)
      ·
        refine ⟨682477009305512547377837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 454984672870341698251891 682477009305512547377837)
        ·
          refine ⟨255928878489567205266689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 682477009305512547377837 255928878489567205266689)
          ·
            refine ⟨191946658867175403950017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 255928878489567205266689 191946658867175403950017)
            ·
              refine ⟨143959994150381552962513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 191946658867175403950017 143959994150381552962513)
              ·
                refine ⟨107969995612786164721885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 143959994150381552962513 107969995612786164721885)
                ·
                  refine ⟨40488748354794811770707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 107969995612786164721885 40488748354794811770707)
                  ·
                    rfl

theorem cell20_88708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 2, 2, 3].length) (baseStart_88708 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_88708 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_88708 prefixEnd_88708 := by exact prefixLift 88708
  have htrace : WordTrace (prefixWord ++ tailWord_88708) baseStart_88708 baseEnd_88708 := by
    simpa [prefixWord, tailWord_88708, baseEnd_88708] using wordTrace_append hprefix tailTrace_88708
  have hstable : (prefixWord ++ tailWord_88708).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_88708).length < 2 ^ (prefixWord ++ tailWord_88708).sum := by decide
  have hdescent : baseEnd_88708 < baseStart_88708 := by decide
  rcases family_descends (prefixWord ++ tailWord_88708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_88722 : List Nat := [3, 2, 3, 1, 2, 1, 3, 5]
def baseStart_88722 : Nat := 118140960795 + 88722 * 2 ^ 59
def prefixEnd_88722 : Nat := 4983230072969 + 3 ^ 40 * 88722 * 2
def baseEnd_88722 : Nat := 13498379445424328434661

theorem tailTrace_88722 : CollatzResearch.WordTrace tailWord_88722 prefixEnd_88722 13498379445424328434661 := by
  unfold tailWord_88722
  simp only [CollatzResearch.WordTrace]
  refine ⟨808989296145705339089105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2157304789721880904237613 808989296145705339089105)
  ·
    refine ⟨606741972109279004316829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 808989296145705339089105 606741972109279004316829)
    ·
      refine ⟨227528239540979626618811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 606741972109279004316829 227528239540979626618811)
      ·
        refine ⟨341292359311469439928217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 227528239540979626618811 341292359311469439928217)
        ·
          refine ⟨255969269483602079946163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 341292359311469439928217 255969269483602079946163)
          ·
            refine ⟨383953904225403119919245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 255969269483602079946163 383953904225403119919245)
            ·
              refine ⟨143982714084526169969717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 383953904225403119919245 143982714084526169969717)
              ·
                refine ⟨13498379445424328434661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 143982714084526169969717 13498379445424328434661)
                ·
                  rfl

theorem cell20_88722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 3, 5].length) (baseStart_88722 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_88722 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_88722 prefixEnd_88722 := by exact prefixLift 88722
  have htrace : WordTrace (prefixWord ++ tailWord_88722) baseStart_88722 baseEnd_88722 := by
    simpa [prefixWord, tailWord_88722, baseEnd_88722] using wordTrace_append hprefix tailTrace_88722
  have hstable : (prefixWord ++ tailWord_88722).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_88722).length < 2 ^ (prefixWord ++ tailWord_88722).sum := by decide
  have hdescent : baseEnd_88722 < baseStart_88722 := by decide
  rcases family_descends (prefixWord ++ tailWord_88722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_88767 : List Nat := [1, 1, 2, 2, 2, 4, 3, 2, 3]
def baseStart_88767 : Nat := 118140960795 + 88767 * 2 ^ 59
def prefixEnd_88767 : Nat := 4983230072969 + 3 ^ 40 * 88767 * 2
def baseEnd_88767 : Nat := 40515677562452828803799

theorem tailTrace_88767 : CollatzResearch.WordTrace tailWord_88767 prefixEnd_88767 40515677562452828803799 := by
  unfold tailWord_88767
  simp only [CollatzResearch.WordTrace]
  refine ⟨3237598469419794041744555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2158398979613196027829703 3237598469419794041744555)
  ·
    refine ⟨4856397704129691062616833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3237598469419794041744555 4856397704129691062616833)
    ·
      refine ⟨3642298278097268296962625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4856397704129691062616833 3642298278097268296962625)
      ·
        refine ⟨2731723708572951222721969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3642298278097268296962625 2731723708572951222721969)
        ·
          refine ⟨2048792781429713417041477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2731723708572951222721969 2048792781429713417041477)
          ·
            refine ⟨384148646518071265695277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2048792781429713417041477 384148646518071265695277)
            ·
              refine ⟨144055742444276724635729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 384148646518071265695277 144055742444276724635729)
              ·
                refine ⟨108041806833207543476797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 144055742444276724635729 108041806833207543476797)
                ·
                  refine ⟨40515677562452828803799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 108041806833207543476797 40515677562452828803799)
                  ·
                    rfl

theorem cell20_88767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 3, 2, 3].length) (baseStart_88767 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_88767 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_88767 prefixEnd_88767 := by exact prefixLift 88767
  have htrace : WordTrace (prefixWord ++ tailWord_88767) baseStart_88767 baseEnd_88767 := by
    simpa [prefixWord, tailWord_88767, baseEnd_88767] using wordTrace_append hprefix tailTrace_88767
  have hstable : (prefixWord ++ tailWord_88767).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_88767).length < 2 ^ (prefixWord ++ tailWord_88767).sum := by decide
  have hdescent : baseEnd_88767 < baseStart_88767 := by decide
  rcases family_descends (prefixWord ++ tailWord_88767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_88821 : List Nat := [1, 3, 6, 1, 1, 1, 3, 2, 2]
def baseStart_88821 : Nat := 118140960795 + 88821 * 2 ^ 59
def prefixEnd_88821 : Nat := 4983230072969 + 3 ^ 40 * 88821 * 2
def baseEnd_88821 : Nat := 40540324633868641003579

theorem tailTrace_88821 : CollatzResearch.WordTrace tailWord_88821 prefixEnd_88821 40540324633868641003579 := by
  unfold tailWord_88821
  simp only [CollatzResearch.WordTrace]
  refine ⟨3239568011224161264210317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2159712007482774176140211 3239568011224161264210317)
  ·
    refine ⟨1214838004209060474078869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3239568011224161264210317 1214838004209060474078869)
    ·
      refine ⟨56945531447299709722447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 1214838004209060474078869 56945531447299709722447)
      ·
        refine ⟨85418297170949564583671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56945531447299709722447 85418297170949564583671)
        ·
          refine ⟨128127445756424346875507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85418297170949564583671 128127445756424346875507)
          ·
            refine ⟨192191168634636520313261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128127445756424346875507 192191168634636520313261)
            ·
              refine ⟨72071688237988695117473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 192191168634636520313261 72071688237988695117473)
              ·
                refine ⟨54053766178491521338105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72071688237988695117473 54053766178491521338105)
                ·
                  refine ⟨40540324633868641003579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54053766178491521338105 40540324633868641003579)
                  ·
                    rfl

theorem cell20_88821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 3, 2, 2].length) (baseStart_88821 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_88821 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_88821 prefixEnd_88821 := by exact prefixLift 88821
  have htrace : WordTrace (prefixWord ++ tailWord_88821) baseStart_88821 baseEnd_88821 := by
    simpa [prefixWord, tailWord_88821, baseEnd_88821] using wordTrace_append hprefix tailTrace_88821
  have hstable : (prefixWord ++ tailWord_88821).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_88821).length < 2 ^ (prefixWord ++ tailWord_88821).sum := by decide
  have hdescent : baseEnd_88821 < baseStart_88821 := by decide
  rcases family_descends (prefixWord ++ tailWord_88821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_88826 : List Nat := [3, 1, 1, 1, 1, 3, 4, 1, 5]
def baseStart_88826 : Nat := 118140960795 + 88826 * 2 ^ 59
def prefixEnd_88826 : Nat := 4983230072969 + 3 ^ 40 * 88826 * 2
def baseEnd_88826 : Nat := 40542606770110845836891

theorem tailTrace_88826 : CollatzResearch.WordTrace tailWord_88826 prefixEnd_88826 40542606770110845836891 := by
  unfold tailWord_88826
  simp only [CollatzResearch.WordTrace]
  refine ⟨809937594051511779535583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2159833584137364745428221 809937594051511779535583)
  ·
    refine ⟨1214906391077267669303375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 809937594051511779535583 1214906391077267669303375)
    ·
      refine ⟨1822359586615901503955063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1214906391077267669303375 1822359586615901503955063)
      ·
        refine ⟨2733539379923852255932595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1822359586615901503955063 2733539379923852255932595)
        ·
          refine ⟨4100309069885778383898893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2733539379923852255932595 4100309069885778383898893)
          ·
            refine ⟨1537615901207166893962085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4100309069885778383898893 1537615901207166893962085)
            ·
              refine ⟨288302981476343792617891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1537615901207166893962085 288302981476343792617891)
              ·
                refine ⟨432454472214515688926837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 288302981476343792617891 432454472214515688926837)
                ·
                  refine ⟨40542606770110845836891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 432454472214515688926837 40542606770110845836891)
                  ·
                    rfl

theorem cell20_88826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 4, 1, 5].length) (baseStart_88826 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_88826 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_88826 prefixEnd_88826 := by exact prefixLift 88826
  have htrace : WordTrace (prefixWord ++ tailWord_88826) baseStart_88826 baseEnd_88826 := by
    simpa [prefixWord, tailWord_88826, baseEnd_88826] using wordTrace_append hprefix tailTrace_88826
  have hstable : (prefixWord ++ tailWord_88826).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_88826).length < 2 ^ (prefixWord ++ tailWord_88826).sum := by decide
  have hdescent : baseEnd_88826 < baseStart_88826 := by decide
  rcases family_descends (prefixWord ++ tailWord_88826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_88839 : List Nat := [1, 1, 4, 4, 1, 3, 2, 1, 3]
def baseStart_88839 : Nat := 118140960795 + 88839 * 2 ^ 59
def prefixEnd_88839 : Nat := 4983230072969 + 3 ^ 40 * 88839 * 2
def baseEnd_88839 : Nat := 40548540324340578403505

theorem tailTrace_88839 : CollatzResearch.WordTrace tailWord_88839 prefixEnd_88839 40548540324340578403505 := by
  unfold tailWord_88839
  simp only [CollatzResearch.WordTrace]
  refine ⟨3240224525158950338365571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2160149683439300225577047 3240224525158950338365571)
  ·
    refine ⟨4860336787738425507548357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3240224525158950338365571 4860336787738425507548357)
    ·
      refine ⟨911313147700954782665317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4860336787738425507548357 911313147700954782665317)
      ·
        refine ⟨170871215193929021749747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 911313147700954782665317 170871215193929021749747)
        ·
          refine ⟨256306822790893532624621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170871215193929021749747 256306822790893532624621)
          ·
            refine ⟨96115058546585074734233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 256306822790893532624621 96115058546585074734233)
            ·
              refine ⟨72086293909938806050675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 96115058546585074734233 72086293909938806050675)
              ·
                refine ⟨108129440864908209076013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72086293909938806050675 108129440864908209076013)
                ·
                  refine ⟨40548540324340578403505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 108129440864908209076013 40548540324340578403505)
                  ·
                    rfl

theorem cell20_88839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 3, 2, 1, 3].length) (baseStart_88839 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_88839 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_88839 prefixEnd_88839 := by exact prefixLift 88839
  have htrace : WordTrace (prefixWord ++ tailWord_88839) baseStart_88839 baseEnd_88839 := by
    simpa [prefixWord, tailWord_88839, baseEnd_88839] using wordTrace_append hprefix tailTrace_88839
  have hstable : (prefixWord ++ tailWord_88839).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_88839).length < 2 ^ (prefixWord ++ tailWord_88839).sum := by decide
  have hdescent : baseEnd_88839 < baseStart_88839 := by decide
  rcases family_descends (prefixWord ++ tailWord_88839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_88874 : List Nat := [3, 1, 4, 3, 1, 8]
def baseStart_88874 : Nat := 118140960795 + 88874 * 2 ^ 59
def prefixEnd_88874 : Nat := 4983230072969 + 3 ^ 40 * 88874 * 2
def baseEnd_88874 : Nat := 1502389454742074527285

theorem tailTrace_88874 : CollatzResearch.WordTrace tailWord_88874 prefixEnd_88874 1502389454742074527285 := by
  unfold tailWord_88874
  simp only [CollatzResearch.WordTrace]
  refine ⟨810375270008037828972419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2161000720021434210593117 810375270008037828972419)
  ·
    refine ⟨1215562905012056743458629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 810375270008037828972419 1215562905012056743458629)
    ·
      refine ⟨227918044689760639398493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1215562905012056743458629 227918044689760639398493)
      ·
        refine ⟨85469266758660239774435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 227918044689760639398493 85469266758660239774435)
        ·
          refine ⟨128203900137990359661653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85469266758660239774435 128203900137990359661653)
          ·
            refine ⟨1502389454742074527285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 128203900137990359661653 1502389454742074527285)
            ·
              rfl

theorem cell20_88874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 8].length) (baseStart_88874 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_88874 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_88874 prefixEnd_88874 := by exact prefixLift 88874
  have htrace : WordTrace (prefixWord ++ tailWord_88874) baseStart_88874 baseEnd_88874 := by
    simpa [prefixWord, tailWord_88874, baseEnd_88874] using wordTrace_append hprefix tailTrace_88874
  have hstable : (prefixWord ++ tailWord_88874).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_88874).length < 2 ^ (prefixWord ++ tailWord_88874).sum := by decide
  have hdescent : baseEnd_88874 < baseStart_88874 := by decide
  rcases family_descends (prefixWord ++ tailWord_88874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_88881 : List Nat := [1, 2, 2, 3, 2, 1, 4, 2, 3]
def baseStart_88881 : Nat := 118140960795 + 88881 * 2 ^ 59
def prefixEnd_88881 : Nat := 4983230072969 + 3 ^ 40 * 88881 * 2
def baseEnd_88881 : Nat := 40567710268775099003333

theorem tailTrace_88881 : CollatzResearch.WordTrace tailWord_88881 prefixEnd_88881 40567710268775099003333 := by
  unfold tailWord_88881
  simp only [CollatzResearch.WordTrace]
  refine ⟨3241756391006791511394497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2161170927337861007596331 3241756391006791511394497)
  ·
    refine ⟨2431317293255093633545873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3241756391006791511394497 2431317293255093633545873)
    ·
      refine ⟨1823487969941320225159405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2431317293255093633545873 1823487969941320225159405)
      ·
        refine ⟨683807988727995084434777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1823487969941320225159405 683807988727995084434777)
        ·
          refine ⟨512855991545996313326083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 683807988727995084434777 512855991545996313326083)
          ·
            refine ⟨769283987318994469989125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 512855991545996313326083 769283987318994469989125)
            ·
              refine ⟨144240747622311463122961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 769283987318994469989125 144240747622311463122961)
              ·
                refine ⟨108180560716733597342221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 144240747622311463122961 108180560716733597342221)
                ·
                  refine ⟨40567710268775099003333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 108180560716733597342221 40567710268775099003333)
                  ·
                    rfl

theorem cell20_88881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 4, 2, 3].length) (baseStart_88881 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_88881 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_88881 prefixEnd_88881 := by exact prefixLift 88881
  have htrace : WordTrace (prefixWord ++ tailWord_88881) baseStart_88881 baseEnd_88881 := by
    simpa [prefixWord, tailWord_88881, baseEnd_88881] using wordTrace_append hprefix tailTrace_88881
  have hstable : (prefixWord ++ tailWord_88881).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_88881).length < 2 ^ (prefixWord ++ tailWord_88881).sum := by decide
  have hdescent : baseEnd_88881 < baseStart_88881 := by decide
  rcases family_descends (prefixWord ++ tailWord_88881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_88895 : List Nat := [1, 1, 2, 2, 5, 1, 3, 5]
def baseStart_88895 : Nat := 118140960795 + 88895 * 2 ^ 59
def prefixEnd_88895 : Nat := 4983230072969 + 3 ^ 40 * 88895 * 2
def baseEnd_88895 : Nat := 13524700083417757512203

theorem tailTrace_88895 : CollatzResearch.WordTrace tailWord_88895 prefixEnd_88895 13524700083417757512203 := by
  unfold tailWord_88895
  simp only [CollatzResearch.WordTrace]
  refine ⟨3242267012956071902404139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2161511341970714601602759 3242267012956071902404139)
  ·
    refine ⟨4863400519434107853606209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3242267012956071902404139 4863400519434107853606209)
    ·
      refine ⟨3647550389575580890204657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4863400519434107853606209 3647550389575580890204657)
      ·
        refine ⟨2735662792181685667653493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3647550389575580890204657 2735662792181685667653493)
        ·
          refine ⟨256468386767033031342515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2735662792181685667653493 256468386767033031342515)
          ·
            refine ⟨384702580150549547013773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 256468386767033031342515 384702580150549547013773)
            ·
              refine ⟨144263467556456080130165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 384702580150549547013773 144263467556456080130165)
              ·
                refine ⟨13524700083417757512203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 144263467556456080130165 13524700083417757512203)
                ·
                  rfl

theorem cell20_88895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 3, 5].length) (baseStart_88895 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_88895 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_88895 prefixEnd_88895 := by exact prefixLift 88895
  have htrace : WordTrace (prefixWord ++ tailWord_88895) baseStart_88895 baseEnd_88895 := by
    simpa [prefixWord, tailWord_88895, baseEnd_88895] using wordTrace_append hprefix tailTrace_88895
  have hstable : (prefixWord ++ tailWord_88895).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_88895).length < 2 ^ (prefixWord ++ tailWord_88895).sum := by decide
  have hdescent : baseEnd_88895 < baseStart_88895 := by decide
  rcases family_descends (prefixWord ++ tailWord_88895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_88936 : List Nat := [2, 1, 4, 2, 1, 4, 1, 2, 3]
def baseStart_88936 : Nat := 118140960795 + 88936 * 2 ^ 59
def prefixEnd_88936 : Nat := 4983230072969 + 3 ^ 40 * 88936 * 2
def baseEnd_88936 : Nat := 40592813767439352169775

theorem tailTrace_88936 : CollatzResearch.WordTrace tailWord_88936 prefixEnd_88936 40592813767439352169775 := by
  unfold tailWord_88936
  simp only [CollatzResearch.WordTrace]
  refine ⟨1621881202903767952323331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2162508270538357269764441 1621881202903767952323331)
  ·
    refine ⟨2432821804355651928484997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1621881202903767952323331 2432821804355651928484997)
    ·
      refine ⟨456154088316684736590937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2432821804355651928484997 456154088316684736590937)
      ·
        refine ⟨342115566237513552443203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 456154088316684736590937 342115566237513552443203)
        ·
          refine ⟨513173349356270328664805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 342115566237513552443203 513173349356270328664805)
          ·
            refine ⟨96220003004300686624651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 513173349356270328664805 96220003004300686624651)
            ·
              refine ⟨144330004506451029936977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96220003004300686624651 144330004506451029936977)
              ·
                refine ⟨108247503379838272452733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 144330004506451029936977 108247503379838272452733)
                ·
                  refine ⟨40592813767439352169775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 108247503379838272452733 40592813767439352169775)
                  ·
                    rfl

theorem cell20_88936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 4, 1, 2, 3].length) (baseStart_88936 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_88936 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_88936 prefixEnd_88936 := by exact prefixLift 88936
  have htrace : WordTrace (prefixWord ++ tailWord_88936) baseStart_88936 baseEnd_88936 := by
    simpa [prefixWord, tailWord_88936, baseEnd_88936] using wordTrace_append hprefix tailTrace_88936
  have hstable : (prefixWord ++ tailWord_88936).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_88936).length < 2 ^ (prefixWord ++ tailWord_88936).sum := by decide
  have hdescent : baseEnd_88936 < baseStart_88936 := by decide
  rcases family_descends (prefixWord ++ tailWord_88936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_88940 : List Nat := [2, 2, 1, 1, 4, 1, 3, 1, 5]
def baseStart_88940 : Nat := 118140960795 + 88940 * 2 ^ 59
def prefixEnd_88940 : Nat := 4983230072969 + 3 ^ 40 * 88940 * 2
def baseEnd_88940 : Nat := 40594639476433116036425

theorem tailTrace_88940 : CollatzResearch.WordTrace tailWord_88940 prefixEnd_88940 40594639476433116036425 := by
  unfold tailWord_88940
  simp only [CollatzResearch.WordTrace]
  refine ⟨1621954148896522293896137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2162605531862029725194849 1621954148896522293896137)
  ·
    refine ⟨1216465611672391720422103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1621954148896522293896137 1216465611672391720422103)
    ·
      refine ⟨1824698417508587580633155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1216465611672391720422103 1824698417508587580633155)
      ·
        refine ⟨2737047626262881370949733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1824698417508587580633155 2737047626262881370949733)
        ·
          refine ⟨513196429924290257053075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2737047626262881370949733 513196429924290257053075)
          ·
            refine ⟨769794644886435385579613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 513196429924290257053075 769794644886435385579613)
            ·
              refine ⟨288672991832413269592355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 769794644886435385579613 288672991832413269592355)
              ·
                refine ⟨433009487748619904388533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 288672991832413269592355 433009487748619904388533)
                ·
                  refine ⟨40594639476433116036425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 433009487748619904388533 40594639476433116036425)
                  ·
                    rfl

theorem cell20_88940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 5].length) (baseStart_88940 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_88940 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_88940 prefixEnd_88940 := by exact prefixLift 88940
  have htrace : WordTrace (prefixWord ++ tailWord_88940) baseStart_88940 baseEnd_88940 := by
    simpa [prefixWord, tailWord_88940, baseEnd_88940] using wordTrace_append hprefix tailTrace_88940
  have hstable : (prefixWord ++ tailWord_88940).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_88940).length < 2 ^ (prefixWord ++ tailWord_88940).sum := by decide
  have hdescent : baseEnd_88940 < baseStart_88940 := by decide
  rcases family_descends (prefixWord ++ tailWord_88940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_88947 : List Nat := [1, 1, 1, 2, 2, 1, 5, 3, 4]
def baseStart_88947 : Nat := 118140960795 + 88947 * 2 ^ 59
def prefixEnd_88947 : Nat := 4983230072969 + 3 ^ 40 * 88947 * 2
def baseEnd_88947 : Nat := 40597834467172202803063

theorem tailTrace_88947 : CollatzResearch.WordTrace tailWord_88947 prefixEnd_88947 40597834467172202803063 := by
  unfold tailWord_88947
  simp only [CollatzResearch.WordTrace]
  refine ⟨3244163608767684783297095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2162775739178456522198063 3244163608767684783297095)
  ·
    refine ⟨4866245413151527174945643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3244163608767684783297095 4866245413151527174945643)
    ·
      refine ⟨7299368119727290762418465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4866245413151527174945643 7299368119727290762418465)
      ·
        refine ⟨5474526089795468071813849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7299368119727290762418465 5474526089795468071813849)
        ·
          refine ⟨4105894567346601053860387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5474526089795468071813849 4105894567346601053860387)
          ·
            refine ⟨6158841851019901580790581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4105894567346601053860387 6158841851019901580790581)
            ·
              refine ⟨577391423533115773199117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6158841851019901580790581 577391423533115773199117)
              ·
                refine ⟨216521783824918414949669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 577391423533115773199117 216521783824918414949669)
                ·
                  refine ⟨40597834467172202803063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 216521783824918414949669 40597834467172202803063)
                  ·
                    rfl

theorem cell20_88947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 3, 4].length) (baseStart_88947 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_88947 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_88947 prefixEnd_88947 := by exact prefixLift 88947
  have htrace : WordTrace (prefixWord ++ tailWord_88947) baseStart_88947 baseEnd_88947 := by
    simpa [prefixWord, tailWord_88947, baseEnd_88947] using wordTrace_append hprefix tailTrace_88947
  have hstable : (prefixWord ++ tailWord_88947).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_88947).length < 2 ^ (prefixWord ++ tailWord_88947).sum := by decide
  have hdescent : baseEnd_88947 < baseStart_88947 := by decide
  rcases family_descends (prefixWord ++ tailWord_88947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_88954 : List Nat := [3, 1, 1, 1, 1, 1, 3, 9]
def baseStart_88954 : Nat := 118140960795 + 88954 * 2 ^ 59
def prefixEnd_88954 : Nat := 4983230072969 + 3 ^ 40 * 88954 * 2
def baseEnd_88954 : Nat := 13533676485970429856567

theorem tailTrace_88954 : CollatzResearch.WordTrace tailWord_88954 prefixEnd_88954 13533676485970429856567 := by
  unfold tailWord_88954
  simp only [CollatzResearch.WordTrace]
  refine ⟨811104729935581244700479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2162945946494883319201277 811104729935581244700479)
  ·
    refine ⟨1216657094903371867050719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 811104729935581244700479 1216657094903371867050719)
    ·
      refine ⟨1824985642355057800576079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1216657094903371867050719 1824985642355057800576079)
      ·
        refine ⟨2737478463532586700864119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1824985642355057800576079 2737478463532586700864119)
        ·
          refine ⟨4106217695298880051296179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2737478463532586700864119 4106217695298880051296179)
          ·
            refine ⟨6159326542948320076944269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4106217695298880051296179 6159326542948320076944269)
            ·
              refine ⟨2309747453605620028854101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6159326542948320076944269 2309747453605620028854101)
              ·
                refine ⟨13533676485970429856567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 2309747453605620028854101 13533676485970429856567)
                ·
                  rfl

theorem cell20_88954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 9].length) (baseStart_88954 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_88954 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_88954 prefixEnd_88954 := by exact prefixLift 88954
  have htrace : WordTrace (prefixWord ++ tailWord_88954) baseStart_88954 baseEnd_88954 := by
    simpa [prefixWord, tailWord_88954, baseEnd_88954] using wordTrace_append hprefix tailTrace_88954
  have hstable : (prefixWord ++ tailWord_88954).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_88954).length < 2 ^ (prefixWord ++ tailWord_88954).sum := by decide
  have hdescent : baseEnd_88954 < baseStart_88954 := by decide
  rcases family_descends (prefixWord ++ tailWord_88954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_88971 : List Nat := [1, 1, 1, 1, 4, 2, 6, 4]
def baseStart_88971 : Nat := 118140960795 + 88971 * 2 ^ 59
def prefixEnd_88971 : Nat := 4983230072969 + 3 ^ 40 * 88971 * 2
def baseEnd_88971 : Nat := 13536262907044928667655

theorem tailTrace_88971 : CollatzResearch.WordTrace tailWord_88971 prefixEnd_88971 13536262907044928667655 := by
  unfold tailWord_88971
  simp only [CollatzResearch.WordTrace]
  refine ⟨3245038960680736882170767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2163359307120491254780511 3245038960680736882170767)
  ·
    refine ⟨4867558441021105323256151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3245038960680736882170767 4867558441021105323256151)
    ·
      refine ⟨7301337661531657984884227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4867558441021105323256151 7301337661531657984884227)
      ·
        refine ⟨10952006492297486977326341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7301337661531657984884227 10952006492297486977326341)
        ·
          refine ⟨2053501217305778808248689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10952006492297486977326341 2053501217305778808248689)
          ·
            refine ⟨1540125912979334106186517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2053501217305778808248689 1540125912979334106186517)
            ·
              refine ⟨72193402170906286227493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1540125912979334106186517 72193402170906286227493)
              ·
                refine ⟨13536262907044928667655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 72193402170906286227493 13536262907044928667655)
                ·
                  rfl

theorem cell20_88971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 6, 4].length) (baseStart_88971 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_88971 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_88971 prefixEnd_88971 := by exact prefixLift 88971
  have htrace : WordTrace (prefixWord ++ tailWord_88971) baseStart_88971 baseEnd_88971 := by
    simpa [prefixWord, tailWord_88971, baseEnd_88971] using wordTrace_append hprefix tailTrace_88971
  have hstable : (prefixWord ++ tailWord_88971).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_88971).length < 2 ^ (prefixWord ++ tailWord_88971).sum := by decide
  have hdescent : baseEnd_88971 < baseStart_88971 := by decide
  rcases family_descends (prefixWord ++ tailWord_88971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_88981 : List Nat := [1, 3, 2, 1, 1, 4, 3, 3, 2]
def baseStart_88981 : Nat := 118140960795 + 88981 * 2 ^ 59
def prefixEnd_88981 : Nat := 4983230072969 + 3 ^ 40 * 88981 * 2
def baseEnd_88981 : Nat := 40613352993619195669591

theorem tailTrace_88981 : CollatzResearch.WordTrace tailWord_88981 prefixEnd_88981 40613352993619195669591 := by
  unfold tailWord_88981
  simp only [CollatzResearch.WordTrace]
  refine ⟨3245403690644508590034797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2163602460429672393356531 3245403690644508590034797)
  ·
    refine ⟨1217026383991690721263049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3245403690644508590034797 1217026383991690721263049)
    ·
      refine ⟨912769787993768040947287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1217026383991690721263049 912769787993768040947287)
      ·
        refine ⟨1369154681990652061420931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 912769787993768040947287 1369154681990652061420931)
        ·
          refine ⟨2053732022985978092131397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1369154681990652061420931 2053732022985978092131397)
          ·
            refine ⟨385074754309870892274637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2053732022985978092131397 385074754309870892274637)
            ·
              refine ⟨144403032866201584602989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 385074754309870892274637 144403032866201584602989)
              ·
                refine ⟨54151137324825594226121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 144403032866201584602989 54151137324825594226121)
                ·
                  refine ⟨40613352993619195669591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54151137324825594226121 40613352993619195669591)
                  ·
                    rfl

theorem cell20_88981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 3, 3, 2].length) (baseStart_88981 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_88981 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_88981 prefixEnd_88981 := by exact prefixLift 88981
  have htrace : WordTrace (prefixWord ++ tailWord_88981) baseStart_88981 baseEnd_88981 := by
    simpa [prefixWord, tailWord_88981, baseEnd_88981] using wordTrace_append hprefix tailTrace_88981
  have hstable : (prefixWord ++ tailWord_88981).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_88981).length < 2 ^ (prefixWord ++ tailWord_88981).sum := by decide
  have hdescent : baseEnd_88981 < baseStart_88981 := by decide
  rcases family_descends (prefixWord ++ tailWord_88981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_88988 : List Nat := [2, 2, 3, 3, 2, 2, 6]
def baseStart_88988 : Nat := 118140960795 + 88988 * 2 ^ 59
def prefixEnd_88988 : Nat := 4983230072969 + 3 ^ 40 * 88988 * 2
def baseEnd_88988 : Nat := 4512949776039809159581

theorem tailTrace_88988 : CollatzResearch.WordTrace tailWord_88988 prefixEnd_88988 4512949776039809159581 := by
  unfold tailWord_88988
  simp only [CollatzResearch.WordTrace]
  refine ⟨1622829500809574392769809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2163772667746099190359745 1622829500809574392769809)
  ·
    refine ⟨1217122125607180794577357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1622829500809574392769809 1217122125607180794577357)
    ·
      refine ⟨456420797102692797966509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1217122125607180794577357 456420797102692797966509)
      ·
        refine ⟨171157798913509799237441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 456420797102692797966509 171157798913509799237441)
        ·
          refine ⟨128368349185132349428081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 171157798913509799237441 128368349185132349428081)
          ·
            refine ⟨96276261888849262071061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 128368349185132349428081 96276261888849262071061)
            ·
              refine ⟨4512949776039809159581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 96276261888849262071061 4512949776039809159581)
              ·
                rfl

theorem cell20_88988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 2, 6].length) (baseStart_88988 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_88988 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_88988 prefixEnd_88988 := by exact prefixLift 88988
  have htrace : WordTrace (prefixWord ++ tailWord_88988) baseStart_88988 baseEnd_88988 := by
    simpa [prefixWord, tailWord_88988, baseEnd_88988] using wordTrace_append hprefix tailTrace_88988
  have hstable : (prefixWord ++ tailWord_88988).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_88988).length < 2 ^ (prefixWord ++ tailWord_88988).sum := by decide
  have hdescent : baseEnd_88988 < baseStart_88988 := by decide
  rcases family_descends (prefixWord ++ tailWord_88988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_88992 : List Nat := [2, 1, 1, 4, 1, 1, 10]
def baseStart_88992 : Nat := 118140960795 + 88992 * 2 ^ 59
def prefixEnd_88992 : Nat := 4983230072969 + 3 ^ 40 * 88992 * 2
def baseEnd_88992 : Nat := 4513152632594671811431

theorem tailTrace_88992 : CollatzResearch.WordTrace tailWord_88992 prefixEnd_88992 4513152632594671811431 := by
  unfold tailWord_88992
  simp only [CollatzResearch.WordTrace]
  refine ⟨1622902446802328734342615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2163869929069771645790153 1622902446802328734342615)
  ·
    refine ⟨2434353670203493101513923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1622902446802328734342615 2434353670203493101513923)
    ·
      refine ⟨3651530505305239652270885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2434353670203493101513923 3651530505305239652270885)
      ·
        refine ⟨684661969744732434800791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3651530505305239652270885 684661969744732434800791)
        ·
          refine ⟨1026992954617098652201187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 684661969744732434800791 1026992954617098652201187)
          ·
            refine ⟨1540489431925647978301781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1026992954617098652201187 1540489431925647978301781)
            ·
              refine ⟨4513152632594671811431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 1540489431925647978301781 4513152632594671811431)
              ·
                rfl

theorem cell20_88992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 10].length) (baseStart_88992 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_88992 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_88992 prefixEnd_88992 := by exact prefixLift 88992
  have htrace : WordTrace (prefixWord ++ tailWord_88992) baseStart_88992 baseEnd_88992 := by
    simpa [prefixWord, tailWord_88992, baseEnd_88992] using wordTrace_append hprefix tailTrace_88992
  have hstable : (prefixWord ++ tailWord_88992).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_88992).length < 2 ^ (prefixWord ++ tailWord_88992).sum := by decide
  have hdescent : baseEnd_88992 < baseStart_88992 := by decide
  rcases family_descends (prefixWord ++ tailWord_88992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_89005 : List Nat := [1, 5, 2, 3, 1, 1, 2, 5]
def baseStart_89005 : Nat := 118140960795 + 89005 * 2 ^ 59
def prefixEnd_89005 : Nat := 4983230072969 + 3 ^ 40 * 89005 * 2
def baseEnd_89005 : Nat := 13541435749193926289831

theorem tailTrace_89005 : CollatzResearch.WordTrace tailWord_89005 prefixEnd_89005 13541435749193926289831 := by
  unfold tailWord_89005
  simp only [CollatzResearch.WordTrace]
  refine ⟨3246279042557560688908469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2164186028371707125938979 3246279042557560688908469)
  ·
    refine ⟨304338660239771314585169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3246279042557560688908469 304338660239771314585169)
    ·
      refine ⟨228253995179828485938877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 304338660239771314585169 228253995179828485938877)
      ·
        refine ⟨85595248192435682227079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 228253995179828485938877 85595248192435682227079)
        ·
          refine ⟨128392872288653523340619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85595248192435682227079 128392872288653523340619)
          ·
            refine ⟨192589308432980285010929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128392872288653523340619 192589308432980285010929)
            ·
              refine ⟨144441981324735213758197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 192589308432980285010929 144441981324735213758197)
              ·
                refine ⟨13541435749193926289831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 144441981324735213758197 13541435749193926289831)
                ·
                  rfl

theorem cell20_89005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 2, 5].length) (baseStart_89005 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_89005 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_89005 prefixEnd_89005 := by exact prefixLift 89005
  have htrace : WordTrace (prefixWord ++ tailWord_89005) baseStart_89005 baseEnd_89005 := by
    simpa [prefixWord, tailWord_89005, baseEnd_89005] using wordTrace_append hprefix tailTrace_89005
  have hstable : (prefixWord ++ tailWord_89005).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_89005).length < 2 ^ (prefixWord ++ tailWord_89005).sum := by decide
  have hdescent : baseEnd_89005 < baseStart_89005 := by decide
  rcases family_descends (prefixWord ++ tailWord_89005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_89040 : List Nat := [2, 1, 1, 1, 1, 2, 3, 7, 2]
def baseStart_89040 : Nat := 118140960795 + 89040 * 2 ^ 59
def prefixEnd_89040 : Nat := 4983230072969 + 3 ^ 40 * 89040 * 2
def baseEnd_89040 : Nat := 40640282201277212702683

theorem tailTrace_89040 : CollatzResearch.WordTrace tailWord_89040 prefixEnd_89040 40640282201277212702683 := by
  unfold tailWord_89040
  simp only [CollatzResearch.WordTrace]
  refine ⟨1623777798715380833216287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2165037064953841110955049 1623777798715380833216287)
  ·
    refine ⟨2435666698073071249824431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1623777798715380833216287 2435666698073071249824431)
    ·
      refine ⟨3653500047109606874736647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2435666698073071249824431 3653500047109606874736647)
      ·
        refine ⟨5480250070664410312104971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3653500047109606874736647 5480250070664410312104971)
        ·
          refine ⟨8220375105996615468157457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5480250070664410312104971 8220375105996615468157457)
          ·
            refine ⟨6165281329497461601118093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8220375105996615468157457 6165281329497461601118093)
            ·
              refine ⟨2311980498561548100419285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6165281329497461601118093 2311980498561548100419285)
              ·
                refine ⟨54187042935036283603577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2311980498561548100419285 54187042935036283603577)
                ·
                  refine ⟨40640282201277212702683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54187042935036283603577 40640282201277212702683)
                  ·
                    rfl

theorem cell20_89040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 7, 2].length) (baseStart_89040 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_89040 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_89040 prefixEnd_89040 := by exact prefixLift 89040
  have htrace : WordTrace (prefixWord ++ tailWord_89040) baseStart_89040 baseEnd_89040 := by
    simpa [prefixWord, tailWord_89040, baseEnd_89040] using wordTrace_append hprefix tailTrace_89040
  have hstable : (prefixWord ++ tailWord_89040).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_89040).length < 2 ^ (prefixWord ++ tailWord_89040).sum := by decide
  have hdescent : baseEnd_89040 < baseStart_89040 := by decide
  rcases family_descends (prefixWord ++ tailWord_89040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_89053 : List Nat := [1, 4, 3, 1, 2, 3, 2, 2, 2]
def baseStart_89053 : Nat := 118140960795 + 89053 * 2 ^ 59
def prefixEnd_89053 : Nat := 4983230072969 + 3 ^ 40 * 89053 * 2
def baseEnd_89053 : Nat := 40646215755506945269297

theorem tailTrace_89053 : CollatzResearch.WordTrace tailWord_89053 prefixEnd_89053 40646215755506945269297 := by
  unfold tailWord_89053
  simp only [CollatzResearch.WordTrace]
  refine ⟨3248029746383664886655813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2165353164255776591103875 3248029746383664886655813)
  ·
    refine ⟨609005577446937166247965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3248029746383664886655813 609005577446937166247965)
    ·
      refine ⟨228377091542601437342987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 609005577446937166247965 228377091542601437342987)
      ·
        refine ⟨342565637313902156014481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 228377091542601437342987 342565637313902156014481)
        ·
          refine ⟨256924227985426617010861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 342565637313902156014481 256924227985426617010861)
          ·
            refine ⟨96346585494534981379073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 256924227985426617010861 96346585494534981379073)
            ·
              refine ⟨72259939120901236034305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 96346585494534981379073 72259939120901236034305)
              ·
                refine ⟨54194954340675927025729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72259939120901236034305 54194954340675927025729)
                ·
                  refine ⟨40646215755506945269297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54194954340675927025729 40646215755506945269297)
                  ·
                    rfl

theorem cell20_89053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 3, 2, 2, 2].length) (baseStart_89053 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_89053 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_89053 prefixEnd_89053 := by exact prefixLift 89053
  have htrace : WordTrace (prefixWord ++ tailWord_89053) baseStart_89053 baseEnd_89053 := by
    simpa [prefixWord, tailWord_89053, baseEnd_89053] using wordTrace_append hprefix tailTrace_89053
  have hstable : (prefixWord ++ tailWord_89053).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_89053).length < 2 ^ (prefixWord ++ tailWord_89053).sum := by decide
  have hdescent : baseEnd_89053 < baseStart_89053 := by decide
  rcases family_descends (prefixWord ++ tailWord_89053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_89075 : List Nat := [1, 1, 1, 2, 2, 2, 1, 1, 9]
def baseStart_89075 : Nat := 118140960795 + 89075 * 2 ^ 59
def prefixEnd_89075 : Nat := 4983230072969 + 3 ^ 40 * 89075 * 2
def baseEnd_89075 : Nat := 40656257154972646535873

theorem tailTrace_89075 : CollatzResearch.WordTrace tailWord_89075 prefixEnd_89075 40656257154972646535873 := by
  unfold tailWord_89075
  simp only [CollatzResearch.WordTrace]
  refine ⟨3248832152303962643956679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2165888101535975095971119 3248832152303962643956679)
  ·
    refine ⟨4873248228455943965935019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3248832152303962643956679 4873248228455943965935019)
    ·
      refine ⟨7309872342683915948902529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4873248228455943965935019 7309872342683915948902529)
      ·
        refine ⟨5482404257012936961676897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7309872342683915948902529 5482404257012936961676897)
        ·
          refine ⟨4111803192759702721257673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5482404257012936961676897 4111803192759702721257673)
          ·
            refine ⟨3083852394569777040943255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4111803192759702721257673 3083852394569777040943255)
            ·
              refine ⟨4625778591854665561414883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3083852394569777040943255 4625778591854665561414883)
              ·
                refine ⟨6938667887781998342122325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4625778591854665561414883 6938667887781998342122325)
                ·
                  refine ⟨40656257154972646535873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 6938667887781998342122325 40656257154972646535873)
                  ·
                    rfl

theorem cell20_89075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 9].length) (baseStart_89075 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_89075 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_89075 prefixEnd_89075 := by exact prefixLift 89075
  have htrace : WordTrace (prefixWord ++ tailWord_89075) baseStart_89075 baseEnd_89075 := by
    simpa [prefixWord, tailWord_89075, baseEnd_89075] using wordTrace_append hprefix tailTrace_89075
  have hstable : (prefixWord ++ tailWord_89075).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_89075).length < 2 ^ (prefixWord ++ tailWord_89075).sum := by decide
  have hdescent : baseEnd_89075 < baseStart_89075 := by decide
  rcases family_descends (prefixWord ++ tailWord_89075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_89078 : List Nat := [5, 1, 1, 1, 3, 1, 1, 1, 6]
def baseStart_89078 : Nat := 118140960795 + 89078 * 2 ^ 59
def prefixEnd_89078 : Nat := 4983230072969 + 3 ^ 40 * 89078 * 2
def baseEnd_89078 : Nat := 40657626436717969435861

theorem tailTrace_89078 : CollatzResearch.WordTrace tailWord_89078 prefixEnd_89078 40657626436717969435861 := by
  unfold tailWord_89078
  simp only [CollatzResearch.WordTrace]
  refine ⟨203058848205818384769743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2165961047528729437543925 203058848205818384769743)
  ·
    refine ⟨304588272308727577154615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203058848205818384769743 304588272308727577154615)
    ·
      refine ⟨456882408463091365731923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 304588272308727577154615 456882408463091365731923)
      ·
        refine ⟨685323612694637048597885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 456882408463091365731923 685323612694637048597885)
        ·
          refine ⟨256996354760488893224207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 685323612694637048597885 256996354760488893224207)
          ·
            refine ⟨385494532140733339836311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 256996354760488893224207 385494532140733339836311)
            ·
              refine ⟨578241798211100009754467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 385494532140733339836311 578241798211100009754467)
              ·
                refine ⟨867362697316650014631701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 578241798211100009754467 867362697316650014631701)
                ·
                  refine ⟨40657626436717969435861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 867362697316650014631701 40657626436717969435861)
                  ·
                    rfl

theorem cell20_89078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 1, 6].length) (baseStart_89078 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_89078 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_89078 prefixEnd_89078 := by exact prefixLift 89078
  have htrace : WordTrace (prefixWord ++ tailWord_89078) baseStart_89078 baseEnd_89078 := by
    simpa [prefixWord, tailWord_89078, baseEnd_89078] using wordTrace_append hprefix tailTrace_89078
  have hstable : (prefixWord ++ tailWord_89078).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_89078).length < 2 ^ (prefixWord ++ tailWord_89078).sum := by decide
  have hdescent : baseEnd_89078 < baseStart_89078 := by decide
  rcases family_descends (prefixWord ++ tailWord_89078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_89095 : List Nat := [1, 1, 4, 3, 1, 1, 4, 3, 2]
def baseStart_89095 : Nat := 118140960795 + 89095 * 2 ^ 59
def prefixEnd_89095 : Nat := 4983230072969 + 3 ^ 40 * 89095 * 2
def baseEnd_89095 : Nat := 40665385699941465869125

theorem tailTrace_89095 : CollatzResearch.WordTrace tailWord_89095 prefixEnd_89095 40665385699941465869125 := by
  unfold tailWord_89095
  simp only [CollatzResearch.WordTrace]
  refine ⟨3249561612231506059684739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2166374408154337373123159 3249561612231506059684739)
  ·
    refine ⟨4874342418347259089527109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3249561612231506059684739 4874342418347259089527109)
    ·
      refine ⟨913939203440111079286333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4874342418347259089527109 913939203440111079286333)
      ·
        refine ⟨342727201290041654732375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 913939203440111079286333 342727201290041654732375)
        ·
          refine ⟨514090801935062482098563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 342727201290041654732375 514090801935062482098563)
          ·
            refine ⟨771136202902593723147845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 514090801935062482098563 771136202902593723147845)
            ·
              refine ⟨144588038044236323090221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 771136202902593723147845 144588038044236323090221)
              ·
                refine ⟨54220514266588621158833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 144588038044236323090221 54220514266588621158833)
                ·
                  refine ⟨40665385699941465869125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54220514266588621158833 40665385699941465869125)
                  ·
                    rfl

theorem cell20_89095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 4, 3, 2].length) (baseStart_89095 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_89095 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_89095 prefixEnd_89095 := by exact prefixLift 89095
  have htrace : WordTrace (prefixWord ++ tailWord_89095) baseStart_89095 baseEnd_89095 := by
    simpa [prefixWord, tailWord_89095, baseEnd_89095] using wordTrace_append hprefix tailTrace_89095
  have hstable : (prefixWord ++ tailWord_89095).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_89095).length < 2 ^ (prefixWord ++ tailWord_89095).sum := by decide
  have hdescent : baseEnd_89095 < baseStart_89095 := by decide
  rcases family_descends (prefixWord ++ tailWord_89095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_89109 : List Nat := [1, 3, 2, 1, 4, 1, 3, 2, 3]
def baseStart_89109 : Nat := 118140960795 + 89109 * 2 ^ 59
def prefixEnd_89109 : Nat := 4983230072969 + 3 ^ 40 * 89109 * 2
def baseEnd_89109 : Nat := 40671775681419639402401

theorem tailTrace_89109 : CollatzResearch.WordTrace tailWord_89109 prefixEnd_89109 40671775681419639402401 := by
  unfold tailWord_89109
  simp only [CollatzResearch.WordTrace]
  refine ⟨3250072234180786450694381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2166714822787190967129587 3250072234180786450694381)
  ·
    refine ⟨1218777087817794919010393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3250072234180786450694381 1218777087817794919010393)
    ·
      refine ⟨914082815863346189257795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1218777087817794919010393 914082815863346189257795)
      ·
        refine ⟨1371124223795019283886693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 914082815863346189257795 1371124223795019283886693)
        ·
          refine ⟨257085791961566115728755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1371124223795019283886693 257085791961566115728755)
          ·
            refine ⟨385628687942349173593133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 257085791961566115728755 385628687942349173593133)
            ·
              refine ⟨144610757978380940097425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 385628687942349173593133 144610757978380940097425)
              ·
                refine ⟨108458068483785705073069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 144610757978380940097425 108458068483785705073069)
                ·
                  refine ⟨40671775681419639402401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 108458068483785705073069 40671775681419639402401)
                  ·
                    rfl

theorem cell20_89109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 3, 2, 3].length) (baseStart_89109 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_89109 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_89109 prefixEnd_89109 := by exact prefixLift 89109
  have htrace : WordTrace (prefixWord ++ tailWord_89109) baseStart_89109 baseEnd_89109 := by
    simpa [prefixWord, tailWord_89109, baseEnd_89109] using wordTrace_append hprefix tailTrace_89109
  have hstable : (prefixWord ++ tailWord_89109).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_89109).length < 2 ^ (prefixWord ++ tailWord_89109).sum := by decide
  have hdescent : baseEnd_89109 < baseStart_89109 := by decide
  rcases family_descends (prefixWord ++ tailWord_89109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_89137 : List Nat := [1, 2, 2, 3, 1, 2, 1, 4, 4]
def baseStart_89137 : Nat := 118140960795 + 89137 * 2 ^ 59
def prefixEnd_89137 : Nat := 4983230072969 + 3 ^ 40 * 89137 * 2
def baseEnd_89137 : Nat := 40684555644375986468953

theorem tailTrace_89137 : CollatzResearch.WordTrace tailWord_89137 prefixEnd_89137 40684555644375986468953 := by
  unfold tailWord_89137
  simp only [CollatzResearch.WordTrace]
  refine ⟨3251093478079347232713665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2167395652052898155142443 3251093478079347232713665)
  ·
    refine ⟨2438320108559510424535249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3251093478079347232713665 2438320108559510424535249)
    ·
      refine ⟨1828740081419632818401437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2438320108559510424535249 1828740081419632818401437)
      ·
        refine ⟨685777530532362306900539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1828740081419632818401437 685777530532362306900539)
        ·
          refine ⟨1028666295798543460350809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 685777530532362306900539 1028666295798543460350809)
          ·
            refine ⟨771499721848907595263107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1028666295798543460350809 771499721848907595263107)
            ·
              refine ⟨1157249582773361392894661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 771499721848907595263107 1157249582773361392894661)
              ·
                refine ⟨216984296770005261167749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1157249582773361392894661 216984296770005261167749)
                ·
                  refine ⟨40684555644375986468953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 216984296770005261167749 40684555644375986468953)
                  ·
                    rfl

theorem cell20_89137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 4, 4].length) (baseStart_89137 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_89137 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_89137 prefixEnd_89137 := by exact prefixLift 89137
  have htrace : WordTrace (prefixWord ++ tailWord_89137) baseStart_89137 baseEnd_89137 := by
    simpa [prefixWord, tailWord_89137, baseEnd_89137] using wordTrace_append hprefix tailTrace_89137
  have hstable : (prefixWord ++ tailWord_89137).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_89137).length < 2 ^ (prefixWord ++ tailWord_89137).sum := by decide
  have hdescent : baseEnd_89137 < baseStart_89137 := by decide
  rcases family_descends (prefixWord ++ tailWord_89137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_89140 : List Nat := [2, 5, 1, 2, 1, 2, 1, 6]
def baseStart_89140 : Nat := 118140960795 + 89140 * 2 ^ 59
def prefixEnd_89140 : Nat := 4983230072969 + 3 ^ 40 * 89140 * 2
def baseEnd_89140 : Nat := 13561974975373769789647

theorem tailTrace_89140 : CollatzResearch.WordTrace tailWord_89140 prefixEnd_89140 13561974975373769789647 := by
  unfold tailWord_89140
  simp only [CollatzResearch.WordTrace]
  refine ⟨1625601448534239372536437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2167468598045652496715249 1625601448534239372536437)
  ·
    refine ⟨152400135800084941175291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1625601448534239372536437 152400135800084941175291)
    ·
      refine ⟨228600203700127411762937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152400135800084941175291 228600203700127411762937)
      ·
        refine ⟨171450152775095558822203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 228600203700127411762937 171450152775095558822203)
        ·
          refine ⟨257175229162643338233305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 171450152775095558822203 257175229162643338233305)
          ·
            refine ⟨192881421871982503674979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 257175229162643338233305 192881421871982503674979)
            ·
              refine ⟨289322132807973755512469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 192881421871982503674979 289322132807973755512469)
              ·
                refine ⟨13561974975373769789647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 289322132807973755512469 13561974975373769789647)
                ·
                  rfl

theorem cell20_89140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 1, 6].length) (baseStart_89140 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_89140 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_89140 prefixEnd_89140 := by exact prefixLift 89140
  have htrace : WordTrace (prefixWord ++ tailWord_89140) baseStart_89140 baseEnd_89140 := by
    simpa [prefixWord, tailWord_89140, baseEnd_89140] using wordTrace_append hprefix tailTrace_89140
  have hstable : (prefixWord ++ tailWord_89140).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_89140).length < 2 ^ (prefixWord ++ tailWord_89140).sum := by decide
  have hdescent : baseEnd_89140 < baseStart_89140 := by decide
  rcases family_descends (prefixWord ++ tailWord_89140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_89150 : List Nat := [4, 2, 1, 3, 1, 1, 3, 3, 2]
def baseStart_89150 : Nat := 118140960795 + 89150 * 2 ^ 59
def prefixEnd_89150 : Nat := 4983230072969 + 3 ^ 40 * 89150 * 2
def baseEnd_89150 : Nat := 40690489198605719035567

theorem tailTrace_89150 : CollatzResearch.WordTrace tailWord_89150 prefixEnd_89150 40690489198605719035567 := by
  unfold tailWord_89150
  simp only [CollatzResearch.WordTrace]
  refine ⟨406445953379031306617113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2167711751354833635291269 406445953379031306617113)
  ·
    refine ⟨304834465034273479962835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 406445953379031306617113 304834465034273479962835)
    ·
      refine ⟨457251697551410219944253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 304834465034273479962835 457251697551410219944253)
      ·
        refine ⟨171469386581778832479095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 457251697551410219944253 171469386581778832479095)
        ·
          refine ⟨257204079872668248718643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 171469386581778832479095 257204079872668248718643)
          ·
            refine ⟨385806119809002373077965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 257204079872668248718643 385806119809002373077965)
            ·
              refine ⟨144677294928375889904237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 385806119809002373077965 144677294928375889904237)
              ·
                refine ⟨54253985598140958714089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 144677294928375889904237 54253985598140958714089)
                ·
                  refine ⟨40690489198605719035567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54253985598140958714089 40690489198605719035567)
                  ·
                    rfl

theorem cell20_89150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 3, 3, 2].length) (baseStart_89150 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_89150 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_89150 prefixEnd_89150 := by exact prefixLift 89150
  have htrace : WordTrace (prefixWord ++ tailWord_89150) baseStart_89150 baseEnd_89150 := by
    simpa [prefixWord, tailWord_89150, baseEnd_89150] using wordTrace_append hprefix tailTrace_89150
  have hstable : (prefixWord ++ tailWord_89150).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_89150).length < 2 ^ (prefixWord ++ tailWord_89150).sum := by decide
  have hdescent : baseEnd_89150 < baseStart_89150 := by decide
  rcases family_descends (prefixWord ++ tailWord_89150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_89185 : List Nat := [1, 2, 3, 1, 1, 2, 6, 1, 3]
def baseStart_89185 : Nat := 118140960795 + 89185 * 2 ^ 59
def prefixEnd_89185 : Nat := 4983230072969 + 3 ^ 40 * 89185 * 2
def baseEnd_89185 : Nat := 40706464152301152868757

theorem tailTrace_89185 : CollatzResearch.WordTrace tailWord_89185 prefixEnd_89185 40706464152301152868757 := by
  unfold tailWord_89185
  simp only [CollatzResearch.WordTrace]
  refine ⟨3252844181905451430461009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2168562787936967620307339 3252844181905451430461009)
  ·
    refine ⟨2439633136429088572845757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3252844181905451430461009 2439633136429088572845757)
    ·
      refine ⟨914862426160908214817159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2439633136429088572845757 914862426160908214817159)
      ·
        refine ⟨1372293639241362322225739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 914862426160908214817159 1372293639241362322225739)
        ·
          refine ⟨2058440458862043483338609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1372293639241362322225739 2058440458862043483338609)
          ·
            refine ⟨1543830344146532612503957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2058440458862043483338609 1543830344146532612503957)
            ·
              refine ⟨72367047381868716211123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1543830344146532612503957 72367047381868716211123)
              ·
                refine ⟨108550571072803074316685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72367047381868716211123 108550571072803074316685)
                ·
                  refine ⟨40706464152301152868757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 108550571072803074316685 40706464152301152868757)
                  ·
                    rfl

theorem cell20_89185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 6, 1, 3].length) (baseStart_89185 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_89185 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_89185 prefixEnd_89185 := by exact prefixLift 89185
  have htrace : WordTrace (prefixWord ++ tailWord_89185) baseStart_89185 baseEnd_89185 := by
    simpa [prefixWord, tailWord_89185, baseEnd_89185] using wordTrace_append hprefix tailTrace_89185
  have hstable : (prefixWord ++ tailWord_89185).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_89185).length < 2 ^ (prefixWord ++ tailWord_89185).sum := by decide
  have hdescent : baseEnd_89185 < baseStart_89185 := by decide
  rcases family_descends (prefixWord ++ tailWord_89185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_89220 : List Nat := [2, 3, 2, 1, 2, 10]
def baseStart_89220 : Nat := 118140960795 + 89220 * 2 ^ 59
def prefixEnd_89220 : Nat := 4983230072969 + 3 ^ 40 * 89220 * 2
def baseEnd_89220 : Nat := 1508238485407280988961

theorem tailTrace_89220 : CollatzResearch.WordTrace tailWord_89220 prefixEnd_89220 1508238485407280988961 := by
  unfold tailWord_89220
  simp only [CollatzResearch.WordTrace]
  refine ⟨1627060368389326203992557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2169413824519101605323409 1627060368389326203992557)
  ·
    refine ⟨610147638145997326497209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1627060368389326203992557 610147638145997326497209)
    ·
      refine ⟨457610728609497994872907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 610147638145997326497209 457610728609497994872907)
      ·
        refine ⟨686416092914246992309361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 457610728609497994872907 686416092914246992309361)
        ·
          refine ⟨514812069685685244232021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 686416092914246992309361 514812069685685244232021)
          ·
            refine ⟨1508238485407280988961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 514812069685685244232021 1508238485407280988961)
            ·
              rfl

theorem cell20_89220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 10].length) (baseStart_89220 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_89220 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_89220 prefixEnd_89220 := by exact prefixLift 89220
  have htrace : WordTrace (prefixWord ++ tailWord_89220) baseStart_89220 baseEnd_89220 := by
    simpa [prefixWord, tailWord_89220, baseEnd_89220] using wordTrace_append hprefix tailTrace_89220
  have hstable : (prefixWord ++ tailWord_89220).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_89220).length < 2 ^ (prefixWord ++ tailWord_89220).sum := by decide
  have hdescent : baseEnd_89220 < baseStart_89220 := by decide
  rcases family_descends (prefixWord ++ tailWord_89220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_89227 : List Nat := [1, 1, 1, 1, 4, 1, 1, 5, 5]
def baseStart_89227 : Nat := 118140960795 + 89227 * 2 ^ 59
def prefixEnd_89227 : Nat := 4983230072969 + 3 ^ 40 * 89227 * 2
def baseEnd_89227 : Nat := 40725634096735673468585

theorem tailTrace_89227 : CollatzResearch.WordTrace tailWord_89227 prefixEnd_89227 40725634096735673468585 := by
  unfold tailWord_89227
  simp only [CollatzResearch.WordTrace]
  refine ⟨3254376047753292603489935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2169584031835528402326623 3254376047753292603489935)
  ·
    refine ⟨4881564071629938905234903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3254376047753292603489935 4881564071629938905234903)
    ·
      refine ⟨7322346107444908357852355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4881564071629938905234903 7322346107444908357852355)
      ·
        refine ⟨10983519161167362536778533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7322346107444908357852355 10983519161167362536778533)
        ·
          refine ⟨2059409842718880475645975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10983519161167362536778533 2059409842718880475645975)
          ·
            refine ⟨3089114764078320713468963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2059409842718880475645975 3089114764078320713468963)
            ·
              refine ⟨4633672146117481070203445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3089114764078320713468963 4633672146117481070203445)
              ·
                refine ⟨434406763698513850331573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4633672146117481070203445 434406763698513850331573)
                ·
                  refine ⟨40725634096735673468585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 434406763698513850331573 40725634096735673468585)
                  ·
                    rfl

theorem cell20_89227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 5, 5].length) (baseStart_89227 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_89227 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_89227 prefixEnd_89227 := by exact prefixLift 89227
  have htrace : WordTrace (prefixWord ++ tailWord_89227) baseStart_89227 baseEnd_89227 := by
    simpa [prefixWord, tailWord_89227, baseEnd_89227] using wordTrace_append hprefix tailTrace_89227
  have hstable : (prefixWord ++ tailWord_89227).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_89227).length < 2 ^ (prefixWord ++ tailWord_89227).sum := by decide
  have hdescent : baseEnd_89227 < baseStart_89227 := by decide
  rcases family_descends (prefixWord ++ tailWord_89227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_89278 : List Nat := [4, 2, 1, 1, 3, 3, 1, 2, 3]
def baseStart_89278 : Nat := 118140960795 + 89278 * 2 ^ 59
def prefixEnd_89278 : Nat := 4983230072969 + 3 ^ 40 * 89278 * 2
def baseEnd_89278 : Nat := 40748911886406162768377

theorem tailTrace_89278 : CollatzResearch.WordTrace tailWord_89278 prefixEnd_89278 40748911886406162768377 := by
  unfold tailWord_89278
  simp only [CollatzResearch.WordTrace]
  refine ⟨407029521321066039199561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2170824113712352209064325 407029521321066039199561)
  ·
    refine ⟨305272140990799529399671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 407029521321066039199561 305272140990799529399671)
    ·
      refine ⟨457908211486199294099507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 305272140990799529399671 457908211486199294099507)
      ·
        refine ⟨686862317229298941149261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 457908211486199294099507 686862317229298941149261)
        ·
          refine ⟨257573368960987102930973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 686862317229298941149261 257573368960987102930973)
          ·
            refine ⟨96590013360370163599115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 257573368960987102930973 96590013360370163599115)
            ·
              refine ⟨144885020040555245398673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96590013360370163599115 144885020040555245398673)
              ·
                refine ⟨108663765030416434049005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 144885020040555245398673 108663765030416434049005)
                ·
                  refine ⟨40748911886406162768377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 108663765030416434049005 40748911886406162768377)
                  ·
                    rfl

theorem cell20_89278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 3, 1, 2, 3].length) (baseStart_89278 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_89278 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_89278 prefixEnd_89278 := by exact prefixLift 89278
  have htrace : WordTrace (prefixWord ++ tailWord_89278) baseStart_89278 baseEnd_89278 := by
    simpa [prefixWord, tailWord_89278, baseEnd_89278] using wordTrace_append hprefix tailTrace_89278
  have hstable : (prefixWord ++ tailWord_89278).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_89278).length < 2 ^ (prefixWord ++ tailWord_89278).sum := by decide
  have hdescent : baseEnd_89278 < baseStart_89278 := by decide
  rcases family_descends (prefixWord ++ tailWord_89278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_89309 : List Nat := [1, 4, 3, 2, 2, 2, 2, 4]
def baseStart_89309 : Nat := 118140960795 + 89309 * 2 ^ 59
def prefixEnd_89309 : Nat := 4983230072969 + 3 ^ 40 * 89309 * 2
def baseEnd_89309 : Nat := 13587687043702610911639

theorem tailTrace_89309 : CollatzResearch.WordTrace tailWord_89309 prefixEnd_89309 13587687043702610911639 := by
  unfold tailWord_89309
  simp only [CollatzResearch.WordTrace]
  refine ⟨3257366833456220607974981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2171577888970813738649987 3257366833456220607974981)
  ·
    refine ⟨610756281273041363995309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3257366833456220607974981 610756281273041363995309)
    ·
      refine ⟨229033605477390511498241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 610756281273041363995309 229033605477390511498241)
      ·
        refine ⟨171775204108042883623681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 229033605477390511498241 171775204108042883623681)
        ·
          refine ⟨128831403081032162717761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 171775204108042883623681 128831403081032162717761)
          ·
            refine ⟨96623552310774122038321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 128831403081032162717761 96623552310774122038321)
            ·
              refine ⟨72467664233080591528741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 96623552310774122038321 72467664233080591528741)
              ·
                refine ⟨13587687043702610911639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 72467664233080591528741 13587687043702610911639)
                ·
                  rfl

theorem cell20_89309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 2, 2, 4].length) (baseStart_89309 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_89309 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_89309 prefixEnd_89309 := by exact prefixLift 89309
  have htrace : WordTrace (prefixWord ++ tailWord_89309) baseStart_89309 baseEnd_89309 := by
    simpa [prefixWord, tailWord_89309, baseEnd_89309] using wordTrace_append hprefix tailTrace_89309
  have hstable : (prefixWord ++ tailWord_89309).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_89309).length < 2 ^ (prefixWord ++ tailWord_89309).sum := by decide
  have hdescent : baseEnd_89309 < baseStart_89309 := by decide
  rcases family_descends (prefixWord ++ tailWord_89309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_89313 : List Nat := [1, 2, 3, 1, 3, 2, 4, 4]
def baseStart_89313 : Nat := 118140960795 + 89313 * 2 ^ 59
def prefixEnd_89313 : Nat := 4983230072969 + 3 ^ 40 * 89313 * 2
def baseEnd_89313 : Nat := 13588295613367198867189

theorem tailTrace_89313 : CollatzResearch.WordTrace tailWord_89313 prefixEnd_89313 13588295613367198867189 := by
  unfold tailWord_89313
  simp only [CollatzResearch.WordTrace]
  refine ⟨3257512725441729291120593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2171675150294486194080395 3257512725441729291120593)
  ·
    refine ⟨2443134544081296968340445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3257512725441729291120593 2443134544081296968340445)
    ·
      refine ⟨916175454030486363127667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2443134544081296968340445 916175454030486363127667)
      ·
        refine ⟨1374263181045729544691501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 916175454030486363127667 1374263181045729544691501)
        ·
          refine ⟨515348692892148579259313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1374263181045729544691501 515348692892148579259313)
          ·
            refine ⟨386511519669111434444485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 515348692892148579259313 386511519669111434444485)
            ·
              refine ⟨72470909937958393958341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 386511519669111434444485 72470909937958393958341)
              ·
                refine ⟨13588295613367198867189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 72470909937958393958341 13588295613367198867189)
                ·
                  rfl

theorem cell20_89313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 4, 4].length) (baseStart_89313 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_89313 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_89313 prefixEnd_89313 := by exact prefixLift 89313
  have htrace : WordTrace (prefixWord ++ tailWord_89313) baseStart_89313 baseEnd_89313 := by
    simpa [prefixWord, tailWord_89313, baseEnd_89313] using wordTrace_append hprefix tailTrace_89313
  have hstable : (prefixWord ++ tailWord_89313).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_89313).length < 2 ^ (prefixWord ++ tailWord_89313).sum := by decide
  have hdescent : baseEnd_89313 < baseStart_89313 := by decide
  rcases family_descends (prefixWord ++ tailWord_89313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_89319 : List Nat := [1, 1, 5, 3, 3, 1, 1, 3, 2]
def baseStart_89319 : Nat := 118140960795 + 89319 * 2 ^ 59
def prefixEnd_89319 : Nat := 4983230072969 + 3 ^ 40 * 89319 * 2
def baseEnd_89319 : Nat := 40767625403592242401543

theorem tailTrace_89319 : CollatzResearch.WordTrace tailWord_89319 prefixEnd_89319 40767625403592242401543 := by
  unfold tailWord_89319
  simp only [CollatzResearch.WordTrace]
  refine ⟨3257731563419992315839011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2171821042279994877226007 3257731563419992315839011)
  ·
    refine ⟨4886597345129988473758517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3257731563419992315839011 4886597345129988473758517)
    ·
      refine ⟨458118501105936419414861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4886597345129988473758517 458118501105936419414861)
      ·
        refine ⟨171794437914726157280573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 458118501105936419414861 171794437914726157280573)
        ·
          refine ⟨64422914218022308980215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 171794437914726157280573 64422914218022308980215)
          ·
            refine ⟨96634371327033463470323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64422914218022308980215 96634371327033463470323)
            ·
              refine ⟨144951556990550195205485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96634371327033463470323 144951556990550195205485)
              ·
                refine ⟨54356833871456323202057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 144951556990550195205485 54356833871456323202057)
                ·
                  refine ⟨40767625403592242401543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54356833871456323202057 40767625403592242401543)
                  ·
                    rfl

theorem cell20_89319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 1, 1, 3, 2].length) (baseStart_89319 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_89319 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_89319 prefixEnd_89319 := by exact prefixLift 89319
  have htrace : WordTrace (prefixWord ++ tailWord_89319) baseStart_89319 baseEnd_89319 := by
    simpa [prefixWord, tailWord_89319, baseEnd_89319] using wordTrace_append hprefix tailTrace_89319
  have hstable : (prefixWord ++ tailWord_89319).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_89319).length < 2 ^ (prefixWord ++ tailWord_89319).sum := by decide
  have hdescent : baseEnd_89319 < baseStart_89319 := by decide
  rcases family_descends (prefixWord ++ tailWord_89319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_89323 : List Nat := [1, 1, 1, 1, 2, 8, 1, 3, 2]
def baseStart_89323 : Nat := 118140960795 + 89323 * 2 ^ 59
def prefixEnd_89323 : Nat := 4983230072969 + 3 ^ 40 * 89323 * 2
def baseEnd_89323 : Nat := 40769451112586006268193

theorem tailTrace_89323 : CollatzResearch.WordTrace tailWord_89323 prefixEnd_89323 40769451112586006268193 := by
  unfold tailWord_89323
  simp only [CollatzResearch.WordTrace]
  refine ⟨3257877455405500998984623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2171918303603667332656415 3257877455405500998984623)
  ·
    refine ⟨4886816183108251498476935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3257877455405500998984623 4886816183108251498476935)
    ·
      refine ⟨7330224274662377247715403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4886816183108251498476935 7330224274662377247715403)
      ·
        refine ⟨10995336411993565871573105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7330224274662377247715403 10995336411993565871573105)
        ·
          refine ⟨8246502308995174403679829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10995336411993565871573105 8246502308995174403679829)
          ·
            refine ⟨96638698933537200043123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 8246502308995174403679829 96638698933537200043123)
            ·
              refine ⟨144958048400305800064685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96638698933537200043123 144958048400305800064685)
              ·
                refine ⟨54359268150114675024257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 144958048400305800064685 54359268150114675024257)
                ·
                  refine ⟨40769451112586006268193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54359268150114675024257 40769451112586006268193)
                  ·
                    rfl

theorem cell20_89323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 8, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 8, 1, 3, 2].length) (baseStart_89323 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_89323 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_89323 prefixEnd_89323 := by exact prefixLift 89323
  have htrace : WordTrace (prefixWord ++ tailWord_89323) baseStart_89323 baseEnd_89323 := by
    simpa [prefixWord, tailWord_89323, baseEnd_89323] using wordTrace_append hprefix tailTrace_89323
  have hstable : (prefixWord ++ tailWord_89323).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_89323).length < 2 ^ (prefixWord ++ tailWord_89323).sum := by decide
  have hdescent : baseEnd_89323 < baseStart_89323 := by decide
  rcases family_descends (prefixWord ++ tailWord_89323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_89330 : List Nat := [3, 2, 1, 3, 4, 1, 6]
def baseStart_89330 : Nat := 118140960795 + 89330 * 2 ^ 59
def prefixEnd_89330 : Nat := 4983230072969 + 3 ^ 40 * 89330 * 2
def baseEnd_89330 : Nat := 4530294011480565892759

theorem tailTrace_89330 : CollatzResearch.WordTrace tailWord_89330 prefixEnd_89330 4530294011480565892759 := by
  unfold tailWord_89330
  simp only [CollatzResearch.WordTrace]
  refine ⟨814533191595035298622361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2172088510920094129659629 814533191595035298622361)
  ·
    refine ⟨610899893696276473966771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 814533191595035298622361 610899893696276473966771)
    ·
      refine ⟨916349840544414710950157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 610899893696276473966771 916349840544414710950157)
      ·
        refine ⟨343631190204155516606309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 916349840544414710950157 343631190204155516606309)
        ·
          refine ⟨64430848163279159363683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 343631190204155516606309 64430848163279159363683)
          ·
            refine ⟨96646272244918739045525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64430848163279159363683 96646272244918739045525)
            ·
              refine ⟨4530294011480565892759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 96646272244918739045525 4530294011480565892759)
              ·
                rfl

theorem cell20_89330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 1, 6].length) (baseStart_89330 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_89330 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_89330 prefixEnd_89330 := by exact prefixLift 89330
  have htrace : WordTrace (prefixWord ++ tailWord_89330) baseStart_89330 baseEnd_89330 := by
    simpa [prefixWord, tailWord_89330, baseEnd_89330] using wordTrace_append hprefix tailTrace_89330
  have hstable : (prefixWord ++ tailWord_89330).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_89330).length < 2 ^ (prefixWord ++ tailWord_89330).sum := by decide
  have hdescent : baseEnd_89330 < baseStart_89330 := by decide
  rcases family_descends (prefixWord ++ tailWord_89330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_89340 : List Nat := [2, 2, 2, 1, 5, 1, 3, 2, 2]
def baseStart_89340 : Nat := 118140960795 + 89340 * 2 ^ 59
def prefixEnd_89340 : Nat := 4983230072969 + 3 ^ 40 * 89340 * 2
def baseEnd_89340 : Nat := 40777210375809502701457

theorem tailTrace_89340 : CollatzResearch.WordTrace tailWord_89340 prefixEnd_89340 40777210375809502701457 := by
  unfold tailWord_89340
  simp only [CollatzResearch.WordTrace]
  refine ⟨1629248748171956451176737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2172331664229275268235649 1629248748171956451176737)
  ·
    refine ⟨1221936561128967338382553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1629248748171956451176737 1221936561128967338382553)
    ·
      refine ⟨916452420846725503786915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1221936561128967338382553 916452420846725503786915)
      ·
        refine ⟨1374678631270088255680373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 916452420846725503786915 1374678631270088255680373)
        ·
          refine ⟨128876121681570773970035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1374678631270088255680373 128876121681570773970035)
          ·
            refine ⟨193314182522356160955053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128876121681570773970035 193314182522356160955053)
            ·
              refine ⟨72492818445883560358145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 193314182522356160955053 72492818445883560358145)
              ·
                refine ⟨54369613834412670268609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72492818445883560358145 54369613834412670268609)
                ·
                  refine ⟨40777210375809502701457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54369613834412670268609 40777210375809502701457)
                  ·
                    rfl

theorem cell20_89340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 3, 2, 2].length) (baseStart_89340 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_89340 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_89340 prefixEnd_89340 := by exact prefixLift 89340
  have htrace : WordTrace (prefixWord ++ tailWord_89340) baseStart_89340 baseEnd_89340 := by
    simpa [prefixWord, tailWord_89340, baseEnd_89340] using wordTrace_append hprefix tailTrace_89340
  have hstable : (prefixWord ++ tailWord_89340).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_89340).length < 2 ^ (prefixWord ++ tailWord_89340).sum := by decide
  have hdescent : baseEnd_89340 < baseStart_89340 := by decide
  rcases family_descends (prefixWord ++ tailWord_89340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_89372 : List Nat := [2, 2, 3, 1, 1, 1, 4, 6]
def baseStart_89372 : Nat := 118140960795 + 89372 * 2 ^ 59
def prefixEnd_89372 : Nat := 4983230072969 + 3 ^ 40 * 89372 * 2
def baseEnd_89372 : Nat := 13597272015919871211553

theorem tailTrace_89372 : CollatzResearch.WordTrace tailWord_89372 prefixEnd_89372 13597272015919871211553 := by
  unfold tailWord_89372
  simp only [CollatzResearch.WordTrace]
  refine ⟨1629832316113991183759185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2173109754818654911678913 1629832316113991183759185)
  ·
    refine ⟨1222374237085493387819389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1629832316113991183759185 1222374237085493387819389)
    ·
      refine ⟨458390338907060020432271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1222374237085493387819389 458390338907060020432271)
      ·
        refine ⟨687585508360590030648407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 458390338907060020432271 687585508360590030648407)
        ·
          refine ⟨1031378262540885045972611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 687585508360590030648407 1031378262540885045972611)
          ·
            refine ⟨1547067393811327568958917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1031378262540885045972611 1547067393811327568958917)
            ·
              refine ⟨290075136339623919179797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1547067393811327568958917 290075136339623919179797)
              ·
                refine ⟨13597272015919871211553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 290075136339623919179797 13597272015919871211553)
                ·
                  rfl

theorem cell20_89372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 4, 6].length) (baseStart_89372 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_89372 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_89372 prefixEnd_89372 := by exact prefixLift 89372
  have htrace : WordTrace (prefixWord ++ tailWord_89372) baseStart_89372 baseEnd_89372 := by
    simpa [prefixWord, tailWord_89372, baseEnd_89372] using wordTrace_append hprefix tailTrace_89372
  have hstable : (prefixWord ++ tailWord_89372).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_89372).length < 2 ^ (prefixWord ++ tailWord_89372).sum := by decide
  have hdescent : baseEnd_89372 < baseStart_89372 := by decide
  rcases family_descends (prefixWord ++ tailWord_89372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_89389 : List Nat := [1, 5, 3, 1, 1, 9]
def baseStart_89389 : Nat := 118140960795 + 89389 * 2 ^ 59
def prefixEnd_89389 : Nat := 4983230072969 + 3 ^ 40 * 89389 * 2
def baseEnd_89389 : Nat := 1511095381888263335849

theorem tailTrace_89389 : CollatzResearch.WordTrace tailWord_89389 prefixEnd_89389 1511095381888263335849 := by
  unfold tailWord_89389
  simp only [CollatzResearch.WordTrace]
  refine ⟨3260284673166394270887221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2173523115444262847258147 3260284673166394270887221)
  ·
    refine ⟨305651688109349462895677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3260284673166394270887221 305651688109349462895677)
    ·
      refine ⟨114619383041006048585879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 305651688109349462895677 114619383041006048585879)
      ·
        refine ⟨171929074561509072878819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114619383041006048585879 171929074561509072878819)
        ·
          refine ⟨257893611842263609318229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 171929074561509072878819 257893611842263609318229)
          ·
            refine ⟨1511095381888263335849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 257893611842263609318229 1511095381888263335849)
            ·
              rfl

theorem cell20_89389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 9].length) (baseStart_89389 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_89389 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_89389 prefixEnd_89389 := by exact prefixLift 89389
  have htrace : WordTrace (prefixWord ++ tailWord_89389) baseStart_89389 baseEnd_89389 := by
    simpa [prefixWord, tailWord_89389, baseEnd_89389] using wordTrace_append hprefix tailTrace_89389
  have hstable : (prefixWord ++ tailWord_89389).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_89389).length < 2 ^ (prefixWord ++ tailWord_89389).sum := by decide
  have hdescent : baseEnd_89389 < baseStart_89389 := by decide
  rcases family_descends (prefixWord ++ tailWord_89389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_89455 : List Nat := [1, 1, 2, 1, 3, 1, 5, 1, 5]
def baseStart_89455 : Nat := 118140960795 + 89455 * 2 ^ 59
def prefixEnd_89455 : Nat := 4983230072969 + 3 ^ 40 * 89455 * 2
def baseEnd_89455 : Nat := 40829699509380213867653

theorem tailTrace_89455 : CollatzResearch.WordTrace tailWord_89455 prefixEnd_89455 40829699509380213867653 := by
  unfold tailWord_89455
  simp only [CollatzResearch.WordTrace]
  refine ⟨3262691890927287542789819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2175127927284858361859879 3262691890927287542789819)
  ·
    refine ⟨4894037836390931314184729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3262691890927287542789819 4894037836390931314184729)
    ·
      refine ⟨3670528377293198485638547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4894037836390931314184729 3670528377293198485638547)
      ·
        refine ⟨5505792565939797728457821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3670528377293198485638547 5505792565939797728457821)
        ·
          refine ⟨2064672212227424148171683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5505792565939797728457821 2064672212227424148171683)
          ·
            refine ⟨3097008318341136222257525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2064672212227424148171683 3097008318341136222257525)
            ·
              refine ⟨290344529844481520836643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3097008318341136222257525 290344529844481520836643)
              ·
                refine ⟨435516794766722281254965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 290344529844481520836643 435516794766722281254965)
                ·
                  refine ⟨40829699509380213867653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 435516794766722281254965 40829699509380213867653)
                  ·
                    rfl

theorem cell20_89455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 5, 1, 5].length) (baseStart_89455 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_89455 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_89455 prefixEnd_89455 := by exact prefixLift 89455
  have htrace : WordTrace (prefixWord ++ tailWord_89455) baseStart_89455 baseEnd_89455 := by
    simpa [prefixWord, tailWord_89455, baseEnd_89455] using wordTrace_append hprefix tailTrace_89455
  have hstable : (prefixWord ++ tailWord_89455).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_89455).length < 2 ^ (prefixWord ++ tailWord_89455).sum := by decide
  have hdescent : baseEnd_89455 < baseStart_89455 := by decide
  rcases family_descends (prefixWord ++ tailWord_89455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_89458 : List Nat := [3, 2, 1, 2, 1, 2, 1, 6, 2]
def baseStart_89458 : Nat := 118140960795 + 89458 * 2 ^ 59
def prefixEnd_89458 : Nat := 4983230072969 + 3 ^ 40 * 89458 * 2
def baseEnd_89458 : Nat := 40831068791125536767641

theorem tailTrace_89458 : CollatzResearch.WordTrace tailWord_89458 prefixEnd_89458 40831068791125536767641 := by
  unfold tailWord_89458
  simp only [CollatzResearch.WordTrace]
  refine ⟨815700327479104763787257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2175200873277612703432685 815700327479104763787257)
  ·
    refine ⟨611775245609328572840443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 815700327479104763787257 611775245609328572840443)
    ·
      refine ⟨917662868413992859260665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 611775245609328572840443 917662868413992859260665)
      ·
        refine ⟨688247151310494644445499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 917662868413992859260665 688247151310494644445499)
        ·
          refine ⟨1032370726965741966668249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 688247151310494644445499 1032370726965741966668249)
          ·
            refine ⟨774278045224306475001187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1032370726965741966668249 774278045224306475001187)
            ·
              refine ⟨1161417067836459712501781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 774278045224306475001187 1161417067836459712501781)
              ·
                refine ⟨54441425054834049023521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1161417067836459712501781 54441425054834049023521)
                ·
                  refine ⟨40831068791125536767641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54441425054834049023521 40831068791125536767641)
                  ·
                    rfl

theorem cell20_89458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 6, 2].length) (baseStart_89458 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_89458 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_89458 prefixEnd_89458 := by exact prefixLift 89458
  have htrace : WordTrace (prefixWord ++ tailWord_89458) baseStart_89458 baseEnd_89458 := by
    simpa [prefixWord, tailWord_89458, baseEnd_89458] using wordTrace_append hprefix tailTrace_89458
  have hstable : (prefixWord ++ tailWord_89458).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_89458).length < 2 ^ (prefixWord ++ tailWord_89458).sum := by decide
  have hdescent : baseEnd_89458 < baseStart_89458 := by decide
  rcases family_descends (prefixWord ++ tailWord_89458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_89479 : List Nat := [1, 1, 4, 2, 2, 2, 2, 2, 4]
def baseStart_89479 : Nat := 118140960795 + 89479 * 2 ^ 59
def prefixEnd_89479 : Nat := 4983230072969 + 3 ^ 40 * 89479 * 2
def baseEnd_89479 : Nat := 40840653763342797067555

theorem tailTrace_89479 : CollatzResearch.WordTrace tailWord_89479 prefixEnd_89479 40840653763342797067555 := by
  unfold tailWord_89479
  simp only [CollatzResearch.WordTrace]
  refine ⟨3263567242840339641663491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2175711495226893094442327 3263567242840339641663491)
  ·
    refine ⟨4895350864260509462495237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3263567242840339641663491 4895350864260509462495237)
    ·
      refine ⟨917878287048845524217857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4895350864260509462495237 917878287048845524217857)
      ·
        refine ⟨688408715286634143163393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 917878287048845524217857 688408715286634143163393)
        ·
          refine ⟨516306536464975607372545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 688408715286634143163393 516306536464975607372545)
          ·
            refine ⟨387229902348731705529409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 516306536464975607372545 387229902348731705529409)
            ·
              refine ⟨290422426761548779147057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 387229902348731705529409 290422426761548779147057)
              ·
                refine ⟨217816820071161584360293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 290422426761548779147057 217816820071161584360293)
                ·
                  refine ⟨40840653763342797067555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 217816820071161584360293 40840653763342797067555)
                  ·
                    rfl

theorem cell20_89479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 2, 2, 4].length) (baseStart_89479 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_89479 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_89479 prefixEnd_89479 := by exact prefixLift 89479
  have htrace : WordTrace (prefixWord ++ tailWord_89479) baseStart_89479 baseEnd_89479 := by
    simpa [prefixWord, tailWord_89479, baseEnd_89479] using wordTrace_append hprefix tailTrace_89479
  have hstable : (prefixWord ++ tailWord_89479).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_89479).length < 2 ^ (prefixWord ++ tailWord_89479).sum := by decide
  have hdescent : baseEnd_89479 < baseStart_89479 := by decide
  rcases family_descends (prefixWord ++ tailWord_89479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_89492 : List Nat := [2, 4, 2, 1, 2, 3, 1, 3, 2]
def baseStart_89492 : Nat := 118140960795 + 89492 * 2 ^ 59
def prefixEnd_89492 : Nat := 4983230072969 + 3 ^ 40 * 89492 * 2
def baseEnd_89492 : Nat := 40846587317572529634169

theorem tailTrace_89492 : CollatzResearch.WordTrace tailWord_89492 prefixEnd_89492 40846587317572529634169 := by
  unfold tailWord_89492
  simp only [CollatzResearch.WordTrace]
  refine ⟨1632020695896621430943365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2176027594528828574591153 1632020695896621430943365)
  ·
    refine ⟨306003880480616518301881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1632020695896621430943365 306003880480616518301881)
    ·
      refine ⟨229502910360462388726411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 306003880480616518301881 229502910360462388726411)
      ·
        refine ⟨344254365540693583089617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 229502910360462388726411 344254365540693583089617)
        ·
          refine ⟨258190774155520187317213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 344254365540693583089617 258190774155520187317213)
          ·
            refine ⟨96821540308320070243955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 258190774155520187317213 96821540308320070243955)
            ·
              refine ⟨145232310462480105365933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96821540308320070243955 145232310462480105365933)
              ·
                refine ⟨54462116423430039512225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 145232310462480105365933 54462116423430039512225)
                ·
                  refine ⟨40846587317572529634169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54462116423430039512225 40846587317572529634169)
                  ·
                    rfl

theorem cell20_89492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 3, 1, 3, 2].length) (baseStart_89492 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_89492 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_89492 prefixEnd_89492 := by exact prefixLift 89492
  have htrace : WordTrace (prefixWord ++ tailWord_89492) baseStart_89492 baseEnd_89492 := by
    simpa [prefixWord, tailWord_89492, baseEnd_89492] using wordTrace_append hprefix tailTrace_89492
  have hstable : (prefixWord ++ tailWord_89492).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_89492).length < 2 ^ (prefixWord ++ tailWord_89492).sum := by decide
  have hdescent : baseEnd_89492 < baseStart_89492 := by decide
  rcases family_descends (prefixWord ++ tailWord_89492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_89493 : List Nat := [1, 3, 2, 1, 1, 2, 3, 2, 5]
def baseStart_89493 : Nat := 118140960795 + 89493 * 2 ^ 59
def prefixEnd_89493 : Nat := 4983230072969 + 3 ^ 40 * 89493 * 2
def baseEnd_89493 : Nat := 40847043744820970600831

theorem tailTrace_89493 : CollatzResearch.WordTrace tailWord_89493 prefixEnd_89493 40847043744820970600831 := by
  unfold tailWord_89493
  simp only [CollatzResearch.WordTrace]
  refine ⟨3264077864789620032673133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2176051909859746688448755 3264077864789620032673133)
  ·
    refine ⟨1224029199296107512252425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3264077864789620032673133 1224029199296107512252425)
    ·
      refine ⟨918021899472080634189319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1224029199296107512252425 918021899472080634189319)
      ·
        refine ⟨1377032849208120951283979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 918021899472080634189319 1377032849208120951283979)
        ·
          refine ⟨2065549273812181426925969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1377032849208120951283979 2065549273812181426925969)
          ·
            refine ⟨1549161955359136070194477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2065549273812181426925969 1549161955359136070194477)
            ·
              refine ⟨580935733259676026322929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1549161955359136070194477 580935733259676026322929)
              ·
                refine ⟨435701799944757019742197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 580935733259676026322929 435701799944757019742197)
                ·
                  refine ⟨40847043744820970600831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 435701799944757019742197 40847043744820970600831)
                  ·
                    rfl

theorem cell20_89493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 2, 5].length) (baseStart_89493 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_89493 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_89493 prefixEnd_89493 := by exact prefixLift 89493
  have htrace : WordTrace (prefixWord ++ tailWord_89493) baseStart_89493 baseEnd_89493 := by
    simpa [prefixWord, tailWord_89493, baseEnd_89493] using wordTrace_append hprefix tailTrace_89493
  have hstable : (prefixWord ++ tailWord_89493).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_89493).length < 2 ^ (prefixWord ++ tailWord_89493).sum := by decide
  have hdescent : baseEnd_89493 < baseStart_89493 := by decide
  rcases family_descends (prefixWord ++ tailWord_89493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_89565 : List Nat := [1, 4, 3, 1, 1, 3, 2, 2, 3]
def baseStart_89565 : Nat := 118140960795 + 89565 * 2 ^ 59
def prefixEnd_89565 : Nat := 4983230072969 + 3 ^ 40 * 89565 * 2
def baseEnd_89565 : Nat := 40879906506708720200537

theorem tailTrace_89565 : CollatzResearch.WordTrace tailWord_89565 prefixEnd_89565 40879906506708720200537 := by
  unfold tailWord_89565
  simp only [CollatzResearch.WordTrace]
  refine ⟨3266703920528776329294149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2177802613685850886196099 3266703920528776329294149)
  ·
    refine ⟨612506985099145561742653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3266703920528776329294149 612506985099145561742653)
    ·
      refine ⟨229690119412179585653495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 612506985099145561742653 229690119412179585653495)
      ·
        refine ⟨344535179118269378480243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 229690119412179585653495 344535179118269378480243)
        ·
          refine ⟨516802768677404067720365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 344535179118269378480243 516802768677404067720365)
          ·
            refine ⟨193801038254026525395137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 516802768677404067720365 193801038254026525395137)
            ·
              refine ⟨145350778690519894046353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 193801038254026525395137 145350778690519894046353)
              ·
                refine ⟨109013084017889920534765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 145350778690519894046353 109013084017889920534765)
                ·
                  refine ⟨40879906506708720200537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 109013084017889920534765 40879906506708720200537)
                  ·
                    rfl

theorem cell20_89565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 2, 2, 3].length) (baseStart_89565 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_89565 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_89565 prefixEnd_89565 := by exact prefixLift 89565
  have htrace : WordTrace (prefixWord ++ tailWord_89565) baseStart_89565 baseEnd_89565 := by
    simpa [prefixWord, tailWord_89565, baseEnd_89565] using wordTrace_append hprefix tailTrace_89565
  have hstable : (prefixWord ++ tailWord_89565).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_89565).length < 2 ^ (prefixWord ++ tailWord_89565).sum := by decide
  have hdescent : baseEnd_89565 < baseStart_89565 := by decide
  rcases family_descends (prefixWord ++ tailWord_89565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_89610 : List Nat := [3, 1, 2, 2, 2, 2, 1, 5, 2]
def baseStart_89610 : Nat := 118140960795 + 89610 * 2 ^ 59
def prefixEnd_89610 : Nat := 4983230072969 + 3 ^ 40 * 89610 * 2
def baseEnd_89610 : Nat := 40900445732888563700353

theorem tailTrace_89610 : CollatzResearch.WordTrace tailWord_89610 prefixEnd_89610 40900445732888563700353 := by
  unfold tailWord_89610
  simp only [CollatzResearch.WordTrace]
  refine ⟨817086301341437253670571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2178896803577166009788189 817086301341437253670571)
  ·
    refine ⟨1225629452012155880505857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 817086301341437253670571 1225629452012155880505857)
    ·
      refine ⟨919222089009116910379393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1225629452012155880505857 919222089009116910379393)
      ·
        refine ⟨689416566756837682784545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 919222089009116910379393 689416566756837682784545)
        ·
          refine ⟨517062425067628262088409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 689416566756837682784545 517062425067628262088409)
          ·
            refine ⟨387796818800721196566307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 517062425067628262088409 387796818800721196566307)
            ·
              refine ⟨581695228201081794849461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 387796818800721196566307 581695228201081794849461)
              ·
                refine ⟨54533927643851418267137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 581695228201081794849461 54533927643851418267137)
                ·
                  refine ⟨40900445732888563700353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54533927643851418267137 40900445732888563700353)
                  ·
                    rfl

theorem cell20_89610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 5, 2].length) (baseStart_89610 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_89610 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_89610 prefixEnd_89610 := by exact prefixLift 89610
  have htrace : WordTrace (prefixWord ++ tailWord_89610) baseStart_89610 baseEnd_89610 := by
    simpa [prefixWord, tailWord_89610, baseEnd_89610] using wordTrace_append hprefix tailTrace_89610
  have hstable : (prefixWord ++ tailWord_89610).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_89610).length < 2 ^ (prefixWord ++ tailWord_89610).sum := by decide
  have hdescent : baseEnd_89610 < baseStart_89610 := by decide
  rcases family_descends (prefixWord ++ tailWord_89610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_89624 : List Nat := [2, 1, 2, 3, 4, 1, 1, 1, 5]
def baseStart_89624 : Nat := 118140960795 + 89624 * 2 ^ 59
def prefixEnd_89624 : Nat := 4983230072969 + 3 ^ 40 * 89624 * 2
def baseEnd_89624 : Nat := 40906835714366737233629

theorem tailTrace_89624 : CollatzResearch.WordTrace tailWord_89624 prefixEnd_89624 40906835714366737233629 := by
  unfold tailWord_89624
  simp only [CollatzResearch.WordTrace]
  refine ⟨1634427913657514702845963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2179237218210019603794617 1634427913657514702845963)
  ·
    refine ⟨2451641870486272054268945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1634427913657514702845963 2451641870486272054268945)
    ·
      refine ⟨1838731402864704040701709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2451641870486272054268945 1838731402864704040701709)
      ·
        refine ⟨689524276074264015263141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1838731402864704040701709 689524276074264015263141)
        ·
          refine ⟨129285801763924502861839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 689524276074264015263141 129285801763924502861839)
          ·
            refine ⟨193928702645886754292759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129285801763924502861839 193928702645886754292759)
            ·
              refine ⟨290893053968830131439139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 193928702645886754292759 290893053968830131439139)
              ·
                refine ⟨436339580953245197158709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 290893053968830131439139 436339580953245197158709)
                ·
                  refine ⟨40906835714366737233629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 436339580953245197158709 40906835714366737233629)
                  ·
                    rfl

theorem cell20_89624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 1, 1, 5].length) (baseStart_89624 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_89624 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_89624 prefixEnd_89624 := by exact prefixLift 89624
  have htrace : WordTrace (prefixWord ++ tailWord_89624) baseStart_89624 baseEnd_89624 := by
    simpa [prefixWord, tailWord_89624, baseEnd_89624] using wordTrace_append hprefix tailTrace_89624
  have hstable : (prefixWord ++ tailWord_89624).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_89624).length < 2 ^ (prefixWord ++ tailWord_89624).sum := by decide
  have hdescent : baseEnd_89624 < baseStart_89624 := by decide
  rcases family_descends (prefixWord ++ tailWord_89624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_89655 : List Nat := [1, 1, 3, 1, 2, 6, 2, 4]
def baseStart_89655 : Nat := 118140960795 + 89655 * 2 ^ 59
def prefixEnd_89655 : Nat := 4983230072969 + 3 ^ 40 * 89655 * 2
def baseEnd_89655 : Nat := 13640328319689469066723

theorem tailTrace_89655 : CollatzResearch.WordTrace tailWord_89655 prefixEnd_89655 13640328319689469066723 := by
  unfold tailWord_89655
  simp only [CollatzResearch.WordTrace]
  refine ⟨3269986490202721700070419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2179990993468481133380279 3269986490202721700070419)
  ·
    refine ⟨4904979735304082550105629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3269986490202721700070419 4904979735304082550105629)
    ·
      refine ⟨1839367400739030956289611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4904979735304082550105629 1839367400739030956289611)
      ·
        refine ⟨2759051101108546434434417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1839367400739030956289611 2759051101108546434434417)
        ·
          refine ⟨2069288325831409825825813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2759051101108546434434417 2069288325831409825825813)
          ·
            refine ⟨96997890273347335585585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 2069288325831409825825813 96997890273347335585585)
            ·
              refine ⟨72748417705010501689189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 96997890273347335585585 72748417705010501689189)
              ·
                refine ⟨13640328319689469066723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 72748417705010501689189 13640328319689469066723)
                ·
                  rfl

theorem cell20_89655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 6, 2, 4].length) (baseStart_89655 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_89655 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_89655 prefixEnd_89655 := by exact prefixLift 89655
  have htrace : WordTrace (prefixWord ++ tailWord_89655) baseStart_89655 baseEnd_89655 := by
    simpa [prefixWord, tailWord_89655, baseEnd_89655] using wordTrace_append hprefix tailTrace_89655
  have hstable : (prefixWord ++ tailWord_89655).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_89655).length < 2 ^ (prefixWord ++ tailWord_89655).sum := by decide
  have hdescent : baseEnd_89655 < baseStart_89655 := by decide
  rcases family_descends (prefixWord ++ tailWord_89655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_89676 : List Nat := [2, 2, 1, 3, 1, 5, 6]
def baseStart_89676 : Nat := 118140960795 + 89676 * 2 ^ 59
def prefixEnd_89676 : Nat := 4983230072969 + 3 ^ 40 * 89676 * 2
def baseEnd_89676 : Nat := 4547841103476185277787

theorem tailTrace_89676 : CollatzResearch.WordTrace tailWord_89676 prefixEnd_89676 4547841103476185277787 := by
  unfold tailWord_89676
  simp only [CollatzResearch.WordTrace]
  refine ⟨1635376211563321143292441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2180501615417761524389921 1635376211563321143292441)
  ·
    refine ⟨1226532158672490857469331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1635376211563321143292441 1226532158672490857469331)
    ·
      refine ⟨1839798238008736286203997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1226532158672490857469331 1839798238008736286203997)
      ·
        refine ⟨689924339253276107326499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1839798238008736286203997 689924339253276107326499)
        ·
          refine ⟨1034886508879914160989749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 689924339253276107326499 1034886508879914160989749)
          ·
            refine ⟨97020610207491952592789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1034886508879914160989749 97020610207491952592789)
            ·
              refine ⟨4547841103476185277787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 97020610207491952592789 4547841103476185277787)
              ·
                rfl

theorem cell20_89676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 5, 6].length) (baseStart_89676 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_89676 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_89676 prefixEnd_89676 := by exact prefixLift 89676
  have htrace : WordTrace (prefixWord ++ tailWord_89676) baseStart_89676 baseEnd_89676 := by
    simpa [prefixWord, tailWord_89676, baseEnd_89676] using wordTrace_append hprefix tailTrace_89676
  have hstable : (prefixWord ++ tailWord_89676).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_89676).length < 2 ^ (prefixWord ++ tailWord_89676).sum := by decide
  have hdescent : baseEnd_89676 < baseStart_89676 := by decide
  rcases family_descends (prefixWord ++ tailWord_89676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_89700 : List Nat := [2, 3, 1, 1, 2, 4, 1, 3, 3]
def baseStart_89700 : Nat := 118140960795 + 89700 * 2 ^ 59
def prefixEnd_89700 : Nat := 4983230072969 + 3 ^ 40 * 89700 * 2
def baseEnd_89700 : Nat := 40941524185248250699985

theorem tailTrace_89700 : CollatzResearch.WordTrace tailWord_89700 prefixEnd_89700 40941524185248250699985 := by
  unfold tailWord_89700
  simp only [CollatzResearch.WordTrace]
  refine ⟨1635813887519847192729277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2181085183359796256972369 1635813887519847192729277)
  ·
    refine ⟨613430207819942697273479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1635813887519847192729277 613430207819942697273479)
    ·
      refine ⟨920145311729914045910219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 613430207819942697273479 920145311729914045910219)
      ·
        refine ⟨1380217967594871068865329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 920145311729914045910219 1380217967594871068865329)
        ·
          refine ⟨1035163475696153301648997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1380217967594871068865329 1035163475696153301648997)
          ·
            refine ⟨194093151693028744059187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1035163475696153301648997 194093151693028744059187)
            ·
              refine ⟨291139727539543116088781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 194093151693028744059187 291139727539543116088781)
              ·
                refine ⟨109177397827328668533293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 291139727539543116088781 109177397827328668533293)
                ·
                  refine ⟨40941524185248250699985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 109177397827328668533293 40941524185248250699985)
                  ·
                    rfl

theorem cell20_89700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 1, 3, 3].length) (baseStart_89700 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_89700 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_89700 prefixEnd_89700 := by exact prefixLift 89700
  have htrace : WordTrace (prefixWord ++ tailWord_89700) baseStart_89700 baseEnd_89700 := by
    simpa [prefixWord, tailWord_89700, baseEnd_89700] using wordTrace_append hprefix tailTrace_89700
  have hstable : (prefixWord ++ tailWord_89700).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_89700).length < 2 ^ (prefixWord ++ tailWord_89700).sum := by decide
  have hdescent : baseEnd_89700 < baseStart_89700 := by decide
  rcases family_descends (prefixWord ++ tailWord_89700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_89714 : List Nat := [3, 2, 1, 2, 3, 1, 2, 6]
def baseStart_89714 : Nat := 118140960795 + 89714 * 2 ^ 59
def prefixEnd_89714 : Nat := 4983230072969 + 3 ^ 40 * 89714 * 2
def baseEnd_89714 : Nat := 13649304722242141411087

theorem tailTrace_89714 : CollatzResearch.WordTrace tailWord_89714 prefixEnd_89714 13649304722242141411087 := by
  unfold tailWord_89714
  simp only [CollatzResearch.WordTrace]
  refine ⟨818034599247243694117049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2181425597992649850978797 818034599247243694117049)
  ·
    refine ⟨613525949435432770587787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 818034599247243694117049 613525949435432770587787)
    ·
      refine ⟨920288924153149155881681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 613525949435432770587787 920288924153149155881681)
      ·
        refine ⟨690216693114861866911261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 920288924153149155881681 690216693114861866911261)
        ·
          refine ⟨258831259918073200091723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 690216693114861866911261 258831259918073200091723)
          ·
            refine ⟨388246889877109800137585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 258831259918073200091723 388246889877109800137585)
            ·
              refine ⟨291185167407832350103189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 388246889877109800137585 291185167407832350103189)
              ·
                refine ⟨13649304722242141411087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 291185167407832350103189 13649304722242141411087)
                ·
                  rfl

theorem cell20_89714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 2, 6].length) (baseStart_89714 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_89714 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_89714 prefixEnd_89714 := by exact prefixLift 89714
  have htrace : WordTrace (prefixWord ++ tailWord_89714) baseStart_89714 baseEnd_89714 := by
    simpa [prefixWord, tailWord_89714, baseEnd_89714] using wordTrace_append hprefix tailTrace_89714
  have hstable : (prefixWord ++ tailWord_89714).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_89714).length < 2 ^ (prefixWord ++ tailWord_89714).sum := by decide
  have hdescent : baseEnd_89714 < baseStart_89714 := by decide
  rcases family_descends (prefixWord ++ tailWord_89714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_89735 : List Nat := [1, 1, 4, 2, 1, 11]
def baseStart_89735 : Nat := 118140960795 + 89735 * 2 ^ 59
def prefixEnd_89735 : Nat := 4983230072969 + 3 ^ 40 * 89735 * 2
def baseEnd_89735 : Nat := 1516944412553469797525

theorem tailTrace_89735 : CollatzResearch.WordTrace tailWord_89735 prefixEnd_89735 1516944412553469797525 := by
  unfold tailWord_89735
  simp only [CollatzResearch.WordTrace]
  refine ⟨3272904329912895362982659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2181936219941930241988439 3272904329912895362982659)
  ·
    refine ⟨4909356494869343044473989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3272904329912895362982659 4909356494869343044473989)
    ·
      refine ⟨920504342788001820838873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4909356494869343044473989 920504342788001820838873)
      ·
        refine ⟨690378257091001365629155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 920504342788001820838873 690378257091001365629155)
        ·
          refine ⟨1035567385636502048443733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 690378257091001365629155 1035567385636502048443733)
          ·
            refine ⟨1516944412553469797525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 1035567385636502048443733 1516944412553469797525)
            ·
              rfl

theorem cell20_89735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 11].length) (baseStart_89735 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_89735 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_89735 prefixEnd_89735 := by exact prefixLift 89735
  have htrace : WordTrace (prefixWord ++ tailWord_89735) baseStart_89735 baseEnd_89735 := by
    simpa [prefixWord, tailWord_89735, baseEnd_89735] using wordTrace_append hprefix tailTrace_89735
  have hstable : (prefixWord ++ tailWord_89735).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_89735).length < 2 ^ (prefixWord ++ tailWord_89735).sum := by decide
  have hdescent : baseEnd_89735 < baseStart_89735 := by decide
  rcases family_descends (prefixWord ++ tailWord_89735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_89738 : List Nat := [3, 1, 2, 3, 2, 1, 1, 4, 3]
def baseStart_89738 : Nat := 118140960795 + 89738 * 2 ^ 59
def prefixEnd_89738 : Nat := 4983230072969 + 3 ^ 40 * 89738 * 2
def baseEnd_89738 : Nat := 40958868420689007433163

theorem tailTrace_89738 : CollatzResearch.WordTrace tailWord_89738 prefixEnd_89738 40958868420689007433163 := by
  unfold tailWord_89738
  simp only [CollatzResearch.WordTrace]
  refine ⟨818253437225506718835467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2182009165934684583561245 818253437225506718835467)
  ·
    refine ⟨1227380155838260078253201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 818253437225506718835467 1227380155838260078253201)
    ·
      refine ⟨920535116878695058689901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1227380155838260078253201 920535116878695058689901)
      ·
        refine ⟨345200668829510647008713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 920535116878695058689901 345200668829510647008713)
        ·
          refine ⟨258900501622132985256535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 345200668829510647008713 258900501622132985256535)
          ·
            refine ⟨388350752433199477884803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 258900501622132985256535 388350752433199477884803)
            ·
              refine ⟨582526128649799216827205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 388350752433199477884803 582526128649799216827205)
              ·
                refine ⟨109223649121837353155101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 582526128649799216827205 109223649121837353155101)
                ·
                  refine ⟨40958868420689007433163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 109223649121837353155101 40958868420689007433163)
                  ·
                    rfl

theorem cell20_89738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 4, 3].length) (baseStart_89738 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_89738 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_89738 prefixEnd_89738 := by exact prefixLift 89738
  have htrace : WordTrace (prefixWord ++ tailWord_89738) baseStart_89738 baseEnd_89738 := by
    simpa [prefixWord, tailWord_89738, baseEnd_89738] using wordTrace_append hprefix tailTrace_89738
  have hstable : (prefixWord ++ tailWord_89738).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_89738).length < 2 ^ (prefixWord ++ tailWord_89738).sum := by decide
  have hdescent : baseEnd_89738 < baseStart_89738 := by decide
  rcases family_descends (prefixWord ++ tailWord_89738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_89748 : List Nat := [2, 4, 2, 2, 2, 2, 1, 5]
def baseStart_89748 : Nat := 118140960795 + 89748 * 2 ^ 59
def prefixEnd_89748 : Nat := 4983230072969 + 3 ^ 40 * 89748 * 2
def baseEnd_89748 : Nat := 13654477564391139033263

theorem tailTrace_89748 : CollatzResearch.WordTrace tailWord_89748 prefixEnd_89748 13654477564391139033263 := by
  unfold tailWord_89748
  simp only [CollatzResearch.WordTrace]
  refine ⟨1636689239432899291602949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2182252319243865722137265 1636689239432899291602949)
  ·
    refine ⟨306879232393668617175553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1636689239432899291602949 306879232393668617175553)
    ·
      refine ⟨230159424295251462881665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 306879232393668617175553 230159424295251462881665)
      ·
        refine ⟨172619568221438597161249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 230159424295251462881665 172619568221438597161249)
        ·
          refine ⟨129464676166078947870937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 172619568221438597161249 129464676166078947870937)
          ·
            refine ⟨97098507124559210903203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 129464676166078947870937 97098507124559210903203)
            ·
              refine ⟨145647760686838816354805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97098507124559210903203 145647760686838816354805)
              ·
                refine ⟨13654477564391139033263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 145647760686838816354805 13654477564391139033263)
                ·
                  rfl

theorem cell20_89748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 2, 1, 5].length) (baseStart_89748 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_89748 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_89748 prefixEnd_89748 := by exact prefixLift 89748
  have htrace : WordTrace (prefixWord ++ tailWord_89748) baseStart_89748 baseEnd_89748 := by
    simpa [prefixWord, tailWord_89748, baseEnd_89748] using wordTrace_append hprefix tailTrace_89748
  have hstable : (prefixWord ++ tailWord_89748).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_89748).length < 2 ^ (prefixWord ++ tailWord_89748).sum := by decide
  have hdescent : baseEnd_89748 < baseStart_89748 := by decide
  rcases family_descends (prefixWord ++ tailWord_89748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_89752 : List Nat := [2, 1, 2, 4, 1, 2, 3, 5]
def baseStart_89752 : Nat := 118140960795 + 89752 * 2 ^ 59
def prefixEnd_89752 : Nat := 4983230072969 + 3 ^ 40 * 89752 * 2
def baseEnd_89752 : Nat := 13655086134055726988813

theorem tailTrace_89752 : CollatzResearch.WordTrace tailWord_89752 prefixEnd_89752 13655086134055726988813 := by
  unfold tailWord_89752
  simp only [CollatzResearch.WordTrace]
  refine ⟨1636762185425653633175755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2182349580567538177567673 1636762185425653633175755)
  ·
    refine ⟨2455143278138480449763633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1636762185425653633175755 2455143278138480449763633)
    ·
      refine ⟨1841357458603860337322725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2455143278138480449763633 1841357458603860337322725)
      ·
        refine ⟨345254523488223813248011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1841357458603860337322725 345254523488223813248011)
        ·
          refine ⟨517881785232335719872017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 345254523488223813248011 517881785232335719872017)
          ·
            refine ⟨388411338924251789904013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 517881785232335719872017 388411338924251789904013)
            ·
              refine ⟨145654252096594421214005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 388411338924251789904013 145654252096594421214005)
              ·
                refine ⟨13655086134055726988813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 145654252096594421214005 13655086134055726988813)
                ·
                  rfl

theorem cell20_89752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 3, 5].length) (baseStart_89752 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_89752 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_89752 prefixEnd_89752 := by exact prefixLift 89752
  have htrace : WordTrace (prefixWord ++ tailWord_89752) baseStart_89752 baseEnd_89752 := by
    simpa [prefixWord, tailWord_89752, baseEnd_89752] using wordTrace_append hprefix tailTrace_89752
  have hstable : (prefixWord ++ tailWord_89752).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_89752).length < 2 ^ (prefixWord ++ tailWord_89752).sum := by decide
  have hdescent : baseEnd_89752 < baseStart_89752 := by decide
  rcases family_descends (prefixWord ++ tailWord_89752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_89790 : List Nat := [4, 2, 1, 1, 2, 3, 7]
def baseStart_89790 : Nat := 118140960795 + 89790 * 2 ^ 59
def prefixEnd_89790 : Nat := 4983230072969 + 3 ^ 40 * 89790 * 2
def baseEnd_89790 : Nat := 4553622515289770855513

theorem tailTrace_89790 : CollatzResearch.WordTrace tailWord_89790 prefixEnd_89790 4553622515289770855513 := by
  unfold tailWord_89790
  simp only [CollatzResearch.WordTrace]
  refine ⟨409363793089204969529353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2183273563142426504156549 409363793089204969529353)
  ·
    refine ⟨307022844816903727147015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 409363793089204969529353 307022844816903727147015)
    ·
      refine ⟨460534267225355590720523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 307022844816903727147015 460534267225355590720523)
      ·
        refine ⟨690801400838033386080785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 460534267225355590720523 690801400838033386080785)
        ·
          refine ⟨518101050628525039560589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 690801400838033386080785 518101050628525039560589)
          ·
            refine ⟨194287893985696889835221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 518101050628525039560589 194287893985696889835221)
            ·
              refine ⟨4553622515289770855513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 194287893985696889835221 4553622515289770855513)
              ·
                rfl

theorem cell20_89790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 7].length) (baseStart_89790 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_89790 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_89790 prefixEnd_89790 := by exact prefixLift 89790
  have htrace : WordTrace (prefixWord ++ tailWord_89790) baseStart_89790 baseEnd_89790 := by
    simpa [prefixWord, tailWord_89790, baseEnd_89790] using wordTrace_append hprefix tailTrace_89790
  have hstable : (prefixWord ++ tailWord_89790).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_89790).length < 2 ^ (prefixWord ++ tailWord_89790).sum := by decide
  have hdescent : baseEnd_89790 < baseStart_89790 := by decide
  rcases family_descends (prefixWord ++ tailWord_89790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_89859 : List Nat := [1, 1, 1, 3, 2, 2, 2, 6, 2]
def baseStart_89859 : Nat := 118140960795 + 89859 * 2 ^ 59
def prefixEnd_89859 : Nat := 4983230072969 + 3 ^ 40 * 89859 * 2
def baseEnd_89859 : Nat := 41014096117750364399335

theorem tailTrace_89859 : CollatzResearch.WordTrace tailWord_89859 prefixEnd_89859 41014096117750364399335 := by
  unfold tailWord_89859
  simp only [CollatzResearch.WordTrace]
  refine ⟨3277426981463664540496631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2184951320975776360331087 3277426981463664540496631)
  ·
    refine ⟨4916140472195496810744947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3277426981463664540496631 4916140472195496810744947)
    ·
      refine ⟨7374210708293245216117421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4916140472195496810744947 7374210708293245216117421)
      ·
        refine ⟨2765329015609966956044033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7374210708293245216117421 2765329015609966956044033)
        ·
          refine ⟨2073996761707475217033025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2765329015609966956044033 2073996761707475217033025)
          ·
            refine ⟨1555497571280606412774769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2073996761707475217033025 1555497571280606412774769)
            ·
              refine ⟨1166623178460454809581077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1555497571280606412774769 1166623178460454809581077)
              ·
                refine ⟨54685461490333819199113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1166623178460454809581077 54685461490333819199113)
                ·
                  refine ⟨41014096117750364399335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54685461490333819199113 41014096117750364399335)
                  ·
                    rfl

theorem cell20_89859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 6, 2].length) (baseStart_89859 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_89859 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_89859 prefixEnd_89859 := by exact prefixLift 89859
  have htrace : WordTrace (prefixWord ++ tailWord_89859) baseStart_89859 baseEnd_89859 := by
    simpa [prefixWord, tailWord_89859, baseEnd_89859] using wordTrace_append hprefix tailTrace_89859
  have hstable : (prefixWord ++ tailWord_89859).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_89859).length < 2 ^ (prefixWord ++ tailWord_89859).sum := by decide
  have hdescent : baseEnd_89859 < baseStart_89859 := by decide
  rcases family_descends (prefixWord ++ tailWord_89859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_89866 : List Nat := [3, 1, 2, 2, 1, 4, 2, 5]
def baseStart_89866 : Nat := 118140960795 + 89866 * 2 ^ 59
def prefixEnd_89866 : Nat := 4983230072969 + 3 ^ 40 * 89866 * 2
def baseEnd_89866 : Nat := 13672430369496483721991

theorem tailTrace_89866 : CollatzResearch.WordTrace tailWord_89866 prefixEnd_89866 13672430369496483721991 := by
  unfold tailWord_89866
  simp only [CollatzResearch.WordTrace]
  refine ⟨819420573109576184000363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2185121528292203157334301 819420573109576184000363)
  ·
    refine ⟨1229130859664364276000545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 819420573109576184000363 1229130859664364276000545)
    ·
      refine ⟨921848144748273207000409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1229130859664364276000545 921848144748273207000409)
      ·
        refine ⟨691386108561204905250307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 921848144748273207000409 691386108561204905250307)
        ·
          refine ⟨1037079162841807357875461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 691386108561204905250307 1037079162841807357875461)
          ·
            refine ⟨194452343032838879601649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1037079162841807357875461 194452343032838879601649)
            ·
              refine ⟨145839257274629159701237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 194452343032838879601649 145839257274629159701237)
              ·
                refine ⟨13672430369496483721991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 145839257274629159701237 13672430369496483721991)
                ·
                  rfl

theorem cell20_89866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 2, 5].length) (baseStart_89866 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_89866 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_89866 prefixEnd_89866 := by exact prefixLift 89866
  have htrace : WordTrace (prefixWord ++ tailWord_89866) baseStart_89866 baseEnd_89866 := by
    simpa [prefixWord, tailWord_89866, baseEnd_89866] using wordTrace_append hprefix tailTrace_89866
  have hstable : (prefixWord ++ tailWord_89866).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_89866).length < 2 ^ (prefixWord ++ tailWord_89866).sum := by decide
  have hdescent : baseEnd_89866 < baseStart_89866 := by decide
  rcases family_descends (prefixWord ++ tailWord_89866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_89880 : List Nat := [2, 1, 2, 3, 1, 1, 2, 4, 4]
def baseStart_89880 : Nat := 118140960795 + 89880 * 2 ^ 59
def prefixEnd_89880 : Nat := 4983230072969 + 3 ^ 40 * 89880 * 2
def baseEnd_89880 : Nat := 41023681089967624699249

theorem tailTrace_89880 : CollatzResearch.WordTrace tailWord_89880 prefixEnd_89880 41023681089967624699249 := by
  unfold tailWord_89880
  simp only [CollatzResearch.WordTrace]
  refine ⟨1639096457193792563505547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2185461942925056751340729 1639096457193792563505547)
  ·
    refine ⟨2458644685790688845258321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1639096457193792563505547 2458644685790688845258321)
    ·
      refine ⟨1843983514343016633943741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2458644685790688845258321 1843983514343016633943741)
      ·
        refine ⟨691493817878631237728903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1843983514343016633943741 691493817878631237728903)
        ·
          refine ⟨1037240726817946856593355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 691493817878631237728903 1037240726817946856593355)
          ·
            refine ⟨1555861090226920284890033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1037240726817946856593355 1555861090226920284890033)
            ·
              refine ⟨1166895817670190213667525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1555861090226920284890033 1166895817670190213667525)
              ·
                refine ⟨218792965813160665062661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1166895817670190213667525 218792965813160665062661)
                ·
                  refine ⟨41023681089967624699249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 218792965813160665062661 41023681089967624699249)
                  ·
                    rfl

theorem cell20_89880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 4, 4].length) (baseStart_89880 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_89880 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_89880 prefixEnd_89880 := by exact prefixLift 89880
  have htrace : WordTrace (prefixWord ++ tailWord_89880) baseStart_89880 baseEnd_89880 := by
    simpa [prefixWord, tailWord_89880, baseEnd_89880] using wordTrace_append hprefix tailTrace_89880
  have hstable : (prefixWord ++ tailWord_89880).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_89880).length < 2 ^ (prefixWord ++ tailWord_89880).sum := by decide
  have hdescent : baseEnd_89880 < baseStart_89880 := by decide
  rcases family_descends (prefixWord ++ tailWord_89880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_89887 : List Nat := [1, 1, 2, 4, 2, 1, 1, 8]
def baseStart_89887 : Nat := 118140960795 + 89887 * 2 ^ 59
def prefixEnd_89887 : Nat := 4983230072969 + 3 ^ 40 * 89887 * 2
def baseEnd_89887 : Nat := 13675625360235570488629

theorem tailTrace_89887 : CollatzResearch.WordTrace tailWord_89887 prefixEnd_89887 13675625360235570488629 := by
  unfold tailWord_89887
  simp only [CollatzResearch.WordTrace]
  refine ⟨3278448225362225322515915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2185632150241483548343943 3278448225362225322515915)
  ·
    refine ⟨4917672338043337983773873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3278448225362225322515915 4917672338043337983773873)
    ·
      refine ⟨3688254253532503487830405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4917672338043337983773873 3688254253532503487830405)
      ·
        refine ⟨691547672537344403968201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3688254253532503487830405 691547672537344403968201)
        ·
          refine ⟨518660754403008302976151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 691547672537344403968201 518660754403008302976151)
          ·
            refine ⟨777991131604512454464227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 518660754403008302976151 777991131604512454464227)
            ·
              refine ⟨1166986697406768681696341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 777991131604512454464227 1166986697406768681696341)
              ·
                refine ⟨13675625360235570488629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1166986697406768681696341 13675625360235570488629)
                ·
                  rfl

theorem cell20_89887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 8].length) (baseStart_89887 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_89887 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_89887 prefixEnd_89887 := by exact prefixLift 89887
  have htrace : WordTrace (prefixWord ++ tailWord_89887) baseStart_89887 baseEnd_89887 := by
    simpa [prefixWord, tailWord_89887, baseEnd_89887] using wordTrace_append hprefix tailTrace_89887
  have hstable : (prefixWord ++ tailWord_89887).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_89887).length < 2 ^ (prefixWord ++ tailWord_89887).sum := by decide
  have hdescent : baseEnd_89887 < baseStart_89887 := by decide
  rcases family_descends (prefixWord ++ tailWord_89887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_89910 : List Nat := [5, 1, 2, 2, 1, 1, 4, 2, 2]
def baseStart_89910 : Nat := 118140960795 + 89910 * 2 ^ 59
def prefixEnd_89910 : Nat := 4983230072969 + 3 ^ 40 * 89910 * 2
def baseEnd_89910 : Nat := 41037373907420853699127

theorem tailTrace_89910 : CollatzResearch.WordTrace tailWord_89910 prefixEnd_89910 41037373907420853699127 := by
  unfold tailWord_89910
  simp only [CollatzResearch.WordTrace]
  refine ⟨204955444017431265662699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2186191402852600167068789 204955444017431265662699)
  ·
    refine ⟨307433166026146898494049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204955444017431265662699 307433166026146898494049)
    ·
      refine ⟨230574874519610173870537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 307433166026146898494049 230574874519610173870537)
      ·
        refine ⟨172931155889707630402903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 230574874519610173870537 172931155889707630402903)
        ·
          refine ⟨259396733834561445604355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 172931155889707630402903 259396733834561445604355)
          ·
            refine ⟨389095100751842168406533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 259396733834561445604355 389095100751842168406533)
            ·
              refine ⟨72955331390970406576225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 389095100751842168406533 72955331390970406576225)
              ·
                refine ⟨54716498543227804932169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72955331390970406576225 54716498543227804932169)
                ·
                  refine ⟨41037373907420853699127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54716498543227804932169 41037373907420853699127)
                  ·
                    rfl

theorem cell20_89910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 4, 2, 2].length) (baseStart_89910 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_89910 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_89910 prefixEnd_89910 := by exact prefixLift 89910
  have htrace : WordTrace (prefixWord ++ tailWord_89910) baseStart_89910 baseEnd_89910 := by
    simpa [prefixWord, tailWord_89910, baseEnd_89910] using wordTrace_append hprefix tailTrace_89910
  have hstable : (prefixWord ++ tailWord_89910).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_89910).length < 2 ^ (prefixWord ++ tailWord_89910).sum := by decide
  have hdescent : baseEnd_89910 < baseStart_89910 := by decide
  rcases family_descends (prefixWord ++ tailWord_89910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_89914 : List Nat := [3, 1, 1, 1, 5, 2, 1, 4, 2]
def baseStart_89914 : Nat := 118140960795 + 89914 * 2 ^ 59
def prefixEnd_89914 : Nat := 4983230072969 + 3 ^ 40 * 89914 * 2
def baseEnd_89914 : Nat := 41039199616414617565777

theorem tailTrace_89914 : CollatzResearch.WordTrace tailWord_89914 prefixEnd_89914 41039199616414617565777 := by
  unfold tailWord_89914
  simp only [CollatzResearch.WordTrace]
  refine ⟨819858249066102233437199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2186288664176272622499197 819858249066102233437199)
  ·
    refine ⟨1229787373599153350155799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 819858249066102233437199 1229787373599153350155799)
    ·
      refine ⟨1844681060398730025233699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1229787373599153350155799 1844681060398730025233699)
      ·
        refine ⟨2767021590598095037850549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1844681060398730025233699 2767021590598095037850549)
        ·
          refine ⟨259408274118571409798489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2767021590598095037850549 259408274118571409798489)
          ·
            refine ⟨194556205588928557348867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 259408274118571409798489 194556205588928557348867)
            ·
              refine ⟨291834308383392836023301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 194556205588928557348867 291834308383392836023301)
              ·
                refine ⟨54718932821886156754369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 291834308383392836023301 54718932821886156754369)
                ·
                  refine ⟨41039199616414617565777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54718932821886156754369 41039199616414617565777)
                  ·
                    rfl

theorem cell20_89914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 1, 4, 2].length) (baseStart_89914 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_89914 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_89914 prefixEnd_89914 := by exact prefixLift 89914
  have htrace : WordTrace (prefixWord ++ tailWord_89914) baseStart_89914 baseEnd_89914 := by
    simpa [prefixWord, tailWord_89914, baseEnd_89914] using wordTrace_append hprefix tailTrace_89914
  have hstable : (prefixWord ++ tailWord_89914).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_89914).length < 2 ^ (prefixWord ++ tailWord_89914).sum := by decide
  have hdescent : baseEnd_89914 < baseStart_89914 := by decide
  rcases family_descends (prefixWord ++ tailWord_89914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_89952 : List Nat := [2, 1, 1, 3, 3, 3, 2, 3, 2]
def baseStart_89952 : Nat := 118140960795 + 89952 * 2 ^ 59
def prefixEnd_89952 : Nat := 4983230072969 + 3 ^ 40 * 89952 * 2
def baseEnd_89952 : Nat := 41056543851855374298955

theorem tailTrace_89952 : CollatzResearch.WordTrace tailWord_89952 prefixEnd_89952 41056543851855374298955 := by
  unfold tailWord_89952
  simp only [CollatzResearch.WordTrace]
  refine ⟨1640409485063370711816055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2187212646751160949088073 1640409485063370711816055)
  ·
    refine ⟨2460614227595056067724083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1640409485063370711816055 2460614227595056067724083)
    ·
      refine ⟨3690921341392584101586125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2460614227595056067724083 3690921341392584101586125)
      ·
        refine ⟨1384095503022219038094797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3690921341392584101586125 1384095503022219038094797)
        ·
          refine ⟨519035813633332139285549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1384095503022219038094797 519035813633332139285549)
          ·
            refine ⟨194638430112499552232081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 519035813633332139285549 194638430112499552232081)
            ·
              refine ⟨145978822584374664174061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 194638430112499552232081 145978822584374664174061)
              ·
                refine ⟨54742058469140499065273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 145978822584374664174061 54742058469140499065273)
                ·
                  refine ⟨41056543851855374298955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54742058469140499065273 41056543851855374298955)
                  ·
                    rfl

theorem cell20_89952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 2, 3, 2].length) (baseStart_89952 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_89952 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_89952 prefixEnd_89952 := by exact prefixLift 89952
  have htrace : WordTrace (prefixWord ++ tailWord_89952) baseStart_89952 baseEnd_89952 := by
    simpa [prefixWord, tailWord_89952, baseEnd_89952] using wordTrace_append hprefix tailTrace_89952
  have hstable : (prefixWord ++ tailWord_89952).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_89952).length < 2 ^ (prefixWord ++ tailWord_89952).sum := by decide
  have hdescent : baseEnd_89952 < baseStart_89952 := by decide
  rcases family_descends (prefixWord ++ tailWord_89952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_89962 : List Nat := [3, 1, 3, 4, 1, 2, 1, 2, 3]
def baseStart_89962 : Nat := 118140960795 + 89962 * 2 ^ 59
def prefixEnd_89962 : Nat := 4983230072969 + 3 ^ 40 * 89962 * 2
def baseEnd_89962 : Nat := 41061108124339783965581

theorem tailTrace_89962 : CollatzResearch.WordTrace tailWord_89962 prefixEnd_89962 41061108124339783965581 := by
  unfold tailWord_89962
  simp only [CollatzResearch.WordTrace]
  refine ⟨820295925022628282874035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2187455800060342087664093 820295925022628282874035)
  ·
    refine ⟨1230443887533942424311053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 820295925022628282874035 1230443887533942424311053)
    ·
      refine ⟨461416457825228409116645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1230443887533942424311053 461416457825228409116645)
      ·
        refine ⟨86515585842230326709371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 461416457825228409116645 86515585842230326709371)
        ·
          refine ⟨129773378763345490064057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86515585842230326709371 129773378763345490064057)
          ·
            refine ⟨97330034072509117548043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 129773378763345490064057 97330034072509117548043)
            ·
              refine ⟨145995051108763676322065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97330034072509117548043 145995051108763676322065)
              ·
                refine ⟨109496288331572757241549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 145995051108763676322065 109496288331572757241549)
                ·
                  refine ⟨41061108124339783965581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 109496288331572757241549 41061108124339783965581)
                  ·
                    rfl

theorem cell20_89962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 2, 1, 2, 3].length) (baseStart_89962 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_89962 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_89962 prefixEnd_89962 := by exact prefixLift 89962
  have htrace : WordTrace (prefixWord ++ tailWord_89962) baseStart_89962 baseEnd_89962 := by
    simpa [prefixWord, tailWord_89962, baseEnd_89962] using wordTrace_append hprefix tailTrace_89962
  have hstable : (prefixWord ++ tailWord_89962).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_89962).length < 2 ^ (prefixWord ++ tailWord_89962).sum := by decide
  have hdescent : baseEnd_89962 < baseStart_89962 := by decide
  rcases family_descends (prefixWord ++ tailWord_89962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_89966 : List Nat := [4, 1, 2, 3, 1, 2, 1, 1, 5]
def baseStart_89966 : Nat := 118140960795 + 89966 * 2 ^ 59
def prefixEnd_89966 : Nat := 4983230072969 + 3 ^ 40 * 89966 * 2
def baseEnd_89966 : Nat := 41062933833333547832231

theorem tailTrace_89966 : CollatzResearch.WordTrace tailWord_89966 prefixEnd_89966 41062933833333547832231 := by
  unfold tailWord_89966
  simp only [CollatzResearch.WordTrace]
  refine ⟨410166199009502726830219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2187553061384014543094501 410166199009502726830219)
  ·
    refine ⟨615249298514254090245329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 410166199009502726830219 615249298514254090245329)
    ·
      refine ⟨461436973885690567683997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 615249298514254090245329 461436973885690567683997)
      ·
        refine ⟨173038865207133962881499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 461436973885690567683997 173038865207133962881499)
        ·
          refine ⟨259558297810700944322249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 173038865207133962881499 259558297810700944322249)
          ·
            refine ⟨194668723358025708241687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 259558297810700944322249 194668723358025708241687)
            ·
              refine ⟨292003085037038562362531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 194668723358025708241687 292003085037038562362531)
              ·
                refine ⟨438004627555557843543797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 292003085037038562362531 438004627555557843543797)
                ·
                  refine ⟨41062933833333547832231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 438004627555557843543797 41062933833333547832231)
                  ·
                    rfl

theorem cell20_89966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 1, 1, 5].length) (baseStart_89966 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_89966 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_89966 prefixEnd_89966 := by exact prefixLift 89966
  have htrace : WordTrace (prefixWord ++ tailWord_89966) baseStart_89966 baseEnd_89966 := by
    simpa [prefixWord, tailWord_89966, baseEnd_89966] using wordTrace_append hprefix tailTrace_89966
  have hstable : (prefixWord ++ tailWord_89966).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_89966).length < 2 ^ (prefixWord ++ tailWord_89966).sum := by decide
  have hdescent : baseEnd_89966 < baseStart_89966 := by decide
  rcases family_descends (prefixWord ++ tailWord_89966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_89973 : List Nat := [1, 3, 4, 1, 1, 1, 4, 1, 4]
def baseStart_89973 : Nat := 118140960795 + 89973 * 2 ^ 59
def prefixEnd_89973 : Nat := 4983230072969 + 3 ^ 40 * 89973 * 2
def baseEnd_89973 : Nat := 41066128824072634598869

theorem tailTrace_89973 : CollatzResearch.WordTrace tailWord_89973 prefixEnd_89973 41066128824072634598869 := by
  unfold tailWord_89973
  simp only [CollatzResearch.WordTrace]
  refine ⟨3281584903050662010146573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2187723268700441340097715 3281584903050662010146573)
  ·
    refine ⟨1230594338643998253804965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3281584903050662010146573 1230594338643998253804965)
    ·
      refine ⟨230736438495749672588431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1230594338643998253804965 230736438495749672588431)
      ·
        refine ⟨346104657743624508882647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 230736438495749672588431 346104657743624508882647)
        ·
          refine ⟨519156986615436763323971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 346104657743624508882647 519156986615436763323971)
          ·
            refine ⟨778735479923155144985957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 519156986615436763323971 778735479923155144985957)
            ·
              refine ⟨146012902485591589684867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 778735479923155144985957 146012902485591589684867)
              ·
                refine ⟨219019353728387384527301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 146012902485591589684867 219019353728387384527301)
                ·
                  refine ⟨41066128824072634598869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 219019353728387384527301 41066128824072634598869)
                  ·
                    rfl

theorem cell20_89973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 4, 1, 4].length) (baseStart_89973 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_89973 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_89973 prefixEnd_89973 := by exact prefixLift 89973
  have htrace : WordTrace (prefixWord ++ tailWord_89973) baseStart_89973 baseEnd_89973 := by
    simpa [prefixWord, tailWord_89973, baseEnd_89973] using wordTrace_append hprefix tailTrace_89973
  have hstable : (prefixWord ++ tailWord_89973).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_89973).length < 2 ^ (prefixWord ++ tailWord_89973).sum := by decide
  have hdescent : baseEnd_89973 < baseStart_89973 := by decide
  rcases family_descends (prefixWord ++ tailWord_89973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_90014 : List Nat := [4, 3, 1, 3, 1, 2, 6]
def baseStart_90014 : Nat := 118140960795 + 90014 * 2 ^ 59
def prefixEnd_90014 : Nat := 4983230072969 + 3 ^ 40 * 90014 * 2
def baseEnd_90014 : Nat := 4564982482362079359115

theorem tailTrace_90014 : CollatzResearch.WordTrace tailWord_90014 prefixEnd_90014 4564982482362079359115 := by
  unfold tailWord_90014
  simp only [CollatzResearch.WordTrace]
  refine ⟨410385036987765751548637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2188720197268084008259397 410385036987765751548637)
  ·
    refine ⟨153894388870412156830739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 410385036987765751548637 153894388870412156830739)
    ·
      refine ⟨230841583305618235246109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153894388870412156830739 230841583305618235246109)
      ·
        refine ⟨86565593739606838217291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 230841583305618235246109 86565593739606838217291)
        ·
          refine ⟨129848390609410257325937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86565593739606838217291 129848390609410257325937)
          ·
            refine ⟨97386292957057692994453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 129848390609410257325937 97386292957057692994453)
            ·
              refine ⟨4564982482362079359115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 97386292957057692994453 4564982482362079359115)
              ·
                rfl

theorem cell20_90014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 2, 6].length) (baseStart_90014 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_90014 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_90014 prefixEnd_90014 := by exact prefixLift 90014
  have htrace : WordTrace (prefixWord ++ tailWord_90014) baseStart_90014 baseEnd_90014 := by
    simpa [prefixWord, tailWord_90014, baseEnd_90014] using wordTrace_append hprefix tailTrace_90014
  have hstable : (prefixWord ++ tailWord_90014).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_90014).length < 2 ^ (prefixWord ++ tailWord_90014).sum := by decide
  have hdescent : baseEnd_90014 < baseStart_90014 := by decide
  rcases family_descends (prefixWord ++ tailWord_90014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_90024 : List Nat := [2, 1, 6, 2, 2, 1, 1, 1, 4]
def baseStart_90024 : Nat := 118140960795 + 90024 * 2 ^ 59
def prefixEnd_90024 : Nat := 4983230072969 + 3 ^ 40 * 90024 * 2
def baseEnd_90024 : Nat := 41089406613743123898661

theorem tailTrace_90024 : CollatzResearch.WordTrace tailWord_90024 prefixEnd_90024 41089406613743123898661 := by
  unfold tailWord_90024
  simp only [CollatzResearch.WordTrace]
  refine ⟨1641722512932948860126563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2188963350577265146835417 1641722512932948860126563)
  ·
    refine ⟨2462583769399423290189845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1641722512932948860126563 2462583769399423290189845)
    ·
      refine ⟨115433614190597966727649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 2462583769399423290189845 115433614190597966727649)
      ·
        refine ⟨86575210642948475045737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115433614190597966727649 86575210642948475045737)
        ·
          refine ⟨64931407982211356284303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86575210642948475045737 64931407982211356284303)
          ·
            refine ⟨97397111973317034426455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64931407982211356284303 97397111973317034426455)
            ·
              refine ⟨146095667959975551639683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97397111973317034426455 146095667959975551639683)
              ·
                refine ⟨219143501939963327459525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 146095667959975551639683 219143501939963327459525)
                ·
                  refine ⟨41089406613743123898661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 219143501939963327459525 41089406613743123898661)
                  ·
                    rfl

theorem cell20_90024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 1, 1, 1, 4].length) (baseStart_90024 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_90024 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_90024 prefixEnd_90024 := by exact prefixLift 90024
  have htrace : WordTrace (prefixWord ++ tailWord_90024) baseStart_90024 baseEnd_90024 := by
    simpa [prefixWord, tailWord_90024, baseEnd_90024] using wordTrace_append hprefix tailTrace_90024
  have hstable : (prefixWord ++ tailWord_90024).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_90024).length < 2 ^ (prefixWord ++ tailWord_90024).sum := by decide
  have hdescent : baseEnd_90024 < baseStart_90024 := by decide
  rcases family_descends (prefixWord ++ tailWord_90024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_90077 : List Nat := [1, 4, 3, 1, 11]
def baseStart_90077 : Nat := 118140960795 + 90077 * 2 ^ 59
def prefixEnd_90077 : Nat := 4983230072969 + 3 ^ 40 * 90077 * 2
def baseEnd_90077 : Nat := 507575274789018458417

theorem tailTrace_90077 : CollatzResearch.WordTrace tailWord_90077 prefixEnd_90077 507575274789018458417 := by
  unfold tailWord_90077
  simp only [CollatzResearch.WordTrace]
  refine ⟨3285378094673887771932485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2190252063115925181288323 3285378094673887771932485)
  ·
    refine ⟨616008392751353957237341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3285378094673887771932485 616008392751353957237341)
    ·
      refine ⟨231003147281757733964003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 616008392751353957237341 231003147281757733964003)
      ·
        refine ⟨346504720922636600946005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 231003147281757733964003 346504720922636600946005)
        ·
          refine ⟨507575274789018458417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 346504720922636600946005 507575274789018458417)
          ·
            rfl

theorem cell20_90077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 11].length) (baseStart_90077 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_90077 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_90077 prefixEnd_90077 := by exact prefixLift 90077
  have htrace : WordTrace (prefixWord ++ tailWord_90077) baseStart_90077 baseEnd_90077 := by
    simpa [prefixWord, tailWord_90077, baseEnd_90077] using wordTrace_append hprefix tailTrace_90077
  have hstable : (prefixWord ++ tailWord_90077).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_90077).length < 2 ^ (prefixWord ++ tailWord_90077).sum := by decide
  have hdescent : baseEnd_90077 < baseStart_90077 := by decide
  rcases family_descends (prefixWord ++ tailWord_90077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_90083 : List Nat := [1, 1, 1, 6, 1, 4, 2, 2, 2]
def baseStart_90083 : Nat := 118140960795 + 90083 * 2 ^ 59
def prefixEnd_90083 : Nat := 4983230072969 + 3 ^ 40 * 90083 * 2
def baseEnd_90083 : Nat := 41116335821401140931753

theorem tailTrace_90083 : CollatzResearch.WordTrace tailWord_90083 prefixEnd_90083 41116335821401140931753 := by
  unfold tailWord_90083
  simp only [CollatzResearch.WordTrace]
  refine ⟨3285596932652150796650903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2190397955101433864433935 3285596932652150796650903)
  ·
    refine ⟨4928395398978226194976355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3285596932652150796650903 4928395398978226194976355)
    ·
      refine ⟨7392593098467339292464533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4928395398978226194976355 7392593098467339292464533)
      ·
        refine ⟨346527801490656529334275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 7392593098467339292464533 346527801490656529334275)
        ·
          refine ⟨519791702235984794001413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 346527801490656529334275 519791702235984794001413)
          ·
            refine ⟨97460944169247148875265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 519791702235984794001413 97460944169247148875265)
            ·
              refine ⟨73095708126935361656449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 97460944169247148875265 73095708126935361656449)
              ·
                refine ⟨54821781095201521242337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73095708126935361656449 54821781095201521242337)
                ·
                  refine ⟨41116335821401140931753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54821781095201521242337 41116335821401140931753)
                  ·
                    rfl

theorem cell20_90083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 4, 2, 2, 2].length) (baseStart_90083 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_90083 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_90083 prefixEnd_90083 := by exact prefixLift 90083
  have htrace : WordTrace (prefixWord ++ tailWord_90083) baseStart_90083 baseEnd_90083 := by
    simpa [prefixWord, tailWord_90083, baseEnd_90083] using wordTrace_append hprefix tailTrace_90083
  have hstable : (prefixWord ++ tailWord_90083).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_90083).length < 2 ^ (prefixWord ++ tailWord_90083).sum := by decide
  have hdescent : baseEnd_90083 < baseStart_90083 := by decide
  rcases family_descends (prefixWord ++ tailWord_90083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_90091 : List Nat := [1, 1, 1, 1, 2, 3, 1, 2, 8]
def baseStart_90091 : Nat := 118140960795 + 90091 * 2 ^ 59
def prefixEnd_90091 : Nat := 4983230072969 + 3 ^ 40 * 90091 * 2
def baseEnd_90091 : Nat := 41119987239388668665053

theorem tailTrace_90091 : CollatzResearch.WordTrace tailWord_90091 prefixEnd_90091 41119987239388668665053 := by
  unfold tailWord_90091
  simp only [CollatzResearch.WordTrace]
  refine ⟨3285888716623168162942127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2190592477748778775294751 3285888716623168162942127)
  ·
    refine ⟨4928833074934752244413191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3285888716623168162942127 4928833074934752244413191)
    ·
      refine ⟨7393249612402128366619787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4928833074934752244413191 7393249612402128366619787)
      ·
        refine ⟨11089874418603192549929681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7393249612402128366619787 11089874418603192549929681)
        ·
          refine ⟨8317405813952394412447261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11089874418603192549929681 8317405813952394412447261)
          ·
            refine ⟨3119027180232147904667723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8317405813952394412447261 3119027180232147904667723)
            ·
              refine ⟨4678540770348221857001585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3119027180232147904667723 4678540770348221857001585)
              ·
                refine ⟨3508905577761166392751189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4678540770348221857001585 3508905577761166392751189)
                ·
                  refine ⟨41119987239388668665053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 3508905577761166392751189 41119987239388668665053)
                  ·
                    rfl

theorem cell20_90091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 2, 8].length) (baseStart_90091 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_90091 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_90091 prefixEnd_90091 := by exact prefixLift 90091
  have htrace : WordTrace (prefixWord ++ tailWord_90091) baseStart_90091 baseEnd_90091 := by
    simpa [prefixWord, tailWord_90091, baseEnd_90091] using wordTrace_append hprefix tailTrace_90091
  have hstable : (prefixWord ++ tailWord_90091).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_90091).length < 2 ^ (prefixWord ++ tailWord_90091).sum := by decide
  have hdescent : baseEnd_90091 < baseStart_90091 := by decide
  rcases family_descends (prefixWord ++ tailWord_90091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_90094 : List Nat := [4, 1, 2, 1, 3, 1, 3, 5]
def baseStart_90094 : Nat := 118140960795 + 90094 * 2 ^ 59
def prefixEnd_90094 : Nat := 4983230072969 + 3 ^ 40 * 90094 * 2
def baseEnd_90094 : Nat := 13707118840377997188347

theorem tailTrace_90094 : CollatzResearch.WordTrace tailWord_90094 prefixEnd_90094 13707118840377997188347 := by
  unfold tailWord_90094
  simp only [CollatzResearch.WordTrace]
  refine ⟨410749766951537459412667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2190665423741533116867557 410749766951537459412667)
  ·
    refine ⟨616124650427306189119001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 410749766951537459412667 616124650427306189119001)
    ·
      refine ⟨462093487820479641839251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 616124650427306189119001 462093487820479641839251)
      ·
        refine ⟨693140231730719462758877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 462093487820479641839251 693140231730719462758877)
        ·
          refine ⟨259927586899019798534579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 693140231730719462758877 259927586899019798534579)
          ·
            refine ⟨389891380348529697801869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 259927586899019798534579 389891380348529697801869)
            ·
              refine ⟨146209267630698636675701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 389891380348529697801869 146209267630698636675701)
              ·
                refine ⟨13707118840377997188347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 146209267630698636675701 13707118840377997188347)
                ·
                  rfl

theorem cell20_90094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 3, 5].length) (baseStart_90094 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_90094 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_90094 prefixEnd_90094 := by exact prefixLift 90094
  have htrace : WordTrace (prefixWord ++ tailWord_90094) baseStart_90094 baseEnd_90094 := by
    simpa [prefixWord, tailWord_90094, baseEnd_90094] using wordTrace_append hprefix tailTrace_90094
  have hstable : (prefixWord ++ tailWord_90094).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_90094).length < 2 ^ (prefixWord ++ tailWord_90094).sum := by decide
  have hdescent : baseEnd_90094 < baseStart_90094 := by decide
  rcases family_descends (prefixWord ++ tailWord_90094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_90108 : List Nat := [2, 2, 2, 1, 2, 2, 3, 2, 4]
def baseStart_90108 : Nat := 118140960795 + 90108 * 2 ^ 59
def prefixEnd_90108 : Nat := 4983230072969 + 3 ^ 40 * 90108 * 2
def baseEnd_90108 : Nat := 41127746502612165098317

theorem tailTrace_90108 : CollatzResearch.WordTrace tailWord_90108 prefixEnd_90108 41127746502612165098317 := by
  unfold tailWord_90108
  simp only [CollatzResearch.WordTrace]
  refine ⟨1643254378780790033155489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2191005838374386710873985 1643254378780790033155489)
  ·
    refine ⟨1232440784085592524866617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1643254378780790033155489 1232440784085592524866617)
    ·
      refine ⟨924330588064194393649963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1232440784085592524866617 924330588064194393649963)
      ·
        refine ⟨1386495882096291590474945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 924330588064194393649963 1386495882096291590474945)
        ·
          refine ⟨1039871911572218692856209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1386495882096291590474945 1039871911572218692856209)
          ·
            refine ⟨779903933679164019642157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1039871911572218692856209 779903933679164019642157)
            ·
              refine ⟨292463975129686507365809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 779903933679164019642157 292463975129686507365809)
              ·
                refine ⟨219347981347264880524357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 292463975129686507365809 219347981347264880524357)
                ·
                  refine ⟨41127746502612165098317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 219347981347264880524357 41127746502612165098317)
                  ·
                    rfl

theorem cell20_90108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 3, 2, 4].length) (baseStart_90108 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_90108 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_90108 prefixEnd_90108 := by exact prefixLift 90108
  have htrace : WordTrace (prefixWord ++ tailWord_90108) baseStart_90108 baseEnd_90108 := by
    simpa [prefixWord, tailWord_90108, baseEnd_90108] using wordTrace_append hprefix tailTrace_90108
  have hstable : (prefixWord ++ tailWord_90108).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_90108).length < 2 ^ (prefixWord ++ tailWord_90108).sum := by decide
  have hdescent : baseEnd_90108 < baseStart_90108 := by decide
  rcases family_descends (prefixWord ++ tailWord_90108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_90135 : List Nat := [1, 1, 3, 5, 2, 2, 1, 2, 3]
def baseStart_90135 : Nat := 118140960795 + 90135 * 2 ^ 59
def prefixEnd_90135 : Nat := 4983230072969 + 3 ^ 40 * 90135 * 2
def baseEnd_90135 : Nat := 41140070038320071198207

theorem tailTrace_90135 : CollatzResearch.WordTrace tailWord_90135 prefixEnd_90135 41140070038320071198207 := by
  unfold tailWord_90135
  simp only [CollatzResearch.WordTrace]
  refine ⟨3287493528463763677543859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2191662352309175785029239 3287493528463763677543859)
  ·
    refine ⟨4931240292695645516315789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3287493528463763677543859 4931240292695645516315789)
    ·
      refine ⟨1849215109760867068618421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4931240292695645516315789 1849215109760867068618421)
      ·
        refine ⟨173363916540081287682977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1849215109760867068618421 173363916540081287682977)
        ·
          refine ⟨130022937405060965762233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 173363916540081287682977 130022937405060965762233)
          ·
            refine ⟨97517203053795724321675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 130022937405060965762233 97517203053795724321675)
            ·
              refine ⟨146275804580693586482513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97517203053795724321675 146275804580693586482513)
              ·
                refine ⟨109706853435520189861885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 146275804580693586482513 109706853435520189861885)
                ·
                  refine ⟨41140070038320071198207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 109706853435520189861885 41140070038320071198207)
                  ·
                    rfl

theorem cell20_90135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 2, 1, 2, 3].length) (baseStart_90135 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_90135 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_90135 prefixEnd_90135 := by exact prefixLift 90135
  have htrace : WordTrace (prefixWord ++ tailWord_90135) baseStart_90135 baseEnd_90135 := by
    simpa [prefixWord, tailWord_90135, baseEnd_90135] using wordTrace_append hprefix tailTrace_90135
  have hstable : (prefixWord ++ tailWord_90135).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_90135).length < 2 ^ (prefixWord ++ tailWord_90135).sum := by decide
  have hdescent : baseEnd_90135 < baseStart_90135 := by decide
  rcases family_descends (prefixWord ++ tailWord_90135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_90152 : List Nat := [2, 1, 5, 3, 1, 1, 3, 1, 3]
def baseStart_90152 : Nat := 118140960795 + 90152 * 2 ^ 59
def prefixEnd_90152 : Nat := 4983230072969 + 3 ^ 40 * 90152 * 2
def baseEnd_90152 : Nat := 41147829301543567631471

theorem tailTrace_90152 : CollatzResearch.WordTrace tailWord_90152 prefixEnd_90152 41147829301543567631471 := by
  unfold tailWord_90152
  simp only [CollatzResearch.WordTrace]
  refine ⟨1644056784701087790456355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2192075712934783720608473 1644056784701087790456355)
  ·
    refine ⟨2466085177051631685684533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1644056784701087790456355 2466085177051631685684533)
    ·
      refine ⟨231195485348590470532925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2466085177051631685684533 231195485348590470532925)
      ·
        refine ⟨86698307005721426449847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 231195485348590470532925 86698307005721426449847)
        ·
          refine ⟨130047460508582139674771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86698307005721426449847 130047460508582139674771)
          ·
            refine ⟨195071190762873209512157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130047460508582139674771 195071190762873209512157)
            ·
              refine ⟨73151696536077453567059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 195071190762873209512157 73151696536077453567059)
              ·
                refine ⟨109727544804116180350589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73151696536077453567059 109727544804116180350589)
                ·
                  refine ⟨41147829301543567631471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 109727544804116180350589 41147829301543567631471)
                  ·
                    rfl

theorem cell20_90152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 3, 1, 3].length) (baseStart_90152 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_90152 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_90152 prefixEnd_90152 := by exact prefixLift 90152
  have htrace : WordTrace (prefixWord ++ tailWord_90152) baseStart_90152 baseEnd_90152 := by
    simpa [prefixWord, tailWord_90152, baseEnd_90152] using wordTrace_append hprefix tailTrace_90152
  have hstable : (prefixWord ++ tailWord_90152).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_90152).length < 2 ^ (prefixWord ++ tailWord_90152).sum := by decide
  have hdescent : baseEnd_90152 < baseStart_90152 := by decide
  rcases family_descends (prefixWord ++ tailWord_90152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_90177 : List Nat := [1, 2, 5, 1, 2, 1, 1, 2, 5]
def baseStart_90177 : Nat := 118140960795 + 90177 * 2 ^ 59
def prefixEnd_90177 : Nat := 4983230072969 + 3 ^ 40 * 90177 * 2
def baseEnd_90177 : Nat := 41159239982754591798035

theorem tailTrace_90177 : CollatzResearch.WordTrace tailWord_90177 prefixEnd_90177 41159239982754591798035 := by
  unfold tailWord_90177
  simp only [CollatzResearch.WordTrace]
  refine ⟨3289025394311604850572785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2192683596207736567048523 3289025394311604850572785)
  ·
    refine ⟨2466769045733703637929589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3289025394311604850572785 2466769045733703637929589)
    ·
      refine ⟨231259598037534716055899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2466769045733703637929589 231259598037534716055899)
      ·
        refine ⟨346889397056302074083849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 231259598037534716055899 346889397056302074083849)
        ·
          refine ⟨260167047792226555562887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 346889397056302074083849 260167047792226555562887)
          ·
            refine ⟨390250571688339833344331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 260167047792226555562887 390250571688339833344331)
            ·
              refine ⟨585375857532509750016497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 390250571688339833344331 585375857532509750016497)
              ·
                refine ⟨439031893149382312512373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 585375857532509750016497 439031893149382312512373)
                ·
                  refine ⟨41159239982754591798035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 439031893149382312512373 41159239982754591798035)
                  ·
                    rfl

theorem cell20_90177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 2, 5].length) (baseStart_90177 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_90177 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_90177 prefixEnd_90177 := by exact prefixLift 90177
  have htrace : WordTrace (prefixWord ++ tailWord_90177) baseStart_90177 baseEnd_90177 := by
    simpa [prefixWord, tailWord_90177, baseEnd_90177] using wordTrace_append hprefix tailTrace_90177
  have hstable : (prefixWord ++ tailWord_90177).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_90177).length < 2 ^ (prefixWord ++ tailWord_90177).sum := by decide
  have hdescent : baseEnd_90177 < baseStart_90177 := by decide
  rcases family_descends (prefixWord ++ tailWord_90177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_90215 : List Nat := [1, 1, 5, 1, 1, 2, 3, 3, 3]
def baseStart_90215 : Nat := 118140960795 + 90215 * 2 ^ 59
def prefixEnd_90215 : Nat := 4983230072969 + 3 ^ 40 * 90215 * 2
def baseEnd_90215 : Nat := 41176584218195348531213

theorem tailTrace_90215 : CollatzResearch.WordTrace tailWord_90215 prefixEnd_90215 41176584218195348531213 := by
  unfold tailWord_90215
  simp only [CollatzResearch.WordTrace]
  refine ⟨3290411368173937340456099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2193607578782624893637399 3290411368173937340456099)
  ·
    refine ⟨4935617052260906010684149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3290411368173937340456099 4935617052260906010684149)
    ·
      refine ⟨462714098649459938501639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4935617052260906010684149 462714098649459938501639)
      ·
        refine ⟨694071147974189907752459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 462714098649459938501639 694071147974189907752459)
        ·
          refine ⟨1041106721961284861628689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 694071147974189907752459 1041106721961284861628689)
          ·
            refine ⟨780830041470963646221517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1041106721961284861628689 780830041470963646221517)
            ·
              refine ⟨292811265551611367333069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 780830041470963646221517 292811265551611367333069)
              ·
                refine ⟨109804224581854262749901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 292811265551611367333069 109804224581854262749901)
                ·
                  refine ⟨41176584218195348531213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 109804224581854262749901 41176584218195348531213)
                  ·
                    rfl

theorem cell20_90215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 3, 3, 3].length) (baseStart_90215 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_90215 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_90215 prefixEnd_90215 := by exact prefixLift 90215
  have htrace : WordTrace (prefixWord ++ tailWord_90215) baseStart_90215 baseEnd_90215 := by
    simpa [prefixWord, tailWord_90215, baseEnd_90215] using wordTrace_append hprefix tailTrace_90215
  have hstable : (prefixWord ++ tailWord_90215).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_90215).length < 2 ^ (prefixWord ++ tailWord_90215).sum := by decide
  have hdescent : baseEnd_90215 < baseStart_90215 := by decide
  rcases family_descends (prefixWord ++ tailWord_90215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_90222 : List Nat := [4, 1, 2, 2, 1, 1, 2, 1, 6]
def baseStart_90222 : Nat := 118140960795 + 90222 * 2 ^ 59
def prefixEnd_90222 : Nat := 4983230072969 + 3 ^ 40 * 90222 * 2
def baseEnd_90222 : Nat := 41179779208934435297851

theorem tailTrace_90222 : CollatzResearch.WordTrace tailWord_90222 prefixEnd_90222 41179779208934435297851 := by
  unfold tailWord_90222
  simp only [CollatzResearch.WordTrace]
  refine ⟨411333334893572191995115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2193777786099051690640613 411333334893572191995115)
  ·
    refine ⟨617000002340358287992673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 411333334893572191995115 617000002340358287992673)
    ·
      refine ⟨462750001755268715994505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 617000002340358287992673 462750001755268715994505)
      ·
        refine ⟨347062501316451536995879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 462750001755268715994505 347062501316451536995879)
        ·
          refine ⟨520593751974677305493819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 347062501316451536995879 520593751974677305493819)
          ·
            refine ⟨780890627962015958240729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 520593751974677305493819 780890627962015958240729)
            ·
              refine ⟨585667970971511968680547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 780890627962015958240729 585667970971511968680547)
              ·
                refine ⟨878501956457267953020821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 585667970971511968680547 878501956457267953020821)
                ·
                  refine ⟨41179779208934435297851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 878501956457267953020821 41179779208934435297851)
                  ·
                    rfl

theorem cell20_90222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 1, 6].length) (baseStart_90222 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_90222 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_90222 prefixEnd_90222 := by exact prefixLift 90222
  have htrace : WordTrace (prefixWord ++ tailWord_90222) baseStart_90222 baseEnd_90222 := by
    simpa [prefixWord, tailWord_90222, baseEnd_90222] using wordTrace_append hprefix tailTrace_90222
  have hstable : (prefixWord ++ tailWord_90222).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_90222).length < 2 ^ (prefixWord ++ tailWord_90222).sum := by decide
  have hdescent : baseEnd_90222 < baseStart_90222 := by decide
  rcases family_descends (prefixWord ++ tailWord_90222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_90263 : List Nat := [1, 1, 3, 3, 5, 1, 1, 5]
def baseStart_90263 : Nat := 118140960795 + 90263 * 2 ^ 59
def prefixEnd_90263 : Nat := 4983230072969 + 3 ^ 40 * 90263 * 2
def baseEnd_90263 : Nat := 13732830908706838310339

theorem tailTrace_90263 : CollatzResearch.WordTrace tailWord_90263 prefixEnd_90263 13732830908706838310339 := by
  unfold tailWord_90263
  simp only [CollatzResearch.WordTrace]
  refine ⟨3292162072000041538203443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2194774714666694358802295 3292162072000041538203443)
  ·
    refine ⟨4938243108000062307305165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3292162072000041538203443 4938243108000062307305165)
    ·
      refine ⟨1851841165500023365239437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4938243108000062307305165 1851841165500023365239437)
      ·
        refine ⟨694440437062508761964789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1851841165500023365239437 694440437062508761964789)
        ·
          refine ⟨65103790974610196434199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 694440437062508761964789 65103790974610196434199)
          ·
            refine ⟨97655686461915294651299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65103790974610196434199 97655686461915294651299)
            ·
              refine ⟨146483529692872941976949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97655686461915294651299 146483529692872941976949)
              ·
                refine ⟨13732830908706838310339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 146483529692872941976949 13732830908706838310339)
                ·
                  rfl

theorem cell20_90263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 1, 1, 5].length) (baseStart_90263 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_90263 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_90263 prefixEnd_90263 := by exact prefixLift 90263
  have htrace : WordTrace (prefixWord ++ tailWord_90263) baseStart_90263 baseEnd_90263 := by
    simpa [prefixWord, tailWord_90263, baseEnd_90263] using wordTrace_append hprefix tailTrace_90263
  have hstable : (prefixWord ++ tailWord_90263).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_90263).length < 2 ^ (prefixWord ++ tailWord_90263).sum := by decide
  have hdescent : baseEnd_90263 < baseStart_90263 := by decide
  rcases family_descends (prefixWord ++ tailWord_90263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_90308 : List Nat := [2, 3, 3, 1, 2, 1, 3, 2, 3]
def baseStart_90308 : Nat := 118140960795 + 90308 * 2 ^ 59
def prefixEnd_90308 : Nat := 4983230072969 + 3 ^ 40 * 90308 * 2
def baseEnd_90308 : Nat := 41219031952300358430833

theorem tailTrace_90308 : CollatzResearch.WordTrace tailWord_90308 prefixEnd_90308 41219031952300358430833 := by
  unfold tailWord_90308
  simp only [CollatzResearch.WordTrace]
  refine ⟨1646901678418507111795789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2195868904558009482394385 1646901678418507111795789)
  ·
    refine ⟨617588129406940166923421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1646901678418507111795789 617588129406940166923421)
    ·
      refine ⟨231595548527602562596283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 617588129406940166923421 231595548527602562596283)
      ·
        refine ⟨347393322791403843894425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 231595548527602562596283 347393322791403843894425)
        ·
          refine ⟨260544992093552882920819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 347393322791403843894425 260544992093552882920819)
          ·
            refine ⟨390817488140329324381229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 260544992093552882920819 390817488140329324381229)
            ·
              refine ⟨146556558052623496642961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 390817488140329324381229 146556558052623496642961)
              ·
                refine ⟨109917418539467622482221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 146556558052623496642961 109917418539467622482221)
                ·
                  refine ⟨41219031952300358430833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 109917418539467622482221 41219031952300358430833)
                  ·
                    rfl

theorem cell20_90308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 3, 2, 3].length) (baseStart_90308 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_90308 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_90308 prefixEnd_90308 := by exact prefixLift 90308
  have htrace : WordTrace (prefixWord ++ tailWord_90308) baseStart_90308 baseEnd_90308 := by
    simpa [prefixWord, tailWord_90308, baseEnd_90308] using wordTrace_append hprefix tailTrace_90308
  have hstable : (prefixWord ++ tailWord_90308).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_90308).length < 2 ^ (prefixWord ++ tailWord_90308).sum := by decide
  have hdescent : baseEnd_90308 < baseStart_90308 := by decide
  rcases family_descends (prefixWord ++ tailWord_90308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
