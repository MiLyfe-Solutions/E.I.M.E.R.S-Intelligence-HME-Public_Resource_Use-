import V185TrunkScan23Chunk0514

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_3045429 : List Nat := [1, 3, 3, 1, 1, 1, 2, 4, 1, 4, 2]
def baseStart_3045429 : Nat := 118140960795 + 3045429 * 2 ^ 59
def prefixEnd_3045429 : Nat := 4983230072969 + 3 ^ 40 * 3045429 * 2
def baseEnd_3045429 : Nat := 1563768876141470478731833

theorem tailTrace_3045429 : CollatzResearch.WordTrace tailWord_3045429 prefixEnd_3045429 1563768876141470478731833 := by
  unfold tailWord_3045429
  simp only [CollatzResearch.WordTrace]
  refine ⟨111075920883938325709611341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74050613922625550473074227 111075920883938325709611341)
  ·
    refine ⟨41653470331476872141104253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111075920883938325709611341 41653470331476872141104253)
    ·
      refine ⟨15620051374303827052914095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41653470331476872141104253 15620051374303827052914095)
      ·
        refine ⟨23430077061455740579371143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15620051374303827052914095 23430077061455740579371143)
        ·
          refine ⟨35145115592183610869056715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23430077061455740579371143 35145115592183610869056715)
          ·
            refine ⟨52717673388275416303585073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35145115592183610869056715 52717673388275416303585073)
            ·
              refine ⟨39538255041206562227688805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52717673388275416303585073 39538255041206562227688805)
              ·
                refine ⟨7413422820226230417691651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39538255041206562227688805 7413422820226230417691651)
                ·
                  refine ⟨11120134230339345626537477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7413422820226230417691651 11120134230339345626537477)
                  ·
                    refine ⟨2085025168188627304975777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11120134230339345626537477 2085025168188627304975777)
                    ·
                      refine ⟨1563768876141470478731833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2085025168188627304975777 1563768876141470478731833)
                      ·
                        rfl

theorem cell23_3045429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 4, 1, 4, 2].length) (baseStart_3045429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3045429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3045429 prefixEnd_3045429 := by exact prefixLift 3045429
  have htrace : WordTrace (prefixWord ++ tailWord_3045429) baseStart_3045429 baseEnd_3045429 := by
    simpa [prefixWord, tailWord_3045429, baseEnd_3045429] using wordTrace_append hprefix tailTrace_3045429
  have hstable : (prefixWord ++ tailWord_3045429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3045429).length < 2 ^ (prefixWord ++ tailWord_3045429).sum := by decide
  have hdescent : baseEnd_3045429 < baseStart_3045429 := by decide
  rcases family_descends (prefixWord ++ tailWord_3045429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3045445 : List Nat := [1, 3, 1, 1, 1, 3, 1, 1, 1, 1, 9]
def baseStart_3045445 : Nat := 118140960795 + 3045445 * 2 ^ 59
def prefixEnd_3045445 : Nat := 4983230072969 + 3 ^ 40 * 3045445 * 2
def baseEnd_3045445 : Nat := 1563777091831942416131759

theorem tailTrace_3045445 : CollatzResearch.WordTrace tailWord_3045445 prefixEnd_3045445 1563777091831942416131759 := by
  unfold tailWord_3045445
  simp only [CollatzResearch.WordTrace]
  refine ⟨111076504451880360442193789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74051002967920240294795859 111076504451880360442193789)
  ·
    refine ⟨41653689169455135165822671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111076504451880360442193789 41653689169455135165822671)
    ·
      refine ⟨62480533754182702748734007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41653689169455135165822671 62480533754182702748734007)
      ·
        refine ⟨93720800631274054123101011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62480533754182702748734007 93720800631274054123101011)
        ·
          refine ⟨140581200946911081184651517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93720800631274054123101011 140581200946911081184651517)
          ·
            refine ⟨52717950355091655444244319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 140581200946911081184651517 52717950355091655444244319)
            ·
              refine ⟨79076925532637483166366479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52717950355091655444244319 79076925532637483166366479)
              ·
                refine ⟨118615388298956224749549719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79076925532637483166366479 118615388298956224749549719)
                ·
                  refine ⟨177923082448434337124324579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 118615388298956224749549719 177923082448434337124324579)
                  ·
                    refine ⟨266884623672651505686486869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 177923082448434337124324579 266884623672651505686486869)
                    ·
                      refine ⟨1563777091831942416131759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 266884623672651505686486869 1563777091831942416131759)
                      ·
                        rfl

theorem cell23_3045445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 1, 1, 1, 9].length) (baseStart_3045445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3045445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3045445 prefixEnd_3045445 := by exact prefixLift 3045445
  have htrace : WordTrace (prefixWord ++ tailWord_3045445) baseStart_3045445 baseEnd_3045445 := by
    simpa [prefixWord, tailWord_3045445, baseEnd_3045445] using wordTrace_append hprefix tailTrace_3045445
  have hstable : (prefixWord ++ tailWord_3045445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3045445).length < 2 ^ (prefixWord ++ tailWord_3045445).sum := by decide
  have hdescent : baseEnd_3045445 < baseStart_3045445 := by decide
  rcases family_descends (prefixWord ++ tailWord_3045445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3045452 : List Nat := [2, 2, 1, 3, 1, 1, 5, 1, 7]
def baseStart_3045452 : Nat := 118140960795 + 3045452 * 2 ^ 59
def prefixEnd_3045452 : Nat := 4983230072969 + 3 ^ 40 * 3045452 * 2
def baseEnd_3045452 : Nat := 173753409577391543193803

theorem tailTrace_3045452 : CollatzResearch.WordTrace tailWord_3045452 prefixEnd_3045452 173753409577391543193803 := by
  unfold tailWord_3045452
  simp only [CollatzResearch.WordTrace]
  refine ⟨55538379881427500318849305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74051173175236667091799073 55538379881427500318849305)
  ·
    refine ⟨41653784911070625239136979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55538379881427500318849305 41653784911070625239136979)
    ·
      refine ⟨62480677366605937858705469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41653784911070625239136979 62480677366605937858705469)
      ·
        refine ⟨23430254012477226697014551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62480677366605937858705469 23430254012477226697014551)
        ·
          refine ⟨35145381018715840045521827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23430254012477226697014551 35145381018715840045521827)
          ·
            refine ⟨52718071528073760068282741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35145381018715840045521827 52718071528073760068282741)
            ·
              refine ⟨4942319205756915006401507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 52718071528073760068282741 4942319205756915006401507)
              ·
                refine ⟨7413478808635372509602261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4942319205756915006401507 7413478808635372509602261)
                ·
                  refine ⟨173753409577391543193803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7413478808635372509602261 173753409577391543193803)
                  ·
                    rfl

theorem cell23_3045452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 5, 1, 7].length) (baseStart_3045452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3045452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3045452 prefixEnd_3045452 := by exact prefixLift 3045452
  have htrace : WordTrace (prefixWord ++ tailWord_3045452) baseStart_3045452 baseEnd_3045452 := by
    simpa [prefixWord, tailWord_3045452, baseEnd_3045452] using wordTrace_append hprefix tailTrace_3045452
  have hstable : (prefixWord ++ tailWord_3045452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3045452).length < 2 ^ (prefixWord ++ tailWord_3045452).sum := by decide
  have hdescent : baseEnd_3045452 < baseStart_3045452 := by decide
  rcases family_descends (prefixWord ++ tailWord_3045452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3045463 : List Nat := [1, 1, 3, 2, 2, 1, 6, 1, 2, 2, 2]
def baseStart_3045463 : Nat := 118140960795 + 3045463 * 2 ^ 59
def prefixEnd_3045463 : Nat := 4983230072969 + 3 ^ 40 * 3045463 * 2
def baseEnd_3045463 : Nat := 1563786334483723345706677

theorem tailTrace_3045463 : CollatzResearch.WordTrace tailWord_3045463 prefixEnd_3045463 1563786334483723345706677 := by
  unfold tailWord_3045463
  simp only [CollatzResearch.WordTrace]
  refine ⟨111077160965815149516349043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74051440643876766344232695 111077160965815149516349043)
  ·
    refine ⟨166615741448722724274523565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111077160965815149516349043 166615741448722724274523565)
    ·
      refine ⟨62480903043271021602946337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 166615741448722724274523565 62480903043271021602946337)
      ·
        refine ⟨46860677282453266202209753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62480903043271021602946337 46860677282453266202209753)
        ·
          refine ⟨35145507961839949651657315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46860677282453266202209753 35145507961839949651657315)
          ·
            refine ⟨52718261942759924477485973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35145507961839949651657315 52718261942759924477485973)
            ·
              refine ⟨2471168528566871459882155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 52718261942759924477485973 2471168528566871459882155)
              ·
                refine ⟨3706752792850307189823233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2471168528566871459882155 3706752792850307189823233)
                ·
                  refine ⟨2780064594637730392367425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3706752792850307189823233 2780064594637730392367425)
                  ·
                    refine ⟨2085048445978297794275569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2780064594637730392367425 2085048445978297794275569)
                    ·
                      refine ⟨1563786334483723345706677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2085048445978297794275569 1563786334483723345706677)
                      ·
                        rfl

theorem cell23_3045463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 6, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 6, 1, 2, 2, 2].length) (baseStart_3045463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3045463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3045463 prefixEnd_3045463 := by exact prefixLift 3045463
  have htrace : WordTrace (prefixWord ++ tailWord_3045463) baseStart_3045463 baseEnd_3045463 := by
    simpa [prefixWord, tailWord_3045463, baseEnd_3045463] using wordTrace_append hprefix tailTrace_3045463
  have hstable : (prefixWord ++ tailWord_3045463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3045463).length < 2 ^ (prefixWord ++ tailWord_3045463).sum := by decide
  have hdescent : baseEnd_3045463 < baseStart_3045463 := by decide
  rcases family_descends (prefixWord ++ tailWord_3045463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3045536 : List Nat := [2, 1, 1, 4, 2, 4, 1, 1, 2, 1, 4]
def baseStart_3045536 : Nat := 118140960795 + 3045536 * 2 ^ 59
def prefixEnd_3045536 : Nat := 4983230072969 + 3 ^ 40 * 3045536 * 2
def baseEnd_3045536 : Nat := 1563823818571501560093841

theorem tailTrace_3045536 : CollatzResearch.WordTrace tailWord_3045536 prefixEnd_3045536 1563823818571501560093841 := by
  unfold tailWord_3045536
  simp only [CollatzResearch.WordTrace]
  refine ⟨55539911747275341491878231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74053215663033788655837641 55539911747275341491878231)
  ·
    refine ⟨83309867620913012237817347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55539911747275341491878231 83309867620913012237817347)
    ·
      refine ⟨124964801431369518356726021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83309867620913012237817347 124964801431369518356726021)
      ·
        refine ⟨23430900268381784691886129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 124964801431369518356726021 23430900268381784691886129)
        ·
          refine ⟨17573175201286338518914597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23430900268381784691886129 17573175201286338518914597)
          ·
            refine ⟨3294970350241188472296487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17573175201286338518914597 3294970350241188472296487)
            ·
              refine ⟨4942455525361782708444731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3294970350241188472296487 4942455525361782708444731)
              ·
                refine ⟨7413683288042674062667097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4942455525361782708444731 7413683288042674062667097)
                ·
                  refine ⟨5560262466032005547000323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7413683288042674062667097 5560262466032005547000323)
                  ·
                    refine ⟨8340393699048008320500485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5560262466032005547000323 8340393699048008320500485)
                    ·
                      refine ⟨1563823818571501560093841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8340393699048008320500485 1563823818571501560093841)
                      ·
                        rfl

theorem cell23_3045536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 4, 1, 1, 2, 1, 4].length) (baseStart_3045536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3045536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3045536 prefixEnd_3045536 := by exact prefixLift 3045536
  have htrace : WordTrace (prefixWord ++ tailWord_3045536) baseStart_3045536 baseEnd_3045536 := by
    simpa [prefixWord, tailWord_3045536, baseEnd_3045536] using wordTrace_append hprefix tailTrace_3045536
  have hstable : (prefixWord ++ tailWord_3045536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3045536).length < 2 ^ (prefixWord ++ tailWord_3045536).sum := by decide
  have hdescent : baseEnd_3045536 < baseStart_3045536 := by decide
  rcases family_descends (prefixWord ++ tailWord_3045536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3045549 : List Nat := [1, 5, 2, 1, 2, 1, 1, 1, 2, 1, 6]
def baseStart_3045549 : Nat := 118140960795 + 3045549 * 2 ^ 59
def prefixEnd_3045549 : Nat := 4983230072969 + 3 ^ 40 * 3045549 * 2
def baseEnd_3045549 : Nat := 1563830493820010009231281

theorem tailTrace_3045549 : CollatzResearch.WordTrace tailWord_3045549 prefixEnd_3045549 1563830493820010009231281 := by
  unfold tailWord_3045549
  simp only [CollatzResearch.WordTrace]
  refine ⟨111080297643503586203979701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74053531762335724135986467 111080297643503586203979701)
  ·
    refine ⟨10413777904078461206623097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 111080297643503586203979701 10413777904078461206623097)
    ·
      refine ⟨7810333428058845904967323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10413777904078461206623097 7810333428058845904967323)
      ·
        refine ⟨11715500142088268857450985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7810333428058845904967323 11715500142088268857450985)
        ·
          refine ⟨8786625106566201643088239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11715500142088268857450985 8786625106566201643088239)
          ·
            refine ⟨13179937659849302464632359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8786625106566201643088239 13179937659849302464632359)
            ·
              refine ⟨19769906489773953696948539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13179937659849302464632359 19769906489773953696948539)
              ·
                refine ⟨29654859734660930545422809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19769906489773953696948539 29654859734660930545422809)
                ·
                  refine ⟨22241144800995697909067107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29654859734660930545422809 22241144800995697909067107)
                  ·
                    refine ⟨33361717201493546863600661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22241144800995697909067107 33361717201493546863600661)
                    ·
                      refine ⟨1563830493820010009231281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 33361717201493546863600661 1563830493820010009231281)
                      ·
                        rfl

theorem cell23_3045549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 1, 2, 1, 6].length) (baseStart_3045549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3045549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3045549 prefixEnd_3045549 := by exact prefixLift 3045549
  have htrace : WordTrace (prefixWord ++ tailWord_3045549) baseStart_3045549 baseEnd_3045549 := by
    simpa [prefixWord, tailWord_3045549, baseEnd_3045549] using wordTrace_append hprefix tailTrace_3045549
  have hstable : (prefixWord ++ tailWord_3045549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3045549).length < 2 ^ (prefixWord ++ tailWord_3045549).sum := by decide
  have hdescent : baseEnd_3045549 < baseStart_3045549 := by decide
  rcases family_descends (prefixWord ++ tailWord_3045549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3045559 : List Nat := [1, 1, 3, 1, 4, 2, 3, 2, 6]
def baseStart_3045559 : Nat := 118140960795 + 3045559 * 2 ^ 59
def prefixEnd_3045559 : Nat := 4983230072969 + 3 ^ 40 * 3045559 * 2
def baseEnd_3045559 : Nat := 173759514291839441122915

theorem tailTrace_3045559 : CollatzResearch.WordTrace tailWord_3045559 prefixEnd_3045559 173759514291839441122915 := by
  unfold tailWord_3045559
  simp only [CollatzResearch.WordTrace]
  refine ⟨111080662373467357911843731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74053774915644905274562487 111080662373467357911843731)
  ·
    refine ⟨166620993560201036867765597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111080662373467357911843731 166620993560201036867765597)
    ·
      refine ⟨62482872585075388825412099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 166620993560201036867765597 62482872585075388825412099)
      ·
        refine ⟨93724308877613083238118149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62482872585075388825412099 93724308877613083238118149)
        ·
          refine ⟨17573307914552453107147153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 93724308877613083238118149 17573307914552453107147153)
          ·
            refine ⟨13179980935914339830360365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17573307914552453107147153 13179980935914339830360365)
            ·
              refine ⟨4942492850967877436385137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13179980935914339830360365 4942492850967877436385137)
              ·
                refine ⟨3706869638225908077288853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4942492850967877436385137 3706869638225908077288853)
                ·
                  refine ⟨173759514291839441122915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3706869638225908077288853 173759514291839441122915)
                  ·
                    rfl

theorem cell23_3045559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 3, 2, 6].length) (baseStart_3045559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3045559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3045559 prefixEnd_3045559 := by exact prefixLift 3045559
  have htrace : WordTrace (prefixWord ++ tailWord_3045559) baseStart_3045559 baseEnd_3045559 := by
    simpa [prefixWord, tailWord_3045559, baseEnd_3045559] using wordTrace_append hprefix tailTrace_3045559
  have hstable : (prefixWord ++ tailWord_3045559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3045559).length < 2 ^ (prefixWord ++ tailWord_3045559).sum := by decide
  have hdescent : baseEnd_3045559 < baseStart_3045559 := by decide
  rcases family_descends (prefixWord ++ tailWord_3045559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3045562 : List Nat := [3, 1, 1, 1, 2, 2, 3, 1, 1, 2, 6]
def baseStart_3045562 : Nat := 118140960795 + 3045562 * 2 ^ 59
def prefixEnd_3045562 : Nat := 4983230072969 + 3 ^ 40 * 3045562 * 2
def baseEnd_3045562 : Nat := 1563837169068518458368721

theorem tailTrace_3045562 : CollatzResearch.WordTrace tailWord_3045562 prefixEnd_3045562 1563837169068518458368721 := by
  unfold tailWord_3045562
  simp only [CollatzResearch.WordTrace]
  refine ⟨27770192948114122356050735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74053847861637659616135293 27770192948114122356050735)
  ·
    refine ⟨41655289422171183534076103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27770192948114122356050735 41655289422171183534076103)
    ·
      refine ⟨62482934133256775301114155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41655289422171183534076103 62482934133256775301114155)
      ·
        refine ⟨93724401199885162951671233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62482934133256775301114155 93724401199885162951671233)
        ·
          refine ⟨70293300899913872213753425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93724401199885162951671233 70293300899913872213753425)
          ·
            refine ⟨52719975674935404160315069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70293300899913872213753425 52719975674935404160315069)
            ·
              refine ⟨19769990878100776560118151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52719975674935404160315069 19769990878100776560118151)
              ·
                refine ⟨29654986317151164840177227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19769990878100776560118151 29654986317151164840177227)
                ·
                  refine ⟨44482479475726747260265841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29654986317151164840177227 44482479475726747260265841)
                  ·
                    refine ⟨33361859606795060445199381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 44482479475726747260265841 33361859606795060445199381)
                    ·
                      refine ⟨1563837169068518458368721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 33361859606795060445199381 1563837169068518458368721)
                      ·
                        rfl

theorem cell23_3045562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 1, 1, 2, 6].length) (baseStart_3045562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3045562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3045562 prefixEnd_3045562 := by exact prefixLift 3045562
  have htrace : WordTrace (prefixWord ++ tailWord_3045562) baseStart_3045562 baseEnd_3045562 := by
    simpa [prefixWord, tailWord_3045562, baseEnd_3045562] using wordTrace_append hprefix tailTrace_3045562
  have hstable : (prefixWord ++ tailWord_3045562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3045562).length < 2 ^ (prefixWord ++ tailWord_3045562).sum := by decide
  have hdescent : baseEnd_3045562 < baseStart_3045562 := by decide
  rcases family_descends (prefixWord ++ tailWord_3045562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3045570 : List Nat := [3, 5, 1, 1, 1, 1, 2, 1, 2, 4, 2]
def baseStart_3045570 : Nat := 118140960795 + 3045570 * 2 ^ 59
def prefixEnd_3045570 : Nat := 4983230072969 + 3 ^ 40 * 3045570 * 2
def baseEnd_3045570 : Nat := 1563841276913754427068685

theorem tailTrace_3045570 : CollatzResearch.WordTrace tailWord_3045570 prefixEnd_3045570 1563841276913754427068685 := by
  unfold tailWord_3045570
  simp only [CollatzResearch.WordTrace]
  refine ⟨27770265894106876697623541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74054042384285004526996109 27770265894106876697623541)
  ·
    refine ⟨2603462427572519690402207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 27770265894106876697623541 2603462427572519690402207)
    ·
      refine ⟨3905193641358779535603311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2603462427572519690402207 3905193641358779535603311)
      ·
        refine ⟨5857790462038169303404967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3905193641358779535603311 5857790462038169303404967)
        ·
          refine ⟨8786685693057253955107451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5857790462038169303404967 8786685693057253955107451)
          ·
            refine ⟨13180028539585880932661177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8786685693057253955107451 13180028539585880932661177)
            ·
              refine ⟨9885021404689410699495883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13180028539585880932661177 9885021404689410699495883)
              ·
                refine ⟨14827532107034116049243825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9885021404689410699495883 14827532107034116049243825)
                ·
                  refine ⟨11120649080275587036932869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14827532107034116049243825 11120649080275587036932869)
                  ·
                    refine ⟨2085121702551672569424913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11120649080275587036932869 2085121702551672569424913)
                    ·
                      refine ⟨1563841276913754427068685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2085121702551672569424913 1563841276913754427068685)
                      ·
                        rfl

theorem cell23_3045570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 2, 1, 2, 4, 2].length) (baseStart_3045570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3045570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3045570 prefixEnd_3045570 := by exact prefixLift 3045570
  have htrace : WordTrace (prefixWord ++ tailWord_3045570) baseStart_3045570 baseEnd_3045570 := by
    simpa [prefixWord, tailWord_3045570, baseEnd_3045570] using wordTrace_append hprefix tailTrace_3045570
  have hstable : (prefixWord ++ tailWord_3045570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3045570).length < 2 ^ (prefixWord ++ tailWord_3045570).sum := by decide
  have hdescent : baseEnd_3045570 < baseStart_3045570 := by decide
  rcases family_descends (prefixWord ++ tailWord_3045570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3045579 : List Nat := [1, 1, 1, 1, 3, 2, 3, 1, 3, 5, 2]
def baseStart_3045579 : Nat := 118140960795 + 3045579 * 2 ^ 59
def prefixEnd_3045579 : Nat := 4983230072969 + 3 ^ 40 * 3045579 * 2
def baseEnd_3045579 : Nat := 1563845898239644891856143

theorem tailTrace_3045579 : CollatzResearch.WordTrace tailWord_3045579 prefixEnd_3045579 1563845898239644891856143 := by
  unfold tailWord_3045579
  simp only [CollatzResearch.WordTrace]
  refine ⟨111081391833394901327571791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74054261222263267551714527 111081391833394901327571791)
  ·
    refine ⟨166622087750092351991357687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111081391833394901327571791 166622087750092351991357687)
    ·
      refine ⟨249933131625138527987036531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166622087750092351991357687 249933131625138527987036531)
      ·
        refine ⟨374899697437707791980554797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 249933131625138527987036531 374899697437707791980554797)
        ·
          refine ⟨140587386539140421992708049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 374899697437707791980554797 140587386539140421992708049)
          ·
            refine ⟨105440539904355316494531037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 140587386539140421992708049 105440539904355316494531037)
            ·
              refine ⟨39540202464133243685449139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 105440539904355316494531037 39540202464133243685449139)
              ·
                refine ⟨59310303696199865528173709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39540202464133243685449139 59310303696199865528173709)
                ·
                  refine ⟨22241363886074949573065141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59310303696199865528173709 22241363886074949573065141)
                  ·
                    refine ⟨2085127864319526522474857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 22241363886074949573065141 2085127864319526522474857)
                    ·
                      refine ⟨1563845898239644891856143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2085127864319526522474857 1563845898239644891856143)
                      ·
                        rfl

theorem cell23_3045579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 1, 3, 5, 2].length) (baseStart_3045579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3045579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3045579 prefixEnd_3045579 := by exact prefixLift 3045579
  have htrace : WordTrace (prefixWord ++ tailWord_3045579) baseStart_3045579 baseEnd_3045579 := by
    simpa [prefixWord, tailWord_3045579, baseEnd_3045579] using wordTrace_append hprefix tailTrace_3045579
  have hstable : (prefixWord ++ tailWord_3045579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3045579).length < 2 ^ (prefixWord ++ tailWord_3045579).sum := by decide
  have hdescent : baseEnd_3045579 < baseStart_3045579 := by decide
  rcases family_descends (prefixWord ++ tailWord_3045579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3045609 : List Nat := [1, 2, 1, 1, 1, 2, 2, 2, 1, 8, 2]
def baseStart_3045609 : Nat := 118140960795 + 3045609 * 2 ^ 59
def prefixEnd_3045609 : Nat := 4983230072969 + 3 ^ 40 * 3045609 * 2
def baseEnd_3045609 : Nat := 1563861302659279774481005

theorem tailTrace_3045609 : CollatzResearch.WordTrace tailWord_3045609 prefixEnd_3045609 1563861302659279774481005 := by
  unfold tailWord_3045609
  simp only [CollatzResearch.WordTrace]
  refine ⟨111082486023286216451163881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74054990682190810967442587 111082486023286216451163881)
  ·
    refine ⟨83311864517464662338372911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111082486023286216451163881 83311864517464662338372911)
    ·
      refine ⟨124967796776196993507559367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83311864517464662338372911 124967796776196993507559367)
      ·
        refine ⟨187451695164295490261339051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124967796776196993507559367 187451695164295490261339051)
        ·
          refine ⟨281177542746443235392008577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 187451695164295490261339051 281177542746443235392008577)
          ·
            refine ⟨210883157059832426544006433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 281177542746443235392008577 210883157059832426544006433)
            ·
              refine ⟨158162367794874319908004825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 210883157059832426544006433 158162367794874319908004825)
              ·
                refine ⟨118621775846155739931003619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 158162367794874319908004825 118621775846155739931003619)
                ·
                  refine ⟨177932663769233609896505429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 118621775846155739931003619 177932663769233609896505429)
                  ·
                    refine ⟨2085148403545706365974673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 177932663769233609896505429 2085148403545706365974673)
                    ·
                      refine ⟨1563861302659279774481005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2085148403545706365974673 1563861302659279774481005)
                      ·
                        rfl

theorem cell23_3045609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 2, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 2, 1, 8, 2].length) (baseStart_3045609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3045609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3045609 prefixEnd_3045609 := by exact prefixLift 3045609
  have htrace : WordTrace (prefixWord ++ tailWord_3045609) baseStart_3045609 baseEnd_3045609 := by
    simpa [prefixWord, tailWord_3045609, baseEnd_3045609] using wordTrace_append hprefix tailTrace_3045609
  have hstable : (prefixWord ++ tailWord_3045609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3045609).length < 2 ^ (prefixWord ++ tailWord_3045609).sum := by decide
  have hdescent : baseEnd_3045609 < baseStart_3045609 := by decide
  rcases family_descends (prefixWord ++ tailWord_3045609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3045619 : List Nat := [1, 1, 1, 2, 2, 4, 1, 3, 4, 4]
def baseStart_3045619 : Nat := 118140960795 + 3045619 * 2 ^ 59
def prefixEnd_3045619 : Nat := 4983230072969 + 3 ^ 40 * 3045619 * 2
def baseEnd_3045619 : Nat := 521288812488608245118653

theorem tailTrace_3045619 : CollatzResearch.WordTrace tailWord_3045619 prefixEnd_3045619 521288812488608245118653 := by
  unfold tailWord_3045619
  simp only [CollatzResearch.WordTrace]
  refine ⟨111082850753249988159027911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74055233835499992106018607 111082850753249988159027911)
  ·
    refine ⟨166624276129874982238541867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111082850753249988159027911 166624276129874982238541867)
    ·
      refine ⟨249936414194812473357812801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166624276129874982238541867 249936414194812473357812801)
      ·
        refine ⟨187452310646109355018359601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 249936414194812473357812801 187452310646109355018359601)
        ·
          refine ⟨140589232984582016263769701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 187452310646109355018359601 140589232984582016263769701)
          ·
            refine ⟨26360481184609128049456819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 140589232984582016263769701 26360481184609128049456819)
            ·
              refine ⟨39540721776913692074185229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26360481184609128049456819 39540721776913692074185229)
              ·
                refine ⟨14827770666342634527819461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39540721776913692074185229 14827770666342634527819461)
                ·
                  refine ⟨2780206999939243973966149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14827770666342634527819461 2780206999939243973966149)
                  ·
                    refine ⟨521288812488608245118653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2780206999939243973966149 521288812488608245118653)
                    ·
                      rfl

theorem cell23_3045619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 3, 4, 4].length) (baseStart_3045619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3045619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3045619 prefixEnd_3045619 := by exact prefixLift 3045619
  have htrace : WordTrace (prefixWord ++ tailWord_3045619) baseStart_3045619 baseEnd_3045619 := by
    simpa [prefixWord, tailWord_3045619, baseEnd_3045619] using wordTrace_append hprefix tailTrace_3045619
  have hstable : (prefixWord ++ tailWord_3045619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3045619).length < 2 ^ (prefixWord ++ tailWord_3045619).sum := by decide
  have hdescent : baseEnd_3045619 < baseStart_3045619 := by decide
  rcases family_descends (prefixWord ++ tailWord_3045619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3045632 : List Nat := [2, 1, 1, 2, 1, 1, 5, 10]
def baseStart_3045632 : Nat := 118140960795 + 3045632 * 2 ^ 59
def prefixEnd_3045632 : Nat := 4983230072969 + 3 ^ 40 * 3045632 * 2
def baseEnd_3045632 : Nat := 57921226396827154981237

theorem tailTrace_3045632 : CollatzResearch.WordTrace tailWord_3045632 prefixEnd_3045632 57921226396827154981237 := by
  unfold tailWord_3045632
  simp only [CollatzResearch.WordTrace]
  refine ⟨55541662451101445689625575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74055549934801927586167433 55541662451101445689625575)
  ·
    refine ⟨83312493676652168534438363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55541662451101445689625575 83312493676652168534438363)
    ·
      refine ⟨124968740514978252801657545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83312493676652168534438363 124968740514978252801657545)
      ·
        refine ⟨93726555386233689601243159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124968740514978252801657545 93726555386233689601243159)
        ·
          refine ⟨140589833079350534401864739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93726555386233689601243159 140589833079350534401864739)
          ·
            refine ⟨210884749619025801602797109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140589833079350534401864739 210884749619025801602797109)
            ·
              refine ⟨19770445276783668900262229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 210884749619025801602797109 19770445276783668900262229)
              ·
                refine ⟨57921226396827154981237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 19770445276783668900262229 57921226396827154981237)
                ·
                  rfl

theorem cell23_3045632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 10].length) (baseStart_3045632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3045632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3045632 prefixEnd_3045632 := by exact prefixLift 3045632
  have htrace : WordTrace (prefixWord ++ tailWord_3045632) baseStart_3045632 baseEnd_3045632 := by
    simpa [prefixWord, tailWord_3045632, baseEnd_3045632] using wordTrace_append hprefix tailTrace_3045632
  have hstable : (prefixWord ++ tailWord_3045632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3045632).length < 2 ^ (prefixWord ++ tailWord_3045632).sum := by decide
  have hdescent : baseEnd_3045632 < baseStart_3045632 := by decide
  rcases family_descends (prefixWord ++ tailWord_3045632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3045646 : List Nat := [4, 1, 1, 2, 1, 2, 3, 1, 3, 2, 3]
def baseStart_3045646 : Nat := 118140960795 + 3045646 * 2 ^ 59
def prefixEnd_3045646 : Nat := 4983230072969 + 3 ^ 40 * 3045646 * 2
def baseEnd_3045646 : Nat := 1563880301443496129718335

theorem tailTrace_3045646 : CollatzResearch.WordTrace tailWord_3045646 prefixEnd_3045646 1563880301443496129718335 := by
  unfold tailWord_3045646
  simp only [CollatzResearch.WordTrace]
  refine ⟨13885479440519021471282599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74055890349434781180173861 13885479440519021471282599)
  ·
    refine ⟨20828219160778532206923899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13885479440519021471282599 20828219160778532206923899)
    ·
      refine ⟨31242328741167798310385849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20828219160778532206923899 31242328741167798310385849)
      ·
        refine ⟨23431746555875848732789387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31242328741167798310385849 23431746555875848732789387)
        ·
          refine ⟨35147619833813773099184081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23431746555875848732789387 35147619833813773099184081)
          ·
            refine ⟨26360714875360329824388061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35147619833813773099184081 26360714875360329824388061)
            ·
              refine ⟨9885268078260123684145523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26360714875360329824388061 9885268078260123684145523)
              ·
                refine ⟨14827902117390185526218285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9885268078260123684145523 14827902117390185526218285)
                ·
                  refine ⟨5560463294021319572331857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14827902117390185526218285 5560463294021319572331857)
                  ·
                    refine ⟨4170347470515989679248893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5560463294021319572331857 4170347470515989679248893)
                    ·
                      refine ⟨1563880301443496129718335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4170347470515989679248893 1563880301443496129718335)
                      ·
                        rfl

theorem cell23_3045646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 3, 1, 3, 2, 3].length) (baseStart_3045646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3045646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3045646 prefixEnd_3045646 := by exact prefixLift 3045646
  have htrace : WordTrace (prefixWord ++ tailWord_3045646) baseStart_3045646 baseEnd_3045646 := by
    simpa [prefixWord, tailWord_3045646, baseEnd_3045646] using wordTrace_append hprefix tailTrace_3045646
  have hstable : (prefixWord ++ tailWord_3045646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3045646).length < 2 ^ (prefixWord ++ tailWord_3045646).sum := by decide
  have hdescent : baseEnd_3045646 < baseStart_3045646 := by decide
  rcases family_descends (prefixWord ++ tailWord_3045646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3045659 : List Nat := [1, 1, 1, 1, 1, 1, 7, 1, 3, 3, 3]
def baseStart_3045659 : Nat := 118140960795 + 3045659 * 2 ^ 59
def prefixEnd_3045659 : Nat := 4983230072969 + 3 ^ 40 * 3045659 * 2
def baseEnd_3045659 : Nat := 1563886976692004578855775

theorem tailTrace_3045659 : CollatzResearch.WordTrace tailWord_3045659 prefixEnd_3045659 1563886976692004578855775 := by
  unfold tailWord_3045659
  simp only [CollatzResearch.WordTrace]
  refine ⟨111084309673105074990484031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74056206448736716660322687 111084309673105074990484031)
  ·
    refine ⟨166626464509657612485726047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111084309673105074990484031 166626464509657612485726047)
    ·
      refine ⟨249939696764486418728589071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166626464509657612485726047 249939696764486418728589071)
      ·
        refine ⟨374909545146729628092883607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 249939696764486418728589071 374909545146729628092883607)
        ·
          refine ⟨562364317720094442139325411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 374909545146729628092883607 562364317720094442139325411)
          ·
            refine ⟨843546476580141663208988117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 562364317720094442139325411 843546476580141663208988117)
            ·
              refine ⟨19770620544847070231460659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 843546476580141663208988117 19770620544847070231460659)
              ·
                refine ⟨29655930817270605347190989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19770620544847070231460659 29655930817270605347190989)
                ·
                  refine ⟨11120974056476477005196621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29655930817270605347190989 11120974056476477005196621)
                  ·
                    refine ⟨4170365271178678876948733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11120974056476477005196621 4170365271178678876948733)
                    ·
                      refine ⟨1563886976692004578855775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4170365271178678876948733 1563886976692004578855775)
                      ·
                        rfl

theorem cell23_3045659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 1, 3, 3, 3].length) (baseStart_3045659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3045659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3045659 prefixEnd_3045659 := by exact prefixLift 3045659
  have htrace : WordTrace (prefixWord ++ tailWord_3045659) baseStart_3045659 baseEnd_3045659 := by
    simpa [prefixWord, tailWord_3045659, baseEnd_3045659] using wordTrace_append hprefix tailTrace_3045659
  have hstable : (prefixWord ++ tailWord_3045659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3045659).length < 2 ^ (prefixWord ++ tailWord_3045659).sum := by decide
  have hdescent : baseEnd_3045659 < baseStart_3045659 := by decide
  rcases family_descends (prefixWord ++ tailWord_3045659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3045660 : List Nat := [2, 2, 3, 1, 1, 1, 1, 7, 1, 2, 2]
def baseStart_3045660 : Nat := 118140960795 + 3045660 * 2 ^ 59
def prefixEnd_3045660 : Nat := 4983230072969 + 3 ^ 40 * 3045660 * 2
def baseEnd_3045660 : Nat := 1563887490172659074943271

theorem tailTrace_3045660 : CollatzResearch.WordTrace tailWord_3045660 prefixEnd_3045660 1563887490172659074943271 := by
  unfold tailWord_3045660
  simp only [CollatzResearch.WordTrace]
  refine ⟨55542173073050726080635217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74056230764067634774180289 55542173073050726080635217)
  ·
    refine ⟨41656629804788044560476413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55542173073050726080635217 41656629804788044560476413)
    ·
      refine ⟨15621236176795516710178655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41656629804788044560476413 15621236176795516710178655)
      ·
        refine ⟨23431854265193275065267983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15621236176795516710178655 23431854265193275065267983)
        ·
          refine ⟨35147781397789912597901975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23431854265193275065267983 35147781397789912597901975)
          ·
            refine ⟨52721672096684868896852963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35147781397789912597901975 52721672096684868896852963)
            ·
              refine ⟨79082508145027303345279445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52721672096684868896852963 79082508145027303345279445)
              ·
                refine ⟨1853496284649077422154987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 79082508145027303345279445 1853496284649077422154987)
                ·
                  refine ⟨2780244426973616133232481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1853496284649077422154987 2780244426973616133232481)
                  ·
                    refine ⟨2085183320230212099924361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2780244426973616133232481 2085183320230212099924361)
                    ·
                      refine ⟨1563887490172659074943271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2085183320230212099924361 1563887490172659074943271)
                      ·
                        rfl

theorem cell23_3045660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 7, 1, 2, 2].length) (baseStart_3045660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3045660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3045660 prefixEnd_3045660 := by exact prefixLift 3045660
  have htrace : WordTrace (prefixWord ++ tailWord_3045660) baseStart_3045660 baseEnd_3045660 := by
    simpa [prefixWord, tailWord_3045660, baseEnd_3045660] using wordTrace_append hprefix tailTrace_3045660
  have hstable : (prefixWord ++ tailWord_3045660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3045660).length < 2 ^ (prefixWord ++ tailWord_3045660).sum := by decide
  have hdescent : baseEnd_3045660 < baseStart_3045660 := by decide
  rcases family_descends (prefixWord ++ tailWord_3045660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3045676 : List Nat := [2, 2, 1, 1, 1, 3, 2, 3, 4, 1, 3]
def baseStart_3045676 : Nat := 118140960795 + 3045676 * 2 ^ 59
def prefixEnd_3045676 : Nat := 4983230072969 + 3 ^ 40 * 3045676 * 2
def baseEnd_3045676 : Nat := 1563895705863131012343197

theorem tailTrace_3045676 : CollatzResearch.WordTrace tailWord_3045676 prefixEnd_3045676 1563895705863131012343197 := by
  unfold tailWord_3045676
  simp only [CollatzResearch.WordTrace]
  refine ⟨55542464857021743446926441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74056619809362324595901921 55542464857021743446926441)
  ·
    refine ⟨41656848642766307585194831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55542464857021743446926441 41656848642766307585194831)
    ·
      refine ⟨62485272964149461377792247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41656848642766307585194831 62485272964149461377792247)
      ·
        refine ⟨93727909446224192066688371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62485272964149461377792247 93727909446224192066688371)
        ·
          refine ⟨140591864169336288100032557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93727909446224192066688371 140591864169336288100032557)
          ·
            refine ⟨52721949063501108037512209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 140591864169336288100032557 52721949063501108037512209)
            ·
              refine ⟨39541461797625831028134157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52721949063501108037512209 39541461797625831028134157)
              ·
                refine ⟨14828048174109686635550309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39541461797625831028134157 14828048174109686635550309)
                ·
                  refine ⟨2780259032645566244165683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14828048174109686635550309 2780259032645566244165683)
                  ·
                    refine ⟨4170388548968349366248525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2780259032645566244165683 4170388548968349366248525)
                    ·
                      refine ⟨1563895705863131012343197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4170388548968349366248525 1563895705863131012343197)
                      ·
                        rfl

theorem cell23_3045676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 1, 3].length) (baseStart_3045676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3045676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3045676 prefixEnd_3045676 := by exact prefixLift 3045676
  have htrace : WordTrace (prefixWord ++ tailWord_3045676) baseStart_3045676 baseEnd_3045676 := by
    simpa [prefixWord, tailWord_3045676, baseEnd_3045676] using wordTrace_append hprefix tailTrace_3045676
  have hstable : (prefixWord ++ tailWord_3045676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3045676).length < 2 ^ (prefixWord ++ tailWord_3045676).sum := by decide
  have hdescent : baseEnd_3045676 < baseStart_3045676 := by decide
  rcases family_descends (prefixWord ++ tailWord_3045676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3045703 : List Nat := [1, 1, 4, 1, 2, 2, 2, 4, 1, 3, 2]
def baseStart_3045703 : Nat := 118140960795 + 3045703 * 2 ^ 59
def prefixEnd_3045703 : Nat := 4983230072969 + 3 ^ 40 * 3045703 * 2
def baseEnd_3045703 : Nat := 1563909569840802406705573

theorem tailTrace_3045703 : CollatzResearch.WordTrace tailWord_3045703 prefixEnd_3045703 1563909569840802406705573 := by
  unfold tailWord_3045703
  simp only [CollatzResearch.WordTrace]
  refine ⟨111085914484945670505085763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74057276323297113670057175 111085914484945670505085763)
  ·
    refine ⟨166628871727418505757628645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111085914484945670505085763 166628871727418505757628645)
    ·
      refine ⟨31242913448890969829555371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 166628871727418505757628645 31242913448890969829555371)
      ·
        refine ⟨46864370173336454744333057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31242913448890969829555371 46864370173336454744333057)
        ·
          refine ⟨35148277630002341058249793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46864370173336454744333057 35148277630002341058249793)
          ·
            refine ⟨26361208222501755793687345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35148277630002341058249793 26361208222501755793687345)
            ·
              refine ⟨19770906166876316845265509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26361208222501755793687345 19770906166876316845265509)
              ·
                refine ⟨3707044906289309408487283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19770906166876316845265509 3707044906289309408487283)
                ·
                  refine ⟨5560567359433964112730925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3707044906289309408487283 5560567359433964112730925)
                  ·
                    refine ⟨2085212759787736542274097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5560567359433964112730925 2085212759787736542274097)
                    ·
                      refine ⟨1563909569840802406705573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2085212759787736542274097 1563909569840802406705573)
                      ·
                        rfl

theorem cell23_3045703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 4, 1, 3, 2].length) (baseStart_3045703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3045703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3045703 prefixEnd_3045703 := by exact prefixLift 3045703
  have htrace : WordTrace (prefixWord ++ tailWord_3045703) baseStart_3045703 baseEnd_3045703 := by
    simpa [prefixWord, tailWord_3045703, baseEnd_3045703] using wordTrace_append hprefix tailTrace_3045703
  have hstable : (prefixWord ++ tailWord_3045703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3045703).length < 2 ^ (prefixWord ++ tailWord_3045703).sum := by decide
  have hdescent : baseEnd_3045703 < baseStart_3045703 := by decide
  rcases family_descends (prefixWord ++ tailWord_3045703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3045719 : List Nat := [1, 1, 3, 2, 3, 1, 2, 1, 1, 3, 5]
def baseStart_3045719 : Nat := 118140960795 + 3045719 * 2 ^ 59
def prefixEnd_3045719 : Nat := 4983230072969 + 3 ^ 40 * 3045719 * 2
def baseEnd_3045719 : Nat := 1563917785531274344105499

theorem tailTrace_3045719 : CollatzResearch.WordTrace tailWord_3045719 prefixEnd_3045719 1563917785531274344105499 := by
  unfold tailWord_3045719
  simp only [CollatzResearch.WordTrace]
  refine ⟨111086498052887705237668211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74057665368591803491778807 111086498052887705237668211)
  ·
    refine ⟨166629747079331557856502317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111086498052887705237668211 166629747079331557856502317)
    ·
      refine ⟨62486155154749334196188369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 166629747079331557856502317 62486155154749334196188369)
      ·
        refine ⟨46864616366062000647141277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62486155154749334196188369 46864616366062000647141277)
        ·
          refine ⟨17574231137273250242677979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46864616366062000647141277 17574231137273250242677979)
          ·
            refine ⟨26361346705909875364016969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17574231137273250242677979 26361346705909875364016969)
            ·
              refine ⟨19771010029432406523012727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26361346705909875364016969 19771010029432406523012727)
              ·
                refine ⟨29656515044148609784519091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19771010029432406523012727 29656515044148609784519091)
                ·
                  refine ⟨44484772566222914676778637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29656515044148609784519091 44484772566222914676778637)
                  ·
                    refine ⟨16681789712333593003791989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 44484772566222914676778637 16681789712333593003791989)
                    ·
                      refine ⟨1563917785531274344105499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16681789712333593003791989 1563917785531274344105499)
                      ·
                        rfl

theorem cell23_3045719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 1, 1, 3, 5].length) (baseStart_3045719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3045719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3045719 prefixEnd_3045719 := by exact prefixLift 3045719
  have htrace : WordTrace (prefixWord ++ tailWord_3045719) baseStart_3045719 baseEnd_3045719 := by
    simpa [prefixWord, tailWord_3045719, baseEnd_3045719] using wordTrace_append hprefix tailTrace_3045719
  have hstable : (prefixWord ++ tailWord_3045719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3045719).length < 2 ^ (prefixWord ++ tailWord_3045719).sum := by decide
  have hdescent : baseEnd_3045719 < baseStart_3045719 := by decide
  rcases family_descends (prefixWord ++ tailWord_3045719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3045746 : List Nat := [3, 2, 1, 2, 1, 3, 2, 1, 2, 2, 4]
def baseStart_3045746 : Nat := 118140960795 + 3045746 * 2 ^ 59
def prefixEnd_3045746 : Nat := 4983230072969 + 3 ^ 40 * 3045746 * 2
def baseEnd_3045746 : Nat := 1563931649508945738467875

theorem tailTrace_3045746 : CollatzResearch.WordTrace tailWord_3045746 prefixEnd_3045746 1563931649508945738467875 := by
  unfold tailWord_3045746
  simp only [CollatzResearch.WordTrace]
  refine ⟨27771870705947472212225273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74058321882526592565934061 27771870705947472212225273)
  ·
    refine ⟨20828903029460604159168955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27771870705947472212225273 20828903029460604159168955)
    ·
      refine ⟨31243354544190906238753433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20828903029460604159168955 31243354544190906238753433)
      ·
        refine ⟨23432515908143179679065075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31243354544190906238753433 23432515908143179679065075)
        ·
          refine ⟨35148773862214769518597613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23432515908143179679065075 35148773862214769518597613)
          ·
            refine ⟨13180790198330538569474105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35148773862214769518597613 13180790198330538569474105)
            ·
              refine ⟨9885592648747903927105579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13180790198330538569474105 9885592648747903927105579)
              ·
                refine ⟨14828388973121855890658369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9885592648747903927105579 14828388973121855890658369)
                ·
                  refine ⟨11121291729841391917993777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14828388973121855890658369 11121291729841391917993777)
                  ·
                    refine ⟨8340968797381043938495333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11121291729841391917993777 8340968797381043938495333)
                    ·
                      refine ⟨1563931649508945738467875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8340968797381043938495333 1563931649508945738467875)
                      ·
                        rfl

theorem cell23_3045746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 2, 1, 2, 2, 4].length) (baseStart_3045746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3045746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3045746 prefixEnd_3045746 := by exact prefixLift 3045746
  have htrace : WordTrace (prefixWord ++ tailWord_3045746) baseStart_3045746 baseEnd_3045746 := by
    simpa [prefixWord, tailWord_3045746, baseEnd_3045746] using wordTrace_append hprefix tailTrace_3045746
  have hstable : (prefixWord ++ tailWord_3045746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3045746).length < 2 ^ (prefixWord ++ tailWord_3045746).sum := by decide
  have hdescent : baseEnd_3045746 < baseStart_3045746 := by decide
  rcases family_descends (prefixWord ++ tailWord_3045746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3045776 : List Nat := [2, 1, 1, 1, 1, 1, 2, 1, 6, 5, 2]
def baseStart_3045776 : Nat := 118140960795 + 3045776 * 2 ^ 59
def prefixEnd_3045776 : Nat := 4983230072969 + 3 ^ 40 * 3045776 * 2
def baseEnd_3045776 : Nat := 1563947053928580621092737

theorem tailTrace_3045776 : CollatzResearch.WordTrace tailWord_3045776 prefixEnd_3045776 1563947053928580621092737 := by
  unfold tailWord_3045776
  simp only [CollatzResearch.WordTrace]
  refine ⟨55544288506840601986246591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74059051342454135981662121 55544288506840601986246591)
  ·
    refine ⟨83316432760260902979369887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55544288506840601986246591 83316432760260902979369887)
    ·
      refine ⟨124974649140391354469054831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83316432760260902979369887 124974649140391354469054831)
      ·
        refine ⟨187461973710587031703582247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124974649140391354469054831 187461973710587031703582247)
        ·
          refine ⟨281192960565880547555373371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 187461973710587031703582247 281192960565880547555373371)
          ·
            refine ⟨421789440848820821333060057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 281192960565880547555373371 421789440848820821333060057)
            ·
              refine ⟨316342080636615615999795043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 421789440848820821333060057 316342080636615615999795043)
              ·
                refine ⟨474513120954923423999692565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 316342080636615615999795043 474513120954923423999692565)
                ·
                  refine ⟨22242802544762035499985589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 474513120954923423999692565 22242802544762035499985589)
                  ·
                    refine ⟨2085262738571440828123649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 22242802544762035499985589 2085262738571440828123649)
                    ·
                      refine ⟨1563947053928580621092737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2085262738571440828123649 1563947053928580621092737)
                      ·
                        rfl

theorem cell23_3045776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 6, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 6, 5, 2].length) (baseStart_3045776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3045776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3045776 prefixEnd_3045776 := by exact prefixLift 3045776
  have htrace : WordTrace (prefixWord ++ tailWord_3045776) baseStart_3045776 baseEnd_3045776 := by
    simpa [prefixWord, tailWord_3045776, baseEnd_3045776] using wordTrace_append hprefix tailTrace_3045776
  have hstable : (prefixWord ++ tailWord_3045776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3045776).length < 2 ^ (prefixWord ++ tailWord_3045776).sum := by decide
  have hdescent : baseEnd_3045776 < baseStart_3045776 := by decide
  rcases family_descends (prefixWord ++ tailWord_3045776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3045786 : List Nat := [3, 1, 1, 4, 1, 2, 1, 1, 4, 5]
def baseStart_3045786 : Nat := 118140960795 + 3045786 * 2 ^ 59
def prefixEnd_3045786 : Nat := 4983230072969 + 3 ^ 40 * 3045786 * 2
def baseEnd_3045786 : Nat := 521317396245041860655897

theorem tailTrace_3045786 : CollatzResearch.WordTrace tailWord_3045786 prefixEnd_3045786 521317396245041860655897 := by
  unfold tailWord_3045786
  simp only [CollatzResearch.WordTrace]
  refine ⟨27772235435911243920089303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74059294495763317120238141 27772235435911243920089303)
  ·
    refine ⟨41658353153866865880133955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27772235435911243920089303 41658353153866865880133955)
    ·
      refine ⟨62487529730800298820200933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41658353153866865880133955 62487529730800298820200933)
      ·
        refine ⟨11716411824525056028787675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 62487529730800298820200933 11716411824525056028787675)
        ·
          refine ⟨17574617736787584043181513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11716411824525056028787675 17574617736787584043181513)
          ·
            refine ⟨13180963302590688032386135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17574617736787584043181513 13180963302590688032386135)
            ·
              refine ⟨19771444953886032048579203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13180963302590688032386135 19771444953886032048579203)
              ·
                refine ⟨29657167430829048072868805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19771444953886032048579203 29657167430829048072868805)
                ·
                  refine ⟨5560718893280446513662901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29657167430829048072868805 5560718893280446513662901)
                  ·
                    refine ⟨521317396245041860655897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5560718893280446513662901 521317396245041860655897)
                    ·
                      rfl

theorem cell23_3045786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 1, 4, 5].length) (baseStart_3045786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3045786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3045786 prefixEnd_3045786 := by exact prefixLift 3045786
  have htrace : WordTrace (prefixWord ++ tailWord_3045786) baseStart_3045786 baseEnd_3045786 := by
    simpa [prefixWord, tailWord_3045786, baseEnd_3045786] using wordTrace_append hprefix tailTrace_3045786
  have hstable : (prefixWord ++ tailWord_3045786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3045786).length < 2 ^ (prefixWord ++ tailWord_3045786).sum := by decide
  have hdescent : baseEnd_3045786 < baseStart_3045786 := by decide
  rcases family_descends (prefixWord ++ tailWord_3045786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3045790 : List Nat := [4, 3, 1, 2, 1, 3, 1, 1, 7]
def baseStart_3045790 : Nat := 118140960795 + 3045790 * 2 ^ 59
def prefixEnd_3045790 : Nat := 4983230072969 + 3 ^ 40 * 3045790 * 2
def baseEnd_3045790 : Nat := 173772693628638174035297

theorem tailTrace_3045790 : CollatzResearch.WordTrace tailWord_3045790 prefixEnd_3045790 173772693628638174035297 := by
  unfold tailWord_3045790
  simp only [CollatzResearch.WordTrace]
  refine ⟨13886135954453810545437853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74059391757086989575668549 13886135954453810545437853)
  ·
    refine ⟨5207300982920178954539195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13886135954453810545437853 5207300982920178954539195)
    ·
      refine ⟨7810951474380268431808793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5207300982920178954539195 7810951474380268431808793)
      ·
        refine ⟨5858213605785201323856595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7810951474380268431808793 5858213605785201323856595)
        ·
          refine ⟨8787320408677801985784893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5858213605785201323856595 8787320408677801985784893)
          ·
            refine ⟨3295245153254175744669335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8787320408677801985784893 3295245153254175744669335)
            ·
              refine ⟨4942867729881263617004003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3295245153254175744669335 4942867729881263617004003)
              ·
                refine ⟨7414301594821895425506005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4942867729881263617004003 7414301594821895425506005)
                ·
                  refine ⟨173772693628638174035297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7414301594821895425506005 173772693628638174035297)
                  ·
                    rfl

theorem cell23_3045790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 3, 1, 1, 7].length) (baseStart_3045790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3045790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3045790 prefixEnd_3045790 := by exact prefixLift 3045790
  have htrace : WordTrace (prefixWord ++ tailWord_3045790) baseStart_3045790 baseEnd_3045790 := by
    simpa [prefixWord, tailWord_3045790, baseEnd_3045790] using wordTrace_append hprefix tailTrace_3045790
  have hstable : (prefixWord ++ tailWord_3045790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3045790).length < 2 ^ (prefixWord ++ tailWord_3045790).sum := by decide
  have hdescent : baseEnd_3045790 < baseStart_3045790 := by decide
  rcases family_descends (prefixWord ++ tailWord_3045790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3045816 : List Nat := [2, 1, 2, 1, 2, 2, 1, 3, 5, 4]
def baseStart_3045816 : Nat := 118140960795 + 3045816 * 2 ^ 59
def prefixEnd_3045816 : Nat := 4983230072969 + 3 ^ 40 * 3045816 * 2
def baseEnd_3045816 : Nat := 521322531051586821530851

theorem tailTrace_3045816 : CollatzResearch.WordTrace tailWord_3045816 prefixEnd_3045816 521322531051586821530851 := by
  unfold tailWord_3045816
  simp only [CollatzResearch.WordTrace]
  refine ⟨55545017966768145401974651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74060023955690860535966201 55545017966768145401974651)
  ·
    refine ⟨83317526950152218102961977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55545017966768145401974651 83317526950152218102961977)
    ·
      refine ⟨62488145212614163577221483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83317526950152218102961977 62488145212614163577221483)
      ·
        refine ⟨93732217818921245365832225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62488145212614163577221483 93732217818921245365832225)
        ·
          refine ⟨70299163364190934024374169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93732217818921245365832225 70299163364190934024374169)
          ·
            refine ⟨52724372523143200518280627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70299163364190934024374169 52724372523143200518280627)
            ·
              refine ⟨79086558784714800777420941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52724372523143200518280627 79086558784714800777420941)
              ·
                refine ⟨29657459544268050291532853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 79086558784714800777420941 29657459544268050291532853)
                ·
                  refine ⟨2780386832275129714831205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 29657459544268050291532853 2780386832275129714831205)
                  ·
                    refine ⟨521322531051586821530851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2780386832275129714831205 521322531051586821530851)
                    ·
                      rfl

theorem cell23_3045816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 3, 5, 4].length) (baseStart_3045816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3045816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3045816 prefixEnd_3045816 := by exact prefixLift 3045816
  have htrace : WordTrace (prefixWord ++ tailWord_3045816) baseStart_3045816 baseEnd_3045816 := by
    simpa [prefixWord, tailWord_3045816, baseEnd_3045816] using wordTrace_append hprefix tailTrace_3045816
  have hstable : (prefixWord ++ tailWord_3045816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3045816).length < 2 ^ (prefixWord ++ tailWord_3045816).sum := by decide
  have hdescent : baseEnd_3045816 < baseStart_3045816 := by decide
  rcases family_descends (prefixWord ++ tailWord_3045816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3045819 : List Nat := [1, 1, 1, 1, 1, 2, 2, 1, 6, 1, 6]
def baseStart_3045819 : Nat := 118140960795 + 3045819 * 2 ^ 59
def prefixEnd_3045819 : Nat := 4983230072969 + 3 ^ 40 * 3045819 * 2
def baseEnd_3045819 : Nat := 1563969133596723952855039

theorem tailTrace_3045819 : CollatzResearch.WordTrace tailWord_3045819 prefixEnd_3045819 1563969133596723952855039 := by
  unfold tailWord_3045819
  simp only [CollatzResearch.WordTrace]
  refine ⟨111090145352525422316308511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74060096901683614877539007 111090145352525422316308511)
  ·
    refine ⟨166635218028788133474462767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111090145352525422316308511 166635218028788133474462767)
    ·
      refine ⟨249952827043182200211694151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166635218028788133474462767 249952827043182200211694151)
      ·
        refine ⟨374929240564773300317541227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 249952827043182200211694151 374929240564773300317541227)
        ·
          refine ⟨562393860847159950476311841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 374929240564773300317541227 562393860847159950476311841)
          ·
            refine ⟨421795395635369962857233881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 562393860847159950476311841 421795395635369962857233881)
            ·
              refine ⟨316346546726527472142925411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 421795395635369962857233881 316346546726527472142925411)
              ·
                refine ⟨474519820089791208214388117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 316346546726527472142925411 474519820089791208214388117)
                ·
                  refine ⟨22243116566708962885049443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 474519820089791208214388117 22243116566708962885049443)
                  ·
                    refine ⟨33364674850063444327574165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22243116566708962885049443 33364674850063444327574165)
                    ·
                      refine ⟨1563969133596723952855039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 33364674850063444327574165 1563969133596723952855039)
                      ·
                        rfl

theorem cell23_3045819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 6, 1, 6].length) (baseStart_3045819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3045819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3045819 prefixEnd_3045819 := by exact prefixLift 3045819
  have htrace : WordTrace (prefixWord ++ tailWord_3045819) baseStart_3045819 baseEnd_3045819 := by
    simpa [prefixWord, tailWord_3045819, baseEnd_3045819] using wordTrace_append hprefix tailTrace_3045819
  have hstable : (prefixWord ++ tailWord_3045819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3045819).length < 2 ^ (prefixWord ++ tailWord_3045819).sum := by decide
  have hdescent : baseEnd_3045819 < baseStart_3045819 := by decide
  rcases family_descends (prefixWord ++ tailWord_3045819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3045850 : List Nat := [3, 1, 1, 2, 3, 1, 3, 4, 1, 4]
def baseStart_3045850 : Nat := 118140960795 + 3045850 * 2 ^ 59
def prefixEnd_3045850 : Nat := 4983230072969 + 3 ^ 40 * 3045850 * 2
def baseEnd_3045850 : Nat := 521328350499004443855799

theorem tailTrace_3045850 : CollatzResearch.WordTrace tailWord_3045850 prefixEnd_3045850 521328350499004443855799 := by
  unfold tailWord_3045850
  simp only [CollatzResearch.WordTrace]
  refine ⟨27772819003853278652671751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74060850676942076407124669 27772819003853278652671751)
  ·
    refine ⟨41659228505779917979007627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27772819003853278652671751 41659228505779917979007627)
    ·
      refine ⟨62488842758669876968511441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41659228505779917979007627 62488842758669876968511441)
      ·
        refine ⟨46866632069002407726383581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62488842758669876968511441 46866632069002407726383581)
        ·
          refine ⟨17574987025875902897393843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46866632069002407726383581 17574987025875902897393843)
          ·
            refine ⟨26362480538813854346090765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17574987025875902897393843 26362480538813854346090765)
            ·
              refine ⟨9885930202055195379784037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26362480538813854346090765 9885930202055195379784037)
              ·
                refine ⟨1853611912885349133709507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9885930202055195379784037 1853611912885349133709507)
                ·
                  refine ⟨2780417869328023700564261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1853611912885349133709507 2780417869328023700564261)
                  ·
                    refine ⟨521328350499004443855799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2780417869328023700564261 521328350499004443855799)
                    ·
                      rfl

theorem cell23_3045850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 3, 4, 1, 4].length) (baseStart_3045850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3045850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3045850 prefixEnd_3045850 := by exact prefixLift 3045850
  have htrace : WordTrace (prefixWord ++ tailWord_3045850) baseStart_3045850 baseEnd_3045850 := by
    simpa [prefixWord, tailWord_3045850, baseEnd_3045850] using wordTrace_append hprefix tailTrace_3045850
  have hstable : (prefixWord ++ tailWord_3045850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3045850).length < 2 ^ (prefixWord ++ tailWord_3045850).sum := by decide
  have hdescent : baseEnd_3045850 < baseStart_3045850 := by decide
  rcases family_descends (prefixWord ++ tailWord_3045850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3045923 : List Nat := [1, 1, 1, 4, 4, 1, 3, 1, 1, 6]
def baseStart_3045923 : Nat := 118140960795 + 3045923 * 2 ^ 59
def prefixEnd_3045923 : Nat := 4983230072969 + 3 ^ 40 * 3045923 * 2
def baseEnd_3045923 : Nat := 521340845194930515318187

theorem tailTrace_3045923 : CollatzResearch.WordTrace tailWord_3045923 prefixEnd_3045923 521340845194930515318187 := by
  unfold tailWord_3045923
  simp only [CollatzResearch.WordTrace]
  refine ⟨111093938544148648078094423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74062625696099098718729615 111093938544148648078094423)
  ·
    refine ⟨166640907816222972117141635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111093938544148648078094423 166640907816222972117141635)
    ·
      refine ⟨249961361724334458175712453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166640907816222972117141635 249961361724334458175712453)
      ·
        refine ⟨46867755323312710907946085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 249961361724334458175712453 46867755323312710907946085)
        ·
          refine ⟨8787704123121133295239891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46867755323312710907946085 8787704123121133295239891)
          ·
            refine ⟨13181556184681699942859837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8787704123121133295239891 13181556184681699942859837)
            ·
              refine ⟨4943083569255637478572439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13181556184681699942859837 4943083569255637478572439)
              ·
                refine ⟨7414625353883456217858659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4943083569255637478572439 7414625353883456217858659)
                ·
                  refine ⟨11121938030825184326787989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7414625353883456217858659 11121938030825184326787989)
                  ·
                    refine ⟨521340845194930515318187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11121938030825184326787989 521340845194930515318187)
                    ·
                      rfl

theorem cell23_3045923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 3, 1, 1, 6].length) (baseStart_3045923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3045923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3045923 prefixEnd_3045923 := by exact prefixLift 3045923
  have htrace : WordTrace (prefixWord ++ tailWord_3045923) baseStart_3045923 baseEnd_3045923 := by
    simpa [prefixWord, tailWord_3045923, baseEnd_3045923] using wordTrace_append hprefix tailTrace_3045923
  have hstable : (prefixWord ++ tailWord_3045923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3045923).length < 2 ^ (prefixWord ++ tailWord_3045923).sum := by decide
  have hdescent : baseEnd_3045923 < baseStart_3045923 := by decide
  rcases family_descends (prefixWord ++ tailWord_3045923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3045930 : List Nat := [3, 1, 4, 1, 1, 2, 1, 4, 1, 1, 4]
def baseStart_3045930 : Nat := 118140960795 + 3045930 * 2 ^ 59
def prefixEnd_3045930 : Nat := 4983230072969 + 3 ^ 40 * 3045930 * 2
def baseEnd_3045930 : Nat := 1564026129949373018567029

theorem tailTrace_3045930 : CollatzResearch.WordTrace tailWord_3045930 prefixEnd_3045930 1564026129949373018567029 := by
  unfold tailWord_3045930
  simp only [CollatzResearch.WordTrace]
  refine ⟨27773548463780822068399811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74062795903415525515732829 27773548463780822068399811)
  ·
    refine ⟨41660322695671233102599717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27773548463780822068399811 41660322695671233102599717)
    ·
      refine ⟨7811310505438356206737447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41660322695671233102599717 7811310505438356206737447)
      ·
        refine ⟨11716965758157534310106171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7811310505438356206737447 11716965758157534310106171)
        ·
          refine ⟨17575448637236301465159257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11716965758157534310106171 17575448637236301465159257)
          ·
            refine ⟨13181586477927226098869443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17575448637236301465159257 13181586477927226098869443)
            ·
              refine ⟨19772379716890839148304165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13181586477927226098869443 19772379716890839148304165)
              ·
                refine ⟨3707321196917032340307031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19772379716890839148304165 3707321196917032340307031)
                ·
                  refine ⟨5560981795375548510460547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3707321196917032340307031 5560981795375548510460547)
                  ·
                    refine ⟨8341472693063322765690821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5560981795375548510460547 8341472693063322765690821)
                    ·
                      refine ⟨1564026129949373018567029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8341472693063322765690821 1564026129949373018567029)
                      ·
                        rfl

theorem cell23_3045930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 4, 1, 1, 4].length) (baseStart_3045930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3045930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3045930 prefixEnd_3045930 := by exact prefixLift 3045930
  have htrace : WordTrace (prefixWord ++ tailWord_3045930) baseStart_3045930 baseEnd_3045930 := by
    simpa [prefixWord, tailWord_3045930, baseEnd_3045930] using wordTrace_append hprefix tailTrace_3045930
  have hstable : (prefixWord ++ tailWord_3045930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3045930).length < 2 ^ (prefixWord ++ tailWord_3045930).sum := by decide
  have hdescent : baseEnd_3045930 < baseStart_3045930 := by decide
  rcases family_descends (prefixWord ++ tailWord_3045930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3045953 : List Nat := [1, 2, 5, 1, 1, 4, 9]
def baseStart_3045953 : Nat := 118140960795 + 3045953 * 2 ^ 59
def prefixEnd_3045953 : Nat := 4983230072969 + 3 ^ 40 * 3045953 * 2
def baseEnd_3045953 : Nat := 19309110370425017636783

theorem tailTrace_3045953 : CollatzResearch.WordTrace tailWord_3045953 prefixEnd_3045953 19309110370425017636783 := by
  unfold tailWord_3045953
  simp only [CollatzResearch.WordTrace]
  refine ⟨111095032734039963201686513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74063355156026642134457675 111095032734039963201686513)
  ·
    refine ⟨83321274550529972401264885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111095032734039963201686513 83321274550529972401264885)
    ·
      refine ⟨7811369489112184912618583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 83321274550529972401264885 7811369489112184912618583)
      ·
        refine ⟨11717054233668277368927875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7811369489112184912618583 11717054233668277368927875)
        ·
          refine ⟨17575581350502416053391813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11717054233668277368927875 17575581350502416053391813)
          ·
            refine ⟨3295421503219203010010965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17575581350502416053391813 3295421503219203010010965)
            ·
              refine ⟨19309110370425017636783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3295421503219203010010965 19309110370425017636783)
              ·
                rfl

theorem cell23_3045953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 4, 9].length) (baseStart_3045953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3045953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3045953 prefixEnd_3045953 := by exact prefixLift 3045953
  have htrace : WordTrace (prefixWord ++ tailWord_3045953) baseStart_3045953 baseEnd_3045953 := by
    simpa [prefixWord, tailWord_3045953, baseEnd_3045953] using wordTrace_append hprefix tailTrace_3045953
  have hstable : (prefixWord ++ tailWord_3045953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3045953).length < 2 ^ (prefixWord ++ tailWord_3045953).sum := by decide
  have hdescent : baseEnd_3045953 < baseStart_3045953 := by decide
  rcases family_descends (prefixWord ++ tailWord_3045953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3045958 : List Nat := [6, 1, 1, 1, 2, 2, 3, 2, 1, 1, 3]
def baseStart_3045958 : Nat := 118140960795 + 3045958 * 2 ^ 59
def prefixEnd_3045958 : Nat := 4983230072969 + 3 ^ 40 * 3045958 * 2
def baseEnd_3045958 : Nat := 1564040507407698909016901

theorem tailTrace_3045958 : CollatzResearch.WordTrace tailWord_3045958 prefixEnd_3045958 1564040507407698909016901 := by
  unfold tailWord_3045958
  simp only [CollatzResearch.WordTrace]
  refine ⟨3471725471844432782988079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 74063476732681232703745685 3471725471844432782988079)
  ·
    refine ⟨5207588207766649174482119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3471725471844432782988079 5207588207766649174482119)
    ·
      refine ⟨7811382311649973761723179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5207588207766649174482119 7811382311649973761723179)
      ·
        refine ⟨11717073467474960642584769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7811382311649973761723179 11717073467474960642584769)
        ·
          refine ⟨8787805100606220481938577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11717073467474960642584769 8787805100606220481938577)
          ·
            refine ⟨6590853825454665361453933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8787805100606220481938577 6590853825454665361453933)
            ·
              refine ⟨2471570184545499510545225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6590853825454665361453933 2471570184545499510545225)
              ·
                refine ⟨1853677638409124632908919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2471570184545499510545225 1853677638409124632908919)
                ·
                  refine ⟨2780516457613686949363379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1853677638409124632908919 2780516457613686949363379)
                  ·
                    refine ⟨4170774686420530424045069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2780516457613686949363379 4170774686420530424045069)
                    ·
                      refine ⟨1564040507407698909016901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4170774686420530424045069 1564040507407698909016901)
                      ·
                        rfl

theorem cell23_3045958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 3, 2, 1, 1, 3].length) (baseStart_3045958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3045958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3045958 prefixEnd_3045958 := by exact prefixLift 3045958
  have htrace : WordTrace (prefixWord ++ tailWord_3045958) baseStart_3045958 baseEnd_3045958 := by
    simpa [prefixWord, tailWord_3045958, baseEnd_3045958] using wordTrace_append hprefix tailTrace_3045958
  have hstable : (prefixWord ++ tailWord_3045958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3045958).length < 2 ^ (prefixWord ++ tailWord_3045958).sum := by decide
  have hdescent : baseEnd_3045958 < baseStart_3045958 := by decide
  rcases family_descends (prefixWord ++ tailWord_3045958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3046023 : List Nat := [1, 1, 4, 2, 1, 2, 1, 1, 1, 6, 3]
def baseStart_3046023 : Nat := 118140960795 + 3046023 * 2 ^ 59
def prefixEnd_3046023 : Nat := 4983230072969 + 3 ^ 40 * 3046023 * 2
def baseEnd_3046023 : Nat := 1564073883650241154704101

theorem tailTrace_3046023 : CollatzResearch.WordTrace tailWord_3046023 prefixEnd_3046023 1564073883650241154704101 := by
  unfold tailWord_3046023
  simp only [CollatzResearch.WordTrace]
  refine ⟨111097585843786365156734723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74065057229190910104489815 111097585843786365156734723)
  ·
    refine ⟨166646378765679547735102085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111097585843786365156734723 166646378765679547735102085)
    ·
      refine ⟨31246196018564915200331641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 166646378765679547735102085 31246196018564915200331641)
      ·
        refine ⟨23434647013923686400248731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31246196018564915200331641 23434647013923686400248731)
        ·
          refine ⟨35151970520885529600373097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23434647013923686400248731 35151970520885529600373097)
          ·
            refine ⟨26363977890664147200279823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35151970520885529600373097 26363977890664147200279823)
            ·
              refine ⟨39545966835996220800419735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26363977890664147200279823 39545966835996220800419735)
              ·
                refine ⟨59318950253994331200629603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39545966835996220800419735 59318950253994331200629603)
                ·
                  refine ⟨88978425380991496800944405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59318950253994331200629603 88978425380991496800944405)
                  ·
                    refine ⟨4170863689733976412544269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 88978425380991496800944405 4170863689733976412544269)
                    ·
                      refine ⟨1564073883650241154704101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4170863689733976412544269 1564073883650241154704101)
                      ·
                        rfl

theorem cell23_3046023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 1, 1, 6, 3].length) (baseStart_3046023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3046023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3046023 prefixEnd_3046023 := by exact prefixLift 3046023
  have htrace : WordTrace (prefixWord ++ tailWord_3046023) baseStart_3046023 baseEnd_3046023 := by
    simpa [prefixWord, tailWord_3046023, baseEnd_3046023] using wordTrace_append hprefix tailTrace_3046023
  have hstable : (prefixWord ++ tailWord_3046023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3046023).length < 2 ^ (prefixWord ++ tailWord_3046023).sum := by decide
  have hdescent : baseEnd_3046023 < baseStart_3046023 := by decide
  rcases family_descends (prefixWord ++ tailWord_3046023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3046053 : List Nat := [1, 3, 1, 2, 1, 2, 1, 1, 3, 5, 3]
def baseStart_3046053 : Nat := 118140960795 + 3046053 * 2 ^ 59
def prefixEnd_3046053 : Nat := 4983230072969 + 3 ^ 40 * 3046053 * 2
def baseEnd_3046053 : Nat := 1564089288069876037328963

theorem tailTrace_3046053 : CollatzResearch.WordTrace tailWord_3046053 prefixEnd_3046053 1564089288069876037328963 := by
  unfold tailWord_3046053
  simp only [CollatzResearch.WordTrace]
  refine ⟨111098680033677680280326813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74065786689118453520217875 111098680033677680280326813)
  ·
    refine ⟨41662005012629130105122555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111098680033677680280326813 41662005012629130105122555)
    ·
      refine ⟨62493007518943695157683833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41662005012629130105122555 62493007518943695157683833)
      ·
        refine ⟨46869755639207771368262875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62493007518943695157683833 46869755639207771368262875)
        ·
          refine ⟨70304633458811657052394313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46869755639207771368262875 70304633458811657052394313)
          ·
            refine ⟨52728475094108742789295735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70304633458811657052394313 52728475094108742789295735)
            ·
              refine ⟨79092712641163114183943603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52728475094108742789295735 79092712641163114183943603)
              ·
                refine ⟨118639068961744671275915405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79092712641163114183943603 118639068961744671275915405)
                ·
                  refine ⟨44489650860654251728468277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 118639068961744671275915405 44489650860654251728468277)
                  ·
                    refine ⟨4170904768186336099543901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 44489650860654251728468277 4170904768186336099543901)
                    ·
                      refine ⟨1564089288069876037328963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4170904768186336099543901 1564089288069876037328963)
                      ·
                        rfl

theorem cell23_3046053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 1, 3, 5, 3].length) (baseStart_3046053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3046053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3046053 prefixEnd_3046053 := by exact prefixLift 3046053
  have htrace : WordTrace (prefixWord ++ tailWord_3046053) baseStart_3046053 baseEnd_3046053 := by
    simpa [prefixWord, tailWord_3046053, baseEnd_3046053] using wordTrace_append hprefix tailTrace_3046053
  have hstable : (prefixWord ++ tailWord_3046053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3046053).length < 2 ^ (prefixWord ++ tailWord_3046053).sum := by decide
  have hdescent : baseEnd_3046053 < baseStart_3046053 := by decide
  rcases family_descends (prefixWord ++ tailWord_3046053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3046071 : List Nat := [1, 1, 3, 1, 6, 2, 1, 2, 2, 2, 2]
def baseStart_3046071 : Nat := 118140960795 + 3046071 * 2 ^ 59
def prefixEnd_3046071 : Nat := 4983230072969 + 3 ^ 40 * 3046071 * 2
def baseEnd_3046071 : Nat := 1564098530721656966903881

theorem tailTrace_3046071 : CollatzResearch.WordTrace tailWord_3046071 prefixEnd_3046071 1564098530721656966903881 := by
  unfold tailWord_3046071
  simp only [CollatzResearch.WordTrace]
  refine ⟨111099336547612469354482067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74066224365074979569654711 111099336547612469354482067)
  ·
    refine ⟨166649004821418704031723101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111099336547612469354482067 166649004821418704031723101)
    ·
      refine ⟨62493376808032014011896163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 166649004821418704031723101 62493376808032014011896163)
      ·
        refine ⟨93740065212048021017844245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62493376808032014011896163 93740065212048021017844245)
        ·
          refine ⟨4394065556814750985211449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 93740065212048021017844245 4394065556814750985211449)
          ·
            refine ⟨3295549167611063238908587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4394065556814750985211449 3295549167611063238908587)
            ·
              refine ⟨4943323751416594858362881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3295549167611063238908587 4943323751416594858362881)
              ·
                refine ⟨3707492813562446143772161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4943323751416594858362881 3707492813562446143772161)
                ·
                  refine ⟨2780619610171834607829121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3707492813562446143772161 2780619610171834607829121)
                  ·
                    refine ⟨2085464707628875955871841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2780619610171834607829121 2085464707628875955871841)
                    ·
                      refine ⟨1564098530721656966903881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2085464707628875955871841 1564098530721656966903881)
                      ·
                        rfl

theorem cell23_3046071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 2, 1, 2, 2, 2, 2].length) (baseStart_3046071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3046071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3046071 prefixEnd_3046071 := by exact prefixLift 3046071
  have htrace : WordTrace (prefixWord ++ tailWord_3046071) baseStart_3046071 baseEnd_3046071 := by
    simpa [prefixWord, tailWord_3046071, baseEnd_3046071] using wordTrace_append hprefix tailTrace_3046071
  have hstable : (prefixWord ++ tailWord_3046071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3046071).length < 2 ^ (prefixWord ++ tailWord_3046071).sum := by decide
  have hdescent : baseEnd_3046071 < baseStart_3046071 := by decide
  rcases family_descends (prefixWord ++ tailWord_3046071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3046073 : List Nat := [1, 2, 1, 4, 1, 1, 1, 3, 4, 5]
def baseStart_3046073 : Nat := 118140960795 + 3046073 * 2 ^ 59
def prefixEnd_3046073 : Nat := 4983230072969 + 3 ^ 40 * 3046073 * 2
def baseEnd_3046073 : Nat := 521366519227655319692957

theorem tailTrace_3046073 : CollatzResearch.WordTrace tailWord_3046073 prefixEnd_3046073 521366519227655319692957 := by
  unfold tailWord_3046073
  simp only [CollatzResearch.WordTrace]
  refine ⟨111099409493605223696054873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74066272995736815797369915 111099409493605223696054873)
  ·
    refine ⟨83324557120203917772041155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111099409493605223696054873 83324557120203917772041155)
    ·
      refine ⟨124986835680305876658061733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83324557120203917772041155 124986835680305876658061733)
      ·
        refine ⟨23435031690057351873386575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 124986835680305876658061733 23435031690057351873386575)
        ·
          refine ⟨35152547535086027810079863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23435031690057351873386575 35152547535086027810079863)
          ·
            refine ⟨52728821302629041715119795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35152547535086027810079863 52728821302629041715119795)
            ·
              refine ⟨79093231953943562572679693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52728821302629041715119795 79093231953943562572679693)
              ·
                refine ⟨29659961982728835964754885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 79093231953943562572679693 29659961982728835964754885)
                ·
                  refine ⟨5561242871761656743391541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29659961982728835964754885 5561242871761656743391541)
                  ·
                    refine ⟨521366519227655319692957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5561242871761656743391541 521366519227655319692957)
                    ·
                      rfl

theorem cell23_3046073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 3, 4, 5].length) (baseStart_3046073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3046073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3046073 prefixEnd_3046073 := by exact prefixLift 3046073
  have htrace : WordTrace (prefixWord ++ tailWord_3046073) baseStart_3046073 baseEnd_3046073 := by
    simpa [prefixWord, tailWord_3046073, baseEnd_3046073] using wordTrace_append hprefix tailTrace_3046073
  have hstable : (prefixWord ++ tailWord_3046073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3046073).length < 2 ^ (prefixWord ++ tailWord_3046073).sum := by decide
  have hdescent : baseEnd_3046073 < baseStart_3046073 := by decide
  rcases family_descends (prefixWord ++ tailWord_3046073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3046137 : List Nat := [1, 2, 1, 3, 1, 1, 1, 8, 1, 4]
def baseStart_3046137 : Nat := 118140960795 + 3046137 * 2 ^ 59
def prefixEnd_3046137 : Nat := 4983230072969 + 3 ^ 40 * 3046137 * 2
def baseEnd_3046137 : Nat := 521377473481617902892859

theorem tailTrace_3046137 : CollatzResearch.WordTrace tailWord_3046137 prefixEnd_3046137 521377473481617902892859 := by
  unfold tailWord_3046137
  simp only [CollatzResearch.WordTrace]
  refine ⟨111101743765373362626384665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74067829176915575084256443 111101743765373362626384665)
  ·
    refine ⟨83326307824030021969788499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111101743765373362626384665 83326307824030021969788499)
    ·
      refine ⟨124989461736045032954682749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83326307824030021969788499 124989461736045032954682749)
      ·
        refine ⟨46871048151016887358006031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 124989461736045032954682749 46871048151016887358006031)
        ·
          refine ⟨70306572226525331037009047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46871048151016887358006031 70306572226525331037009047)
          ·
            refine ⟨105459858339787996555513571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70306572226525331037009047 105459858339787996555513571)
            ·
              refine ⟨158189787509681994833270357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105459858339787996555513571 158189787509681994833270357)
              ·
                refine ⟨1853786572379085876952387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 158189787509681994833270357 1853786572379085876952387)
                ·
                  refine ⟨2780679858568628815428581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1853786572379085876952387 2780679858568628815428581)
                  ·
                    refine ⟨521377473481617902892859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2780679858568628815428581 521377473481617902892859)
                    ·
                      rfl

theorem cell23_3046137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 8, 1, 4].length) (baseStart_3046137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3046137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3046137 prefixEnd_3046137 := by exact prefixLift 3046137
  have htrace : WordTrace (prefixWord ++ tailWord_3046137) baseStart_3046137 baseEnd_3046137 := by
    simpa [prefixWord, tailWord_3046137, baseEnd_3046137] using wordTrace_append hprefix tailTrace_3046137
  have hstable : (prefixWord ++ tailWord_3046137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3046137).length < 2 ^ (prefixWord ++ tailWord_3046137).sum := by decide
  have hdescent : baseEnd_3046137 < baseStart_3046137 := by decide
  rcases family_descends (prefixWord ++ tailWord_3046137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3046153 : List Nat := [1, 2, 1, 1, 3, 2, 2, 2, 1, 2, 6]
def baseStart_3046153 : Nat := 118140960795 + 3046153 * 2 ^ 59
def prefixEnd_3046153 : Nat := 4983230072969 + 3 ^ 40 * 3046153 * 2
def baseEnd_3046153 : Nat := 1564140636135325646078503

theorem tailTrace_3046153 : CollatzResearch.WordTrace tailWord_3046153 prefixEnd_3046153 1564140636135325646078503 := by
  unfold tailWord_3046153
  simp only [CollatzResearch.WordTrace]
  refine ⟨111102327333315397358967113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74068218222210264905978075 111102327333315397358967113)
  ·
    refine ⟨83326745499986548019225335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111102327333315397358967113 83326745499986548019225335)
    ·
      refine ⟨124990118249979822028838003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83326745499986548019225335 124990118249979822028838003)
      ·
        refine ⟨187485177374969733043257005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124990118249979822028838003 187485177374969733043257005)
        ·
          refine ⟨70306941515613649891221377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 187485177374969733043257005 70306941515613649891221377)
          ·
            refine ⟨52730206136710237418416033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70306941515613649891221377 52730206136710237418416033)
            ·
              refine ⟨39547654602532678063812025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52730206136710237418416033 39547654602532678063812025)
              ·
                refine ⟨29660740951899508547859019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39547654602532678063812025 29660740951899508547859019)
                ·
                  refine ⟨44491111427849262821788529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29660740951899508547859019 44491111427849262821788529)
                  ·
                    refine ⟨33368333570886947116341397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 44491111427849262821788529 33368333570886947116341397)
                    ·
                      refine ⟨1564140636135325646078503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 33368333570886947116341397 1564140636135325646078503)
                      ·
                        rfl

theorem cell23_3046153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 2, 1, 2, 6].length) (baseStart_3046153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3046153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3046153 prefixEnd_3046153 := by exact prefixLift 3046153
  have htrace : WordTrace (prefixWord ++ tailWord_3046153) baseStart_3046153 baseEnd_3046153 := by
    simpa [prefixWord, tailWord_3046153, baseEnd_3046153] using wordTrace_append hprefix tailTrace_3046153
  have hstable : (prefixWord ++ tailWord_3046153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3046153).length < 2 ^ (prefixWord ++ tailWord_3046153).sum := by decide
  have hdescent : baseEnd_3046153 < baseStart_3046153 := by decide
  rcases family_descends (prefixWord ++ tailWord_3046153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3046200 : List Nat := [2, 1, 2, 1, 3, 2, 1, 1, 5, 1, 4]
def baseStart_3046200 : Nat := 118140960795 + 3046200 * 2 ^ 59
def prefixEnd_3046200 : Nat := 4983230072969 + 3 ^ 40 * 3046200 * 2
def baseEnd_3046200 : Nat := 1564164769726086962190787

theorem tailTrace_3046200 : CollatzResearch.WordTrace tailWord_3046200 prefixEnd_3046200 1564164769726086962190787 := by
  unfold tailWord_3046200
  simp only [CollatzResearch.WordTrace]
  refine ⟨55552020782072562192964027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74069361042763416257285369 55552020782072562192964027)
  ·
    refine ⟨83328031173108843289446041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55552020782072562192964027 83328031173108843289446041)
    ·
      refine ⟨62496023379831632467084531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83328031173108843289446041 62496023379831632467084531)
      ·
        refine ⟨93744035069747448700626797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62496023379831632467084531 93744035069747448700626797)
        ·
          refine ⟨35154013151155293262735049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 93744035069747448700626797 35154013151155293262735049)
          ·
            refine ⟨26365509863366469947051287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35154013151155293262735049 26365509863366469947051287)
            ·
              refine ⟨39548264795049704920576931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26365509863366469947051287 39548264795049704920576931)
              ·
                refine ⟨59322397192574557380865397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39548264795049704920576931 59322397192574557380865397)
                ·
                  refine ⟨5561474736803864754456131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 59322397192574557380865397 5561474736803864754456131)
                  ·
                    refine ⟨8342212105205797131684197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5561474736803864754456131 8342212105205797131684197)
                    ·
                      refine ⟨1564164769726086962190787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8342212105205797131684197 1564164769726086962190787)
                      ·
                        rfl

theorem cell23_3046200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 1, 5, 1, 4].length) (baseStart_3046200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3046200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3046200 prefixEnd_3046200 := by exact prefixLift 3046200
  have htrace : WordTrace (prefixWord ++ tailWord_3046200) baseStart_3046200 baseEnd_3046200 := by
    simpa [prefixWord, tailWord_3046200, baseEnd_3046200] using wordTrace_append hprefix tailTrace_3046200
  have hstable : (prefixWord ++ tailWord_3046200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3046200).length < 2 ^ (prefixWord ++ tailWord_3046200).sum := by decide
  have hdescent : baseEnd_3046200 < baseStart_3046200 := by decide
  rcases family_descends (prefixWord ++ tailWord_3046200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3046221 : List Nat := [1, 6, 1, 2, 2, 1, 1, 1, 1, 5, 2]
def baseStart_3046221 : Nat := 118140960795 + 3046221 * 2 ^ 59
def prefixEnd_3046221 : Nat := 4983230072969 + 3 ^ 40 * 3046221 * 2
def baseEnd_3046221 : Nat := 1564175552819831380028191

theorem tailTrace_3046221 : CollatzResearch.WordTrace tailWord_3046221 prefixEnd_3046221 1564175552819831380028191 := by
  unfold tailWord_3046221
  simp only [CollatzResearch.WordTrace]
  refine ⟨111104807497069044972442517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74069871664712696648295011 111104807497069044972442517)
  ·
    refine ⟨5208037851425111483083243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 111104807497069044972442517 5208037851425111483083243)
    ·
      refine ⟨7812056777137667224624865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5208037851425111483083243 7812056777137667224624865)
      ·
        refine ⟨5859042582853250418468649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7812056777137667224624865 5859042582853250418468649)
        ·
          refine ⟨4394281937139937813851487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5859042582853250418468649 4394281937139937813851487)
          ·
            refine ⟨6591422905709906720777231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4394281937139937813851487 6591422905709906720777231)
            ·
              refine ⟨9887134358564860081165847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6591422905709906720777231 9887134358564860081165847)
              ·
                refine ⟨14830701537847290121748771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9887134358564860081165847 14830701537847290121748771)
                ·
                  refine ⟨22246052306770935182623157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14830701537847290121748771 22246052306770935182623157)
                  ·
                    refine ⟨2085567403759775173370921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 22246052306770935182623157 2085567403759775173370921)
                    ·
                      refine ⟨1564175552819831380028191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2085567403759775173370921 1564175552819831380028191)
                      ·
                        rfl

theorem cell23_3046221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 1, 1, 1, 5, 2].length) (baseStart_3046221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3046221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3046221 prefixEnd_3046221 := by exact prefixLift 3046221
  have htrace : WordTrace (prefixWord ++ tailWord_3046221) baseStart_3046221 baseEnd_3046221 := by
    simpa [prefixWord, tailWord_3046221, baseEnd_3046221] using wordTrace_append hprefix tailTrace_3046221
  have hstable : (prefixWord ++ tailWord_3046221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3046221).length < 2 ^ (prefixWord ++ tailWord_3046221).sum := by decide
  have hdescent : baseEnd_3046221 < baseStart_3046221 := by decide
  rcases family_descends (prefixWord ++ tailWord_3046221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3046228 : List Nat := [2, 4, 1, 1, 4, 1, 2, 3, 1, 1, 3]
def baseStart_3046228 : Nat := 118140960795 + 3046228 * 2 ^ 59
def prefixEnd_3046228 : Nat := 4983230072969 + 3 ^ 40 * 3046228 * 2
def baseEnd_3046228 : Nat := 1564179147184412852640659

theorem tailTrace_3046228 : CollatzResearch.WordTrace tailWord_3046228 prefixEnd_3046228 1564179147184412852640659 := by
  unfold tailWord_3046228
  simp only [CollatzResearch.WordTrace]
  refine ⟨55552531404021842583973669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74070041872029123445298225 55552531404021842583973669)
  ·
    refine ⟨10416099638254095484495063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55552531404021842583973669 10416099638254095484495063)
    ·
      refine ⟨15624149457381143226742595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10416099638254095484495063 15624149457381143226742595)
      ·
        refine ⟨23436224186071714840113893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15624149457381143226742595 23436224186071714840113893)
        ·
          refine ⟨4394292034888446532521355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23436224186071714840113893 4394292034888446532521355)
          ·
            refine ⟨6591438052332669798782033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4394292034888446532521355 6591438052332669798782033)
            ·
              refine ⟨4943578539249502349086525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6591438052332669798782033 4943578539249502349086525)
              ·
                refine ⟨1853841952218563380907447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4943578539249502349086525 1853841952218563380907447)
                ·
                  refine ⟨2780762928327845071361171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1853841952218563380907447 2780762928327845071361171)
                  ·
                    refine ⟨4171144392491767607041757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2780762928327845071361171 4171144392491767607041757)
                    ·
                      refine ⟨1564179147184412852640659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4171144392491767607041757 1564179147184412852640659)
                      ·
                        rfl

theorem cell23_3046228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 2, 3, 1, 1, 3].length) (baseStart_3046228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3046228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3046228 prefixEnd_3046228 := by exact prefixLift 3046228
  have htrace : WordTrace (prefixWord ++ tailWord_3046228) baseStart_3046228 baseEnd_3046228 := by
    simpa [prefixWord, tailWord_3046228, baseEnd_3046228] using wordTrace_append hprefix tailTrace_3046228
  have hstable : (prefixWord ++ tailWord_3046228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3046228).length < 2 ^ (prefixWord ++ tailWord_3046228).sum := by decide
  have hdescent : baseEnd_3046228 < baseStart_3046228 := by decide
  rcases family_descends (prefixWord ++ tailWord_3046228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3046234 : List Nat := [3, 1, 1, 2, 1, 4, 4, 1, 1, 1, 4]
def baseStart_3046234 : Nat := 118140960795 + 3046234 * 2 ^ 59
def prefixEnd_3046234 : Nat := 4983230072969 + 3 ^ 40 * 3046234 * 2
def baseEnd_3046234 : Nat := 1564182228068339829165631

theorem tailTrace_3046234 : CollatzResearch.WordTrace tailWord_3046234 prefixEnd_3046234 1564182228068339829165631 := by
  unfold tailWord_3046234
  simp only [CollatzResearch.WordTrace]
  refine ⟨27776320411505487048166439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74070187764014632128443837 27776320411505487048166439)
  ·
    refine ⟨41664480617258230572249659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27776320411505487048166439 41664480617258230572249659)
    ·
      refine ⟨62496720925887345858374489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41664480617258230572249659 62496720925887345858374489)
      ·
        refine ⟨46872540694415509393780867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62496720925887345858374489 46872540694415509393780867)
        ·
          refine ⟨70308811041623264090671301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46872540694415509393780867 70308811041623264090671301)
          ·
            refine ⟨13182902070304362017000869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 70308811041623264090671301 13182902070304362017000869)
            ·
              refine ⟨2471794138182067878187663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13182902070304362017000869 2471794138182067878187663)
              ·
                refine ⟨3707691207273101817281495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2471794138182067878187663 3707691207273101817281495)
                ·
                  refine ⟨5561536810909652725922243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3707691207273101817281495 5561536810909652725922243)
                  ·
                    refine ⟨8342305216364479088883365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5561536810909652725922243 8342305216364479088883365)
                    ·
                      refine ⟨1564182228068339829165631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8342305216364479088883365 1564182228068339829165631)
                      ·
                        rfl

theorem cell23_3046234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 4, 1, 1, 1, 4].length) (baseStart_3046234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3046234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3046234 prefixEnd_3046234 := by exact prefixLift 3046234
  have htrace : WordTrace (prefixWord ++ tailWord_3046234) baseStart_3046234 baseEnd_3046234 := by
    simpa [prefixWord, tailWord_3046234, baseEnd_3046234] using wordTrace_append hprefix tailTrace_3046234
  have hstable : (prefixWord ++ tailWord_3046234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3046234).length < 2 ^ (prefixWord ++ tailWord_3046234).sum := by decide
  have hdescent : baseEnd_3046234 < baseStart_3046234 := by decide
  rcases family_descends (prefixWord ++ tailWord_3046234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3046244 : List Nat := [2, 3, 1, 1, 4, 1, 3, 2, 2, 4]
def baseStart_3046244 : Nat := 118140960795 + 3046244 * 2 ^ 59
def prefixEnd_3046244 : Nat := 4983230072969 + 3 ^ 40 * 3046244 * 2
def baseEnd_3046244 : Nat := 521395787624961596680195

theorem tailTrace_3046244 : CollatzResearch.WordTrace tailWord_3046244 prefixEnd_3046244 521395787624961596680195 := by
  unfold tailWord_3046244
  simp only [CollatzResearch.WordTrace]
  refine ⟨55552823187992859950264893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74070430917323813267019857 55552823187992859950264893)
  ·
    refine ⟨20832308695497322481349335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55552823187992859950264893 20832308695497322481349335)
    ·
      refine ⟨31248463043245983722024003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20832308695497322481349335 31248463043245983722024003)
      ·
        refine ⟨46872694564868975583036005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31248463043245983722024003 46872694564868975583036005)
        ·
          refine ⟨8788630230912932921819251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46872694564868975583036005 8788630230912932921819251)
          ·
            refine ⟨13182945346369399382728877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8788630230912932921819251 13182945346369399382728877)
            ·
              refine ⟨4943604504888524768523329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13182945346369399382728877 4943604504888524768523329)
              ·
                refine ⟨3707703378666393576392497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4943604504888524768523329 3707703378666393576392497)
                ·
                  refine ⟨2780777533999795182294373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3707703378666393576392497 2780777533999795182294373)
                  ·
                    refine ⟨521395787624961596680195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2780777533999795182294373 521395787624961596680195)
                    ·
                      rfl

theorem cell23_3046244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 3, 2, 2, 4].length) (baseStart_3046244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3046244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3046244 prefixEnd_3046244 := by exact prefixLift 3046244
  have htrace : WordTrace (prefixWord ++ tailWord_3046244) baseStart_3046244 baseEnd_3046244 := by
    simpa [prefixWord, tailWord_3046244, baseEnd_3046244] using wordTrace_append hprefix tailTrace_3046244
  have hstable : (prefixWord ++ tailWord_3046244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3046244).length < 2 ^ (prefixWord ++ tailWord_3046244).sum := by decide
  have hdescent : baseEnd_3046244 < baseStart_3046244 := by decide
  rcases family_descends (prefixWord ++ tailWord_3046244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3046251 : List Nat := [1, 1, 1, 1, 2, 2, 6, 4, 1, 2, 2]
def baseStart_3046251 : Nat := 118140960795 + 3046251 * 2 ^ 59
def prefixEnd_3046251 : Nat := 4983230072969 + 3 ^ 40 * 3046251 * 2
def baseEnd_3046251 : Nat := 1564190957239466262653053

theorem tailTrace_3046251 : CollatzResearch.WordTrace tailWord_3046251 prefixEnd_3046251 1564190957239466262653053 := by
  unfold tailWord_3046251
  simp only [CollatzResearch.WordTrace]
  refine ⟨111105901686960360096034607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74070601124640240064023071 111105901686960360096034607)
  ·
    refine ⟨166658852530440540144051911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111105901686960360096034607 166658852530440540144051911)
    ·
      refine ⟨249988278795660810216077867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166658852530440540144051911 249988278795660810216077867)
      ·
        refine ⟨374982418193491215324116801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 249988278795660810216077867 374982418193491215324116801)
        ·
          refine ⟨281236813645118411493087601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 374982418193491215324116801 281236813645118411493087601)
          ·
            refine ⟨210927610233838808619815701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 281236813645118411493087601 210927610233838808619815701)
            ·
              refine ⟨9887231729711194154053861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 210927610233838808619815701 9887231729711194154053861)
              ·
                refine ⟨1853855949320848903885099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9887231729711194154053861 1853855949320848903885099)
                ·
                  refine ⟨2780783923981273355827649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1853855949320848903885099 2780783923981273355827649)
                  ·
                    refine ⟨2085587942985955016870737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2780783923981273355827649 2085587942985955016870737)
                    ·
                      refine ⟨1564190957239466262653053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2085587942985955016870737 1564190957239466262653053)
                      ·
                        rfl

theorem cell23_3046251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 6, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 6, 4, 1, 2, 2].length) (baseStart_3046251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3046251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3046251 prefixEnd_3046251 := by exact prefixLift 3046251
  have htrace : WordTrace (prefixWord ++ tailWord_3046251) baseStart_3046251 baseEnd_3046251 := by
    simpa [prefixWord, tailWord_3046251, baseEnd_3046251] using wordTrace_append hprefix tailTrace_3046251
  have hstable : (prefixWord ++ tailWord_3046251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3046251).length < 2 ^ (prefixWord ++ tailWord_3046251).sum := by decide
  have hdescent : baseEnd_3046251 < baseStart_3046251 := by decide
  rcases family_descends (prefixWord ++ tailWord_3046251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3046254 : List Nat := [4, 1, 2, 3, 2, 1, 1, 2, 1, 1, 5]
def baseStart_3046254 : Nat := 118140960795 + 3046254 * 2 ^ 59
def prefixEnd_3046254 : Nat := 4983230072969 + 3 ^ 40 * 3046254 * 2
def baseEnd_3046254 : Nat := 1564192497681429750915539

theorem tailTrace_3046254 : CollatzResearch.WordTrace tailWord_3046254 prefixEnd_3046254 1564192497681429750915539 := by
  unfold tailWord_3046254
  simp only [CollatzResearch.WordTrace]
  refine ⟨13888251388243686451049227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74070674070632994405595877 13888251388243686451049227)
  ·
    refine ⟨20832377082365529676573841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13888251388243686451049227 20832377082365529676573841)
    ·
      refine ⟨15624282811774147257430381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20832377082365529676573841 15624282811774147257430381)
      ·
        refine ⟨5859106054415305221536393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15624282811774147257430381 5859106054415305221536393)
        ·
          refine ⟨4394329540811478916152295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5859106054415305221536393 4394329540811478916152295)
          ·
            refine ⟨6591494311217218374228443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4394329540811478916152295 6591494311217218374228443)
            ·
              refine ⟨9887241466825827561342665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6591494311217218374228443 9887241466825827561342665)
              ·
                refine ⟨7415431100119370671006999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9887241466825827561342665 7415431100119370671006999)
                ·
                  refine ⟨11123146650179056006510499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7415431100119370671006999 11123146650179056006510499)
                  ·
                    refine ⟨16684719975268584009765749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11123146650179056006510499 16684719975268584009765749)
                    ·
                      refine ⟨1564192497681429750915539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16684719975268584009765749 1564192497681429750915539)
                      ·
                        rfl

theorem cell23_3046254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 1, 2, 1, 1, 5].length) (baseStart_3046254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3046254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3046254 prefixEnd_3046254 := by exact prefixLift 3046254
  have htrace : WordTrace (prefixWord ++ tailWord_3046254) baseStart_3046254 baseEnd_3046254 := by
    simpa [prefixWord, tailWord_3046254, baseEnd_3046254] using wordTrace_append hprefix tailTrace_3046254
  have hstable : (prefixWord ++ tailWord_3046254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3046254).length < 2 ^ (prefixWord ++ tailWord_3046254).sum := by decide
  have hdescent : baseEnd_3046254 < baseStart_3046254 := by decide
  rcases family_descends (prefixWord ++ tailWord_3046254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3046261 : List Nat := [1, 3, 4, 1, 1, 3, 3, 1, 2, 4]
def baseStart_3046261 : Nat := 118140960795 + 3046261 * 2 ^ 59
def prefixEnd_3046261 : Nat := 4983230072969 + 3 ^ 40 * 3046261 * 2
def baseEnd_3046261 : Nat := 521398697348670407842669

theorem tailTrace_3046261 : CollatzResearch.WordTrace tailWord_3046261 prefixEnd_3046261 521398697348670407842669 := by
  unfold tailWord_3046261
  simp only [CollatzResearch.WordTrace]
  refine ⟨111106266416924131803898637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74070844277949421202599091 111106266416924131803898637)
  ·
    refine ⟨41664849906346549426461989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111106266416924131803898637 41664849906346549426461989)
    ·
      refine ⟨7812159357439978017461623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41664849906346549426461989 7812159357439978017461623)
      ·
        refine ⟨11718239036159967026192435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7812159357439978017461623 11718239036159967026192435)
        ·
          refine ⟨17577358554239950539288653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11718239036159967026192435 17577358554239950539288653)
          ·
            refine ⟨6591509457839981452233245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17577358554239950539288653 6591509457839981452233245)
            ·
              refine ⟨2471816046689993044587467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6591509457839981452233245 2471816046689993044587467)
              ·
                refine ⟨3707724070034989566881201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2471816046689993044587467 3707724070034989566881201)
                ·
                  refine ⟨2780793052526242175160901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3707724070034989566881201 2780793052526242175160901)
                  ·
                    refine ⟨521398697348670407842669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2780793052526242175160901 521398697348670407842669)
                    ·
                      rfl

theorem cell23_3046261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 3, 1, 2, 4].length) (baseStart_3046261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3046261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3046261 prefixEnd_3046261 := by exact prefixLift 3046261
  have htrace : WordTrace (prefixWord ++ tailWord_3046261) baseStart_3046261 baseEnd_3046261 := by
    simpa [prefixWord, tailWord_3046261, baseEnd_3046261] using wordTrace_append hprefix tailTrace_3046261
  have hstable : (prefixWord ++ tailWord_3046261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3046261).length < 2 ^ (prefixWord ++ tailWord_3046261).sum := by decide
  have hdescent : baseEnd_3046261 < baseStart_3046261 := by decide
  rcases family_descends (prefixWord ++ tailWord_3046261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3046267 : List Nat := [1, 1, 1, 1, 1, 5, 5, 1, 1, 3, 3]
def baseStart_3046267 : Nat := 118140960795 + 3046267 * 2 ^ 59
def prefixEnd_3046267 : Nat := 4983230072969 + 3 ^ 40 * 3046267 * 2
def baseEnd_3046267 : Nat := 1564199172929938200052979

theorem tailTrace_3046267 : CollatzResearch.WordTrace tailWord_3046267 prefixEnd_3046267 1564199172929938200052979 := by
  unfold tailWord_3046267
  simp only [CollatzResearch.WordTrace]
  refine ⟨111106485254902394828617055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74070990169934929885744703 111106485254902394828617055)
  ·
    refine ⟨166659727882353592242925583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111106485254902394828617055 166659727882353592242925583)
    ·
      refine ⟨249989591823530388364388375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166659727882353592242925583 249989591823530388364388375)
      ·
        refine ⟨374984387735295582546582563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 249989591823530388364388375 374984387735295582546582563)
        ·
          refine ⟨562476581602943373819873845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 374984387735295582546582563 562476581602943373819873845)
          ·
            refine ⟨52732179525275941295613173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 562476581602943373819873845 52732179525275941295613173)
            ·
              refine ⟨4943641830494619496463735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 52732179525275941295613173 4943641830494619496463735)
              ·
                refine ⟨7415462745741929244695603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4943641830494619496463735 7415462745741929244695603)
                ·
                  refine ⟨11123194118612893867043405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7415462745741929244695603 11123194118612893867043405)
                  ·
                    refine ⟨4171197794479835200141277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11123194118612893867043405 4171197794479835200141277)
                    ·
                      refine ⟨1564199172929938200052979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4171197794479835200141277 1564199172929938200052979)
                      ·
                        rfl

theorem cell23_3046267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 5, 1, 1, 3, 3].length) (baseStart_3046267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3046267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3046267 prefixEnd_3046267 := by exact prefixLift 3046267
  have htrace : WordTrace (prefixWord ++ tailWord_3046267) baseStart_3046267 baseEnd_3046267 := by
    simpa [prefixWord, tailWord_3046267, baseEnd_3046267] using wordTrace_append hprefix tailTrace_3046267
  have hstable : (prefixWord ++ tailWord_3046267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3046267).length < 2 ^ (prefixWord ++ tailWord_3046267).sum := by decide
  have hdescent : baseEnd_3046267 < baseStart_3046267 := by decide
  rcases family_descends (prefixWord ++ tailWord_3046267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3046330 : List Nat := [3, 1, 1, 1, 2, 1, 4, 1, 9]
def baseStart_3046330 : Nat := 118140960795 + 3046330 * 2 ^ 59
def prefixEnd_3046330 : Nat := 4983230072969 + 3 ^ 40 * 3046330 * 2
def baseEnd_3046330 : Nat := 173803502467907939285021

theorem tailTrace_3046330 : CollatzResearch.WordTrace tailWord_3046330 prefixEnd_3046330 173803502467907939285021 := by
  unfold tailWord_3046330
  simp only [CollatzResearch.WordTrace]
  refine ⟨27777195763418539147040111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74072522035782771058773629 27777195763418539147040111)
  ·
    refine ⟨41665793645127808720560167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27777195763418539147040111 41665793645127808720560167)
    ·
      refine ⟨62498690467691713080840251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41665793645127808720560167 62498690467691713080840251)
      ·
        refine ⟨93748035701537569621260377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62498690467691713080840251 93748035701537569621260377)
        ·
          refine ⟨70311026776153177215945283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93748035701537569621260377 70311026776153177215945283)
          ·
            refine ⟨105466540164229765823917925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70311026776153177215945283 105466540164229765823917925)
            ·
              refine ⟨19774976280793081091984611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 105466540164229765823917925 19774976280793081091984611)
              ·
                refine ⟨29662464421189621637976917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19774976280793081091984611 29662464421189621637976917)
                ·
                  refine ⟨173803502467907939285021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 29662464421189621637976917 173803502467907939285021)
                  ·
                    rfl

theorem cell23_3046330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 1, 9].length) (baseStart_3046330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3046330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3046330 prefixEnd_3046330 := by exact prefixLift 3046330
  have htrace : WordTrace (prefixWord ++ tailWord_3046330) baseStart_3046330 baseEnd_3046330 := by
    simpa [prefixWord, tailWord_3046330, baseEnd_3046330] using wordTrace_append hprefix tailTrace_3046330
  have hstable : (prefixWord ++ tailWord_3046330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3046330).length < 2 ^ (prefixWord ++ tailWord_3046330).sum := by decide
  have hdescent : baseEnd_3046330 < baseStart_3046330 := by decide
  rcases family_descends (prefixWord ++ tailWord_3046330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3046398 : List Nat := [4, 2, 2, 2, 2, 1, 2, 3, 5]
def baseStart_3046398 : Nat := 118140960795 + 3046398 * 2 ^ 59
def prefixEnd_3046398 : Nat := 4983230072969 + 3 ^ 40 * 3046398 * 2
def baseEnd_3046398 : Nat := 173807382099519687501653

theorem tailTrace_3046398 : CollatzResearch.WordTrace tailWord_3046398 prefixEnd_3046398 173807382099519687501653 := by
  unfold tailWord_3046398
  simp only [CollatzResearch.WordTrace]
  refine ⟨13888907902178475525204481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74074175478285202801090565 13888907902178475525204481)
  ·
    refine ⟨10416680926633856643903361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13888907902178475525204481 10416680926633856643903361)
    ·
      refine ⟨7812510694975392482927521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10416680926633856643903361 7812510694975392482927521)
      ·
        refine ⟨5859383021231544362195641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7812510694975392482927521 5859383021231544362195641)
        ·
          refine ⟨4394537265923658271646731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5859383021231544362195641 4394537265923658271646731)
          ·
            refine ⟨6591805898885487407470097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4394537265923658271646731 6591805898885487407470097)
            ·
              refine ⟨4943854424164115555602573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6591805898885487407470097 4943854424164115555602573)
              ·
                refine ⟨1853945409061543333350965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4943854424164115555602573 1853945409061543333350965)
                ·
                  refine ⟨173807382099519687501653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1853945409061543333350965 173807382099519687501653)
                  ·
                    rfl

theorem cell23_3046398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 2, 3, 5].length) (baseStart_3046398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3046398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3046398 prefixEnd_3046398 := by exact prefixLift 3046398
  have htrace : WordTrace (prefixWord ++ tailWord_3046398) baseStart_3046398 baseEnd_3046398 := by
    simpa [prefixWord, tailWord_3046398, baseEnd_3046398] using wordTrace_append hprefix tailTrace_3046398
  have hstable : (prefixWord ++ tailWord_3046398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3046398).length < 2 ^ (prefixWord ++ tailWord_3046398).sum := by decide
  have hdescent : baseEnd_3046398 < baseStart_3046398 := by decide
  rcases family_descends (prefixWord ++ tailWord_3046398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3046424 : List Nat := [2, 1, 2, 3, 2, 2, 1, 3, 3, 4]
def baseStart_3046424 : Nat := 118140960795 + 3046424 * 2 ^ 59
def prefixEnd_3046424 : Nat := 4983230072969 + 3 ^ 40 * 3046424 * 2
def baseEnd_3046424 : Nat := 521426596464231361929919

theorem tailTrace_3046424 : CollatzResearch.WordTrace tailWord_3046424 prefixEnd_3046424 521426596464231361929919 := by
  unfold tailWord_3046424
  simp only [CollatzResearch.WordTrace]
  refine ⟨55556105757666805321041163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74074807676889073761388217 55556105757666805321041163)
  ·
    refine ⟨83334158636500207981561745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55556105757666805321041163 83334158636500207981561745)
    ·
      refine ⟨62500618977375155986171309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83334158636500207981561745 62500618977375155986171309)
      ·
        refine ⟨23437732116515683494814241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62500618977375155986171309 23437732116515683494814241)
        ·
          refine ⟨17578299087386762621110681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23437732116515683494814241 17578299087386762621110681)
          ·
            refine ⟨13183724315540071965833011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17578299087386762621110681 13183724315540071965833011)
            ·
              refine ⟨19775586473310107948749517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13183724315540071965833011 19775586473310107948749517)
              ·
                refine ⟨7415844927491290480781069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19775586473310107948749517 7415844927491290480781069)
                ·
                  refine ⟨2780941847809233930292901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7415844927491290480781069 2780941847809233930292901)
                  ·
                    refine ⟨521426596464231361929919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2780941847809233930292901 521426596464231361929919)
                    ·
                      rfl

theorem cell23_3046424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 3, 3, 4].length) (baseStart_3046424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3046424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3046424 prefixEnd_3046424 := by exact prefixLift 3046424
  have htrace : WordTrace (prefixWord ++ tailWord_3046424) baseStart_3046424 baseEnd_3046424 := by
    simpa [prefixWord, tailWord_3046424, baseEnd_3046424] using wordTrace_append hprefix tailTrace_3046424
  have hstable : (prefixWord ++ tailWord_3046424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3046424).length < 2 ^ (prefixWord ++ tailWord_3046424).sum := by decide
  have hdescent : baseEnd_3046424 < baseStart_3046424 := by decide
  rcases family_descends (prefixWord ++ tailWord_3046424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3046434 : List Nat := [3, 3, 1, 1, 1, 3, 1, 2, 1, 4, 3]
def baseStart_3046434 : Nat := 118140960795 + 3046434 * 2 ^ 59
def prefixEnd_3046434 : Nat := 4983230072969 + 3 ^ 40 * 3046434 * 2
def baseEnd_3046434 : Nat := 1564284924199239046664711

theorem tailTrace_3046434 : CollatzResearch.WordTrace tailWord_3046434 prefixEnd_3046434 1564284924199239046664711 := by
  unfold tailWord_3046434
  simp only [CollatzResearch.WordTrace]
  refine ⟨27778144061324345587486589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74075050830198254899964237 27778144061324345587486589)
  ·
    refine ⟨10416804022996629595307471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27778144061324345587486589 10416804022996629595307471)
    ·
      refine ⟨15625206034494944392961207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10416804022996629595307471 15625206034494944392961207)
      ·
        refine ⟨23437809051742416589441811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15625206034494944392961207 23437809051742416589441811)
        ·
          refine ⟨35156713577613624884162717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23437809051742416589441811 35156713577613624884162717)
          ·
            refine ⟨13183767591605109331561019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35156713577613624884162717 13183767591605109331561019)
            ·
              refine ⟨19775651387407663997341529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13183767591605109331561019 19775651387407663997341529)
              ·
                refine ⟨14831738540555747998006147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19775651387407663997341529 14831738540555747998006147)
                ·
                  refine ⟨22247607810833621997009221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14831738540555747998006147 22247607810833621997009221)
                  ·
                    refine ⟨4171426464531304124439229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22247607810833621997009221 4171426464531304124439229)
                    ·
                      refine ⟨1564284924199239046664711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4171426464531304124439229 1564284924199239046664711)
                      ·
                        rfl

theorem cell23_3046434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 2, 1, 4, 3].length) (baseStart_3046434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3046434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3046434 prefixEnd_3046434 := by exact prefixLift 3046434
  have htrace : WordTrace (prefixWord ++ tailWord_3046434) baseStart_3046434 baseEnd_3046434 := by
    simpa [prefixWord, tailWord_3046434, baseEnd_3046434] using wordTrace_append hprefix tailTrace_3046434
  have hstable : (prefixWord ++ tailWord_3046434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3046434).length < 2 ^ (prefixWord ++ tailWord_3046434).sum := by decide
  have hdescent : baseEnd_3046434 < baseStart_3046434 := by decide
  rcases family_descends (prefixWord ++ tailWord_3046434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3046454 : List Nat := [5, 1, 2, 1, 1, 2, 1, 2, 8]
def baseStart_3046454 : Nat := 118140960795 + 3046454 * 2 ^ 59
def prefixEnd_3046454 : Nat := 4983230072969 + 3 ^ 40 * 3046454 * 2
def baseEnd_3046454 : Nat := 173810577090258774268291

theorem tailTrace_3046454 : CollatzResearch.WordTrace tailWord_3046454 prefixEnd_3046454 173810577090258774268291 := by
  unfold tailWord_3046454
  simp only [CollatzResearch.WordTrace]
  refine ⟨6944581606576557860354651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 74075537136816617177116277 6944581606576557860354651)
  ·
    refine ⟨10416872409864836790531977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6944581606576557860354651 10416872409864836790531977)
    ·
      refine ⟨7812654307398627592898983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10416872409864836790531977 7812654307398627592898983)
      ·
        refine ⟨11718981461097941389348475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7812654307398627592898983 11718981461097941389348475)
        ·
          refine ⟨17578472191646912084022713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11718981461097941389348475 17578472191646912084022713)
          ·
            refine ⟨13183854143735184063017035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17578472191646912084022713 13183854143735184063017035)
            ·
              refine ⟨19775781215602776094525553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13183854143735184063017035 19775781215602776094525553)
              ·
                refine ⟨14831835911702082070894165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19775781215602776094525553 14831835911702082070894165)
                ·
                  refine ⟨173810577090258774268291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 14831835911702082070894165 173810577090258774268291)
                  ·
                    rfl

theorem cell23_3046454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 2, 8].length) (baseStart_3046454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3046454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3046454 prefixEnd_3046454 := by exact prefixLift 3046454
  have htrace : WordTrace (prefixWord ++ tailWord_3046454) baseStart_3046454 baseEnd_3046454 := by
    simpa [prefixWord, tailWord_3046454, baseEnd_3046454] using wordTrace_append hprefix tailTrace_3046454
  have hstable : (prefixWord ++ tailWord_3046454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3046454).length < 2 ^ (prefixWord ++ tailWord_3046454).sum := by decide
  have hdescent : baseEnd_3046454 < baseStart_3046454 := by decide
  rcases family_descends (prefixWord ++ tailWord_3046454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3046481 : List Nat := [1, 2, 2, 1, 3, 1, 5, 1, 3, 1, 3]
def baseStart_3046481 : Nat := 118140960795 + 3046481 * 2 ^ 59
def prefixEnd_3046481 : Nat := 4983230072969 + 3 ^ 40 * 3046481 * 2
def baseEnd_3046481 : Nat := 1564309057790000362776995

theorem tailTrace_3046481 : CollatzResearch.WordTrace tailWord_3046481 prefixEnd_3046481 1564309057790000362776995 := by
  unfold tailWord_3046481
  simp only [CollatzResearch.WordTrace]
  refine ⟨111114290476127109376907297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74076193650751406251271531 111114290476127109376907297)
  ·
    refine ⟨83335717857095332032680473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111114290476127109376907297 83335717857095332032680473)
    ·
      refine ⟨62501788392821499024510355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83335717857095332032680473 62501788392821499024510355)
      ·
        refine ⟨93752682589232248536765533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62501788392821499024510355 93752682589232248536765533)
        ·
          refine ⟨35157255970962093201287075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 93752682589232248536765533 35157255970962093201287075)
          ·
            refine ⟨52735883956443139801930613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35157255970962093201287075 52735883956443139801930613)
            ·
              refine ⟨4943989120916544356430995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 52735883956443139801930613 4943989120916544356430995)
              ·
                refine ⟨7415983681374816534646493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4943989120916544356430995 7415983681374816534646493)
                ·
                  refine ⟨2780993880515556200492435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7415983681374816534646493 2780993880515556200492435)
                  ·
                    refine ⟨4171490820773334300738653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2780993880515556200492435 4171490820773334300738653)
                    ·
                      refine ⟨1564309057790000362776995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4171490820773334300738653 1564309057790000362776995)
                      ·
                        rfl

theorem cell23_3046481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 5, 1, 3, 1, 3].length) (baseStart_3046481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3046481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3046481 prefixEnd_3046481 := by exact prefixLift 3046481
  have htrace : WordTrace (prefixWord ++ tailWord_3046481) baseStart_3046481 baseEnd_3046481 := by
    simpa [prefixWord, tailWord_3046481, baseEnd_3046481] using wordTrace_append hprefix tailTrace_3046481
  have hstable : (prefixWord ++ tailWord_3046481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3046481).length < 2 ^ (prefixWord ++ tailWord_3046481).sum := by decide
  have hdescent : baseEnd_3046481 < baseStart_3046481 := by decide
  rcases family_descends (prefixWord ++ tailWord_3046481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3046487 : List Nat := [1, 1, 3, 2, 2, 1, 1, 1, 2, 5, 4]
def baseStart_3046487 : Nat := 118140960795 + 3046487 * 2 ^ 59
def prefixEnd_3046487 : Nat := 4983230072969 + 3 ^ 40 * 3046487 * 2
def baseEnd_3046487 : Nat := 1564312138673927339301967

theorem tailTrace_3046487 : CollatzResearch.WordTrace tailWord_3046487 prefixEnd_3046487 1564312138673927339301967 := by
  unfold tailWord_3046487
  simp only [CollatzResearch.WordTrace]
  refine ⟨111114509314105372401625715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74076339542736914934417143 111114509314105372401625715)
  ·
    refine ⟨166671763971158058602438573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111114509314105372401625715 166671763971158058602438573)
    ·
      refine ⟨62501911489184271975914465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 166671763971158058602438573 62501911489184271975914465)
      ·
        refine ⟨46876433616888203981935849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62501911489184271975914465 46876433616888203981935849)
        ·
          refine ⟨35157325212666152986451887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46876433616888203981935849 35157325212666152986451887)
          ·
            refine ⟨52735987818999229479677831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35157325212666152986451887 52735987818999229479677831)
            ·
              refine ⟨79103981728498844219516747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52735987818999229479677831 79103981728498844219516747)
              ·
                refine ⟨118655972592748266329275121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79103981728498844219516747 118655972592748266329275121)
                ·
                  refine ⟨88991979444561199746956341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 118655972592748266329275121 88991979444561199746956341)
                  ·
                    refine ⟨8342998072927612476277157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 88991979444561199746956341 8342998072927612476277157)
                    ·
                      refine ⟨1564312138673927339301967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8342998072927612476277157 1564312138673927339301967)
                      ·
                        rfl

theorem cell23_3046487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 1, 2, 5, 4].length) (baseStart_3046487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3046487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3046487 prefixEnd_3046487 := by exact prefixLift 3046487
  have htrace : WordTrace (prefixWord ++ tailWord_3046487) baseStart_3046487 baseEnd_3046487 := by
    simpa [prefixWord, tailWord_3046487, baseEnd_3046487] using wordTrace_append hprefix tailTrace_3046487
  have hstable : (prefixWord ++ tailWord_3046487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3046487).length < 2 ^ (prefixWord ++ tailWord_3046487).sum := by decide
  have hdescent : baseEnd_3046487 < baseStart_3046487 := by decide
  rcases family_descends (prefixWord ++ tailWord_3046487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3046514 : List Nat := [3, 2, 1, 2, 2, 1, 3, 2, 1, 6]
def baseStart_3046514 : Nat := 118140960795 + 3046514 * 2 ^ 59
def prefixEnd_3046514 : Nat := 4983230072969 + 3 ^ 40 * 3046514 * 2
def baseEnd_3046514 : Nat := 521442000883866244554781

theorem tailTrace_3046514 : CollatzResearch.WordTrace tailWord_3046514 prefixEnd_3046514 521442000883866244554781 := by
  unfold tailWord_3046514
  simp only [CollatzResearch.WordTrace]
  refine ⟨27778873521251889003214649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74076996056671704008572397 27778873521251889003214649)
  ·
    refine ⟨20834155140938916752410987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27778873521251889003214649 20834155140938916752410987)
    ·
      refine ⟨31251232711408375128616481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20834155140938916752410987 31251232711408375128616481)
      ·
        refine ⟨23438424533556281346462361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31251232711408375128616481 23438424533556281346462361)
        ·
          refine ⟨17578818400167211009846771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23438424533556281346462361 17578818400167211009846771)
          ·
            refine ⟨26368227600250816514770157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17578818400167211009846771 26368227600250816514770157)
            ·
              refine ⟨9888085350094056193038809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26368227600250816514770157 9888085350094056193038809)
              ·
                refine ⟨7416064012570542144779107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9888085350094056193038809 7416064012570542144779107)
                ·
                  refine ⟨11124096018855813217168661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7416064012570542144779107 11124096018855813217168661)
                  ·
                    refine ⟨521442000883866244554781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11124096018855813217168661 521442000883866244554781)
                    ·
                      rfl

theorem cell23_3046514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 3, 2, 1, 6].length) (baseStart_3046514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3046514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3046514 prefixEnd_3046514 := by exact prefixLift 3046514
  have htrace : WordTrace (prefixWord ++ tailWord_3046514) baseStart_3046514 baseEnd_3046514 := by
    simpa [prefixWord, tailWord_3046514, baseEnd_3046514] using wordTrace_append hprefix tailTrace_3046514
  have hstable : (prefixWord ++ tailWord_3046514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3046514).length < 2 ^ (prefixWord ++ tailWord_3046514).sum := by decide
  have hdescent : baseEnd_3046514 < baseStart_3046514 := by decide
  rcases family_descends (prefixWord ++ tailWord_3046514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3046518 : List Nat := [5, 1, 1, 2, 1, 1, 5, 1, 1, 5]
def baseStart_3046518 : Nat := 118140960795 + 3046518 * 2 ^ 59
def prefixEnd_3046518 : Nat := 4983230072969 + 3 ^ 40 * 3046518 * 2
def baseEnd_3046518 : Nat := 521442685524738906004775

theorem tailTrace_3046518 : CollatzResearch.WordTrace tailWord_3046518 prefixEnd_3046518 521442685524738906004775 := by
  unfold tailWord_3046518
  simp only [CollatzResearch.WordTrace]
  refine ⟨6944727498562066543500263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 74077093317995376464002805 6944727498562066543500263)
  ·
    refine ⟨10417091247843099815250395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6944727498562066543500263 10417091247843099815250395)
    ·
      refine ⟨15625636871764649722875593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10417091247843099815250395 15625636871764649722875593)
      ·
        refine ⟨11719227653823487292156695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15625636871764649722875593 11719227653823487292156695)
        ·
          refine ⟨17578841480735230938235043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11719227653823487292156695 17578841480735230938235043)
          ·
            refine ⟨26368262221102846407352565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17578841480735230938235043 26368262221102846407352565)
            ·
              refine ⟨2472024583228391850689303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 26368262221102846407352565 2472024583228391850689303)
              ·
                refine ⟨3708036874842587776033955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2472024583228391850689303 3708036874842587776033955)
                ·
                  refine ⟨5562055312263881664050933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3708036874842587776033955 5562055312263881664050933)
                  ·
                    refine ⟨521442685524738906004775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5562055312263881664050933 521442685524738906004775)
                    ·
                      rfl

theorem cell23_3046518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 5, 1, 1, 5].length) (baseStart_3046518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3046518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3046518 prefixEnd_3046518 := by exact prefixLift 3046518
  have htrace : WordTrace (prefixWord ++ tailWord_3046518) baseStart_3046518 baseEnd_3046518 := by
    simpa [prefixWord, tailWord_3046518, baseEnd_3046518] using wordTrace_append hprefix tailTrace_3046518
  have hstable : (prefixWord ++ tailWord_3046518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3046518).length < 2 ^ (prefixWord ++ tailWord_3046518).sum := by decide
  have hdescent : baseEnd_3046518 < baseStart_3046518 := by decide
  rcases family_descends (prefixWord ++ tailWord_3046518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3046526 : List Nat := [4, 2, 4, 1, 1, 2, 2, 2, 1, 4]
def baseStart_3046526 : Nat := 118140960795 + 3046526 * 2 ^ 59
def prefixEnd_3046526 : Nat := 4983230072969 + 3 ^ 40 * 3046526 * 2
def baseEnd_3046526 : Nat := 521444054806484228904763

theorem tailTrace_3046526 : CollatzResearch.WordTrace tailWord_3046526 prefixEnd_3046526 521444054806484228904763 := by
  unfold tailWord_3046526
  simp only [CollatzResearch.WordTrace]
  refine ⟨13889491470120510257786929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74077287840642721374863621 13889491470120510257786929)
  ·
    refine ⟨10417118602590382693340197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13889491470120510257786929 10417118602590382693340197)
    ·
      refine ⟨1953209737985696755001287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10417118602590382693340197 1953209737985696755001287)
      ·
        refine ⟨2929814606978545132501931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1953209737985696755001287 2929814606978545132501931)
        ·
          refine ⟨4394721910467817698752897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2929814606978545132501931 4394721910467817698752897)
          ·
            refine ⟨3296041432850863274064673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4394721910467817698752897 3296041432850863274064673)
            ·
              refine ⟨2472031074638147455548505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3296041432850863274064673 2472031074638147455548505)
              ·
                refine ⟨1854023305978610591661379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2472031074638147455548505 1854023305978610591661379)
                ·
                  refine ⟨2781034958967915887492069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1854023305978610591661379 2781034958967915887492069)
                  ·
                    refine ⟨521444054806484228904763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2781034958967915887492069 521444054806484228904763)
                    ·
                      rfl

theorem cell23_3046526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 2, 2, 2, 1, 4].length) (baseStart_3046526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3046526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3046526 prefixEnd_3046526 := by exact prefixLift 3046526
  have htrace : WordTrace (prefixWord ++ tailWord_3046526) baseStart_3046526 baseEnd_3046526 := by
    simpa [prefixWord, tailWord_3046526, baseEnd_3046526] using wordTrace_append hprefix tailTrace_3046526
  have hstable : (prefixWord ++ tailWord_3046526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3046526).length < 2 ^ (prefixWord ++ tailWord_3046526).sum := by decide
  have hdescent : baseEnd_3046526 < baseStart_3046526 := by decide
  rcases family_descends (prefixWord ++ tailWord_3046526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3046531 : List Nat := [1, 1, 1, 3, 3, 2, 4, 2, 2, 4]
def baseStart_3046531 : Nat := 118140960795 + 3046531 * 2 ^ 59
def prefixEnd_3046531 : Nat := 4983230072969 + 3 ^ 40 * 3046531 * 2
def baseEnd_3046531 : Nat := 521444910607575055717255

theorem tailTrace_3046531 : CollatzResearch.WordTrace tailWord_3046531 prefixEnd_3046531 521444910607575055717255 := by
  unfold tailWord_3046531
  simp only [CollatzResearch.WordTrace]
  refine ⟨111116114125945967916227447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74077409417297311944151631 111116114125945967916227447)
  ·
    refine ⟨166674171188918951874341171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111116114125945967916227447 166674171188918951874341171)
    ·
      refine ⟨250011256783378427811511757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166674171188918951874341171 250011256783378427811511757)
      ·
        refine ⟨93754221293766910429316909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 250011256783378427811511757 93754221293766910429316909)
        ·
          refine ⟨35157832985162591410993841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 93754221293766910429316909 35157832985162591410993841)
          ·
            refine ⟨26368374738871943558245381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35157832985162591410993841 26368374738871943558245381)
            ·
              refine ⟨4944070263538489417171009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26368374738871943558245381 4944070263538489417171009)
              ·
                refine ⟨3708052697653867062878257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4944070263538489417171009 3708052697653867062878257)
                ·
                  refine ⟨2781039523240400297158693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3708052697653867062878257 2781039523240400297158693)
                  ·
                    refine ⟨521444910607575055717255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2781039523240400297158693 521444910607575055717255)
                    ·
                      rfl

theorem cell23_3046531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 4, 2, 2, 4].length) (baseStart_3046531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3046531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3046531 prefixEnd_3046531 := by exact prefixLift 3046531
  have htrace : WordTrace (prefixWord ++ tailWord_3046531) baseStart_3046531 baseEnd_3046531 := by
    simpa [prefixWord, tailWord_3046531, baseEnd_3046531] using wordTrace_append hprefix tailTrace_3046531
  have hstable : (prefixWord ++ tailWord_3046531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3046531).length < 2 ^ (prefixWord ++ tailWord_3046531).sum := by decide
  have hdescent : baseEnd_3046531 < baseStart_3046531 := by decide
  rcases family_descends (prefixWord ++ tailWord_3046531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3046532 : List Nat := [2, 3, 2, 1, 2, 4, 2, 2, 1, 1, 3]
def baseStart_3046532 : Nat := 118140960795 + 3046532 * 2 ^ 59
def prefixEnd_3046532 : Nat := 4983230072969 + 3 ^ 40 * 3046532 * 2
def baseEnd_3046532 : Nat := 1564335245303379663239261

theorem tailTrace_3046532 : CollatzResearch.WordTrace tailWord_3046532 prefixEnd_3046532 1564335245303379663239261 := by
  unfold tailWord_3046532
  simp only [CollatzResearch.WordTrace]
  refine ⟨55558075299471172543506925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74077433732628230058009233 55558075299471172543506925)
  ·
    refine ⟨20834278237301689703815097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55558075299471172543506925 20834278237301689703815097)
    ·
      refine ⟨15625708677976267277861323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20834278237301689703815097 15625708677976267277861323)
      ·
        refine ⟨23438563016964400916791985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15625708677976267277861323 23438563016964400916791985)
        ·
          refine ⟨17578922262723300687593989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23438563016964400916791985 17578922262723300687593989)
          ·
            refine ⟨3296047924260618878923873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17578922262723300687593989 3296047924260618878923873)
            ·
              refine ⟨2472035943195464159192905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3296047924260618878923873 2472035943195464159192905)
              ·
                refine ⟨1854026957396598119394679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2472035943195464159192905 1854026957396598119394679)
                ·
                  refine ⟨2781040436094897179092019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1854026957396598119394679 2781040436094897179092019)
                  ·
                    refine ⟨4171560654142345768638029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2781040436094897179092019 4171560654142345768638029)
                    ·
                      refine ⟨1564335245303379663239261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4171560654142345768638029 1564335245303379663239261)
                      ·
                        rfl

theorem cell23_3046532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 4, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 4, 2, 2, 1, 1, 3].length) (baseStart_3046532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3046532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3046532 prefixEnd_3046532 := by exact prefixLift 3046532
  have htrace : WordTrace (prefixWord ++ tailWord_3046532) baseStart_3046532 baseEnd_3046532 := by
    simpa [prefixWord, tailWord_3046532, baseEnd_3046532] using wordTrace_append hprefix tailTrace_3046532
  have hstable : (prefixWord ++ tailWord_3046532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3046532).length < 2 ^ (prefixWord ++ tailWord_3046532).sum := by decide
  have hdescent : baseEnd_3046532 < baseStart_3046532 := by decide
  rcases family_descends (prefixWord ++ tailWord_3046532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3046538 : List Nat := [3, 1, 2, 3, 1, 1, 2, 3, 3, 2, 2]
def baseStart_3046538 : Nat := 118140960795 + 3046538 * 2 ^ 59
def prefixEnd_3046538 : Nat := 4983230072969 + 3 ^ 40 * 3046538 * 2
def baseEnd_3046538 : Nat := 1564338326187306639764233

theorem tailTrace_3046538 : CollatzResearch.WordTrace tailWord_3046538 prefixEnd_3046538 1564338326187306639764233 := by
  unfold tailWord_3046538
  simp only [CollatzResearch.WordTrace]
  refine ⟨27779092359230152027933067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74077579624613738741154845 27779092359230152027933067)
  ·
    refine ⟨41668638538845228041899601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27779092359230152027933067 41668638538845228041899601)
    ·
      refine ⟨31251478904133921031424701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41668638538845228041899601 31251478904133921031424701)
      ·
        refine ⟨11719304589050220386784263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31251478904133921031424701 11719304589050220386784263)
        ·
          refine ⟨17578956883575330580176395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11719304589050220386784263 17578956883575330580176395)
          ·
            refine ⟨26368435325362995870264593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17578956883575330580176395 26368435325362995870264593)
            ·
              refine ⟨19776326494022246902698445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26368435325362995870264593 19776326494022246902698445)
              ·
                refine ⟨7416122435258342588511917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19776326494022246902698445 7416122435258342588511917)
                ·
                  refine ⟨2781045913221878470691969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7416122435258342588511917 2781045913221878470691969)
                  ·
                    refine ⟨2085784434916408853018977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2781045913221878470691969 2085784434916408853018977)
                    ·
                      refine ⟨1564338326187306639764233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2085784434916408853018977 1564338326187306639764233)
                      ·
                        rfl

theorem cell23_3046538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 3, 3, 2, 2].length) (baseStart_3046538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3046538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3046538 prefixEnd_3046538 := by exact prefixLift 3046538
  have htrace : WordTrace (prefixWord ++ tailWord_3046538) baseStart_3046538 baseEnd_3046538 := by
    simpa [prefixWord, tailWord_3046538, baseEnd_3046538] using wordTrace_append hprefix tailTrace_3046538
  have hstable : (prefixWord ++ tailWord_3046538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3046538).length < 2 ^ (prefixWord ++ tailWord_3046538).sum := by decide
  have hdescent : baseEnd_3046538 < baseStart_3046538 := by decide
  rcases family_descends (prefixWord ++ tailWord_3046538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3046547 : List Nat := [1, 1, 1, 2, 1, 2, 4, 1, 2, 2, 6]
def baseStart_3046547 : Nat := 118140960795 + 3046547 * 2 ^ 59
def prefixEnd_3046547 : Nat := 4983230072969 + 3 ^ 40 * 3046547 * 2
def baseEnd_3046547 : Nat := 1564342947513197104551691

theorem tailTrace_3046547 : CollatzResearch.WordTrace tailWord_3046547 prefixEnd_3046547 1564342947513197104551691 := by
  unfold tailWord_3046547
  simp only [CollatzResearch.WordTrace]
  refine ⟨111116697693888002648809895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74077798462592001765873263 111116697693888002648809895)
  ·
    refine ⟨166675046540832003973214843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111116697693888002648809895 166675046540832003973214843)
    ·
      refine ⟨250012569811248005959822265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166675046540832003973214843 250012569811248005959822265)
      ·
        refine ⟨187509427358436004469866699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 250012569811248005959822265 187509427358436004469866699)
        ·
          refine ⟨281264141037654006704800049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 187509427358436004469866699 281264141037654006704800049)
          ·
            refine ⟨210948105778240505028600037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 281264141037654006704800049 210948105778240505028600037)
            ·
              refine ⟨39552769833420094692862507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 210948105778240505028600037 39552769833420094692862507)
              ·
                refine ⟨59329154750130142039293761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39552769833420094692862507 59329154750130142039293761)
                ·
                  refine ⟨44496866062597606529470321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59329154750130142039293761 44496866062597606529470321)
                  ·
                    refine ⟨33372649546948204897102741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 44496866062597606529470321 33372649546948204897102741)
                    ·
                      refine ⟨1564342947513197104551691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 33372649546948204897102741 1564342947513197104551691)
                      ·
                        rfl

theorem cell23_3046547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 1, 2, 2, 6].length) (baseStart_3046547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3046547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3046547 prefixEnd_3046547 := by exact prefixLift 3046547
  have htrace : WordTrace (prefixWord ++ tailWord_3046547) baseStart_3046547 baseEnd_3046547 := by
    simpa [prefixWord, tailWord_3046547, baseEnd_3046547] using wordTrace_append hprefix tailTrace_3046547
  have hstable : (prefixWord ++ tailWord_3046547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3046547).length < 2 ^ (prefixWord ++ tailWord_3046547).sum := by decide
  have hdescent : baseEnd_3046547 < baseStart_3046547 := by decide
  rcases family_descends (prefixWord ++ tailWord_3046547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3046551 : List Nat := [1, 1, 3, 3, 3, 2, 2, 1, 1, 2, 4]
def baseStart_3046551 : Nat := 118140960795 + 3046551 * 2 ^ 59
def prefixEnd_3046551 : Nat := 4983230072969 + 3 ^ 40 * 3046551 * 2
def baseEnd_3046551 : Nat := 1564345001435815088901673

theorem tailTrace_3046551 : CollatzResearch.WordTrace tailWord_3046551 prefixEnd_3046551 1564345001435815088901673 := by
  unfold tailWord_3046551
  simp only [CollatzResearch.WordTrace]
  refine ⟨111116843585873511331955507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74077895723915674221303671 111116843585873511331955507)
  ·
    refine ⟨166675265378810266997933261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111116843585873511331955507 166675265378810266997933261)
    ·
      refine ⟨62503224517053850124224973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 166675265378810266997933261 62503224517053850124224973)
      ·
        refine ⟨23438709193895193796584365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62503224517053850124224973 23438709193895193796584365)
        ·
          refine ⟨8789515947710697673719137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23438709193895193796584365 8789515947710697673719137)
          ·
            refine ⟨6592136960783023255289353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8789515947710697673719137 6592136960783023255289353)
            ·
              refine ⟨4944102720587267441467015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6592136960783023255289353 4944102720587267441467015)
              ·
                refine ⟨7416154080880901162200523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4944102720587267441467015 7416154080880901162200523)
                ·
                  refine ⟨11124231121321351743300785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7416154080880901162200523 11124231121321351743300785)
                  ·
                    refine ⟨8343173340991013807475589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11124231121321351743300785 8343173340991013807475589)
                    ·
                      refine ⟨1564345001435815088901673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8343173340991013807475589 1564345001435815088901673)
                      ·
                        rfl

theorem cell23_3046551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 2, 1, 1, 2, 4].length) (baseStart_3046551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3046551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3046551 prefixEnd_3046551 := by exact prefixLift 3046551
  have htrace : WordTrace (prefixWord ++ tailWord_3046551) baseStart_3046551 baseEnd_3046551 := by
    simpa [prefixWord, tailWord_3046551, baseEnd_3046551] using wordTrace_append hprefix tailTrace_3046551
  have hstable : (prefixWord ++ tailWord_3046551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3046551).length < 2 ^ (prefixWord ++ tailWord_3046551).sum := by decide
  have hdescent : baseEnd_3046551 < baseStart_3046551 := by decide
  rcases family_descends (prefixWord ++ tailWord_3046551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3046558 : List Nat := [4, 3, 1, 1, 2, 1, 2, 1, 3, 2, 3]
def baseStart_3046558 : Nat := 118140960795 + 3046558 * 2 ^ 59
def prefixEnd_3046558 : Nat := 4983230072969 + 3 ^ 40 * 3046558 * 2
def baseEnd_3046558 : Nat := 1564348595800396561514141

theorem tailTrace_3046558 : CollatzResearch.WordTrace tailWord_3046558 prefixEnd_3046558 1564348595800396561514141 := by
  unfold tailWord_3046558
  simp only [CollatzResearch.WordTrace]
  refine ⟨13889637362106018940932541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74078065931232101018306885 13889637362106018940932541)
  ·
    refine ⟨5208614010789757102849703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13889637362106018940932541 5208614010789757102849703)
    ·
      refine ⟨7812921016184635654274555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5208614010789757102849703 7812921016184635654274555)
      ·
        refine ⟨11719381524276953481411833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7812921016184635654274555 11719381524276953481411833)
        ·
          refine ⟨8789536143207715111058875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11719381524276953481411833 8789536143207715111058875)
          ·
            refine ⟨13184304214811572666588313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8789536143207715111058875 13184304214811572666588313)
            ·
              refine ⟨9888228161108679499941235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13184304214811572666588313 9888228161108679499941235)
              ·
                refine ⟨14832342241663019249911853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9888228161108679499941235 14832342241663019249911853)
                ·
                  refine ⟨5562128340623632218716945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14832342241663019249911853 5562128340623632218716945)
                  ·
                    refine ⟨4171596255467724164037709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5562128340623632218716945 4171596255467724164037709)
                    ·
                      refine ⟨1564348595800396561514141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4171596255467724164037709 1564348595800396561514141)
                      ·
                        rfl

theorem cell23_3046558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 2, 1, 3, 2, 3].length) (baseStart_3046558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3046558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3046558 prefixEnd_3046558 := by exact prefixLift 3046558
  have htrace : WordTrace (prefixWord ++ tailWord_3046558) baseStart_3046558 baseEnd_3046558 := by
    simpa [prefixWord, tailWord_3046558, baseEnd_3046558] using wordTrace_append hprefix tailTrace_3046558
  have hstable : (prefixWord ++ tailWord_3046558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3046558).length < 2 ^ (prefixWord ++ tailWord_3046558).sum := by decide
  have hdescent : baseEnd_3046558 < baseStart_3046558 := by decide
  rcases family_descends (prefixWord ++ tailWord_3046558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3046588 : List Nat := [2, 2, 2, 3, 2, 2, 1, 1, 4, 1, 3]
def baseStart_3046588 : Nat := 118140960795 + 3046588 * 2 ^ 59
def prefixEnd_3046588 : Nat := 4983230072969 + 3 ^ 40 * 3046588 * 2
def baseEnd_3046588 : Nat := 1564364000220031444139003

theorem tailTrace_3046588 : CollatzResearch.WordTrace tailWord_3046588 prefixEnd_3046588 1564364000220031444139003 := by
  unfold tailWord_3046588
  simp only [CollatzResearch.WordTrace]
  refine ⟨55559096543369733325526209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74078795391159644434034945 55559096543369733325526209)
  ·
    refine ⟨41669322407527299994144657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55559096543369733325526209 41669322407527299994144657)
    ·
      refine ⟨31251991805645474995608493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41669322407527299994144657 31251991805645474995608493)
      ·
        refine ⟨11719496927117053123353185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31251991805645474995608493 11719496927117053123353185)
        ·
          refine ⟨8789622695337789842514889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11719496927117053123353185 8789622695337789842514889)
          ·
            refine ⟨6592217021503342381886167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8789622695337789842514889 6592217021503342381886167)
            ·
              refine ⟨9888325532255013572829251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6592217021503342381886167 9888325532255013572829251)
              ·
                refine ⟨14832488298382520359243877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9888325532255013572829251 14832488298382520359243877)
                ·
                  refine ⟨2781091555946722567358227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14832488298382520359243877 2781091555946722567358227)
                  ·
                    refine ⟨4171637333920083851037341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2781091555946722567358227 4171637333920083851037341)
                    ·
                      refine ⟨1564364000220031444139003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4171637333920083851037341 1564364000220031444139003)
                      ·
                        rfl

theorem cell23_3046588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 1, 1, 4, 1, 3].length) (baseStart_3046588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3046588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3046588 prefixEnd_3046588 := by exact prefixLift 3046588
  have htrace : WordTrace (prefixWord ++ tailWord_3046588) baseStart_3046588 baseEnd_3046588 := by
    simpa [prefixWord, tailWord_3046588, baseEnd_3046588] using wordTrace_append hprefix tailTrace_3046588
  have hstable : (prefixWord ++ tailWord_3046588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3046588).length < 2 ^ (prefixWord ++ tailWord_3046588).sum := by decide
  have hdescent : baseEnd_3046588 < baseStart_3046588 := by decide
  rcases family_descends (prefixWord ++ tailWord_3046588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3046628 : List Nat := [2, 3, 1, 1, 1, 2, 3, 2, 4, 2, 2]
def baseStart_3046628 : Nat := 118140960795 + 3046628 * 2 ^ 59
def prefixEnd_3046628 : Nat := 4983230072969 + 3 ^ 40 * 3046628 * 2
def baseEnd_3046628 : Nat := 1564384539446211287638819

theorem tailTrace_3046628 : CollatzResearch.WordTrace tailWord_3046628 prefixEnd_3046628 1564384539446211287638819 := by
  unfold tailWord_3046628
  simp only [CollatzResearch.WordTrace]
  refine ⟨55559826003297276741254269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74079768004396368988339025 55559826003297276741254269)
  ·
    refine ⟨20834934751236478777970351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55559826003297276741254269 20834934751236478777970351)
    ·
      refine ⟨31252402126854718166955527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20834934751236478777970351 31252402126854718166955527)
      ·
        refine ⟨46878603190282077250433291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31252402126854718166955527 46878603190282077250433291)
        ·
          refine ⟨70317904785423115875649937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46878603190282077250433291 70317904785423115875649937)
          ·
            refine ⟨52738428589067336906737453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70317904785423115875649937 52738428589067336906737453)
            ·
              refine ⟨19776910720900251340026545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52738428589067336906737453 19776910720900251340026545)
              ·
                refine ⟨14832683040675188505019909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19776910720900251340026545 14832683040675188505019909)
                ·
                  refine ⟨2781128070126597844691233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14832683040675188505019909 2781128070126597844691233)
                  ·
                    refine ⟨2085846052594948383518425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2781128070126597844691233 2085846052594948383518425)
                    ·
                      refine ⟨1564384539446211287638819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2085846052594948383518425 1564384539446211287638819)
                      ·
                        rfl

theorem cell23_3046628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 2, 4, 2, 2].length) (baseStart_3046628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3046628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3046628 prefixEnd_3046628 := by exact prefixLift 3046628
  have htrace : WordTrace (prefixWord ++ tailWord_3046628) baseStart_3046628 baseEnd_3046628 := by
    simpa [prefixWord, tailWord_3046628, baseEnd_3046628] using wordTrace_append hprefix tailTrace_3046628
  have hstable : (prefixWord ++ tailWord_3046628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3046628).length < 2 ^ (prefixWord ++ tailWord_3046628).sum := by decide
  have hdescent : baseEnd_3046628 < baseStart_3046628 := by decide
  rcases family_descends (prefixWord ++ tailWord_3046628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3046698 : List Nat := [3, 1, 4, 2, 1, 1, 2, 2, 2, 5]
def baseStart_3046698 : Nat := 118140960795 + 3046698 * 2 ^ 59
def prefixEnd_3046698 : Nat := 4983230072969 + 3 ^ 40 * 3046698 * 2
def baseEnd_3046698 : Nat := 521473494364008671254499

theorem tailTrace_3046698 : CollatzResearch.WordTrace tailWord_3046698 prefixEnd_3046698 521473494364008671254499 := by
  unfold tailWord_3046698
  simp only [CollatzResearch.WordTrace]
  refine ⟨27780551279085238859389187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74081470077560636958371165 27780551279085238859389187)
  ·
    refine ⟨41670826918627858289083781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27780551279085238859389187 41670826918627858289083781)
    ·
      refine ⟨7813280047242723429203209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41670826918627858289083781 7813280047242723429203209)
      ·
        refine ⟨5859960035432042571902407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7813280047242723429203209 5859960035432042571902407)
        ·
          refine ⟨8789940053148063857853611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5859960035432042571902407 8789940053148063857853611)
          ·
            refine ⟨13184910079722095786780417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8789940053148063857853611 13184910079722095786780417)
            ·
              refine ⟨9888682559791571840085313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13184910079722095786780417 9888682559791571840085313)
              ·
                refine ⟨7416511919843678880063985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9888682559791571840085313 7416511919843678880063985)
                ·
                  refine ⟨5562383939882759160047989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7416511919843678880063985 5562383939882759160047989)
                  ·
                    refine ⟨521473494364008671254499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5562383939882759160047989 521473494364008671254499)
                    ·
                      rfl

theorem cell23_3046698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 2, 2, 2, 5].length) (baseStart_3046698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3046698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3046698 prefixEnd_3046698 := by exact prefixLift 3046698
  have htrace : WordTrace (prefixWord ++ tailWord_3046698) baseStart_3046698 baseEnd_3046698 := by
    simpa [prefixWord, tailWord_3046698, baseEnd_3046698] using wordTrace_append hprefix tailTrace_3046698
  have hstable : (prefixWord ++ tailWord_3046698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3046698).length < 2 ^ (prefixWord ++ tailWord_3046698).sum := by decide
  have hdescent : baseEnd_3046698 < baseStart_3046698 := by decide
  rcases family_descends (prefixWord ++ tailWord_3046698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3046704 : List Nat := [2, 1, 1, 1, 2, 2, 3, 1, 2, 3, 5]
def baseStart_3046704 : Nat := 118140960795 + 3046704 * 2 ^ 59
def prefixEnd_3046704 : Nat := 4983230072969 + 3 ^ 40 * 3046704 * 2
def baseEnd_3046704 : Nat := 1564423563975952990288469

theorem tailTrace_3046704 : CollatzResearch.WordTrace tailWord_3046704 prefixEnd_3046704 1564423563975952990288469 := by
  unfold tailWord_3046704
  simp only [CollatzResearch.WordTrace]
  refine ⟨55561211977159609231137583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74081615969546145641516777 55561211977159609231137583)
  ·
    refine ⟨83341817965739413846706375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55561211977159609231137583 83341817965739413846706375)
    ·
      refine ⟨125012726948609120770059563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83341817965739413846706375 125012726948609120770059563)
      ·
        refine ⟨187519090422913681155089345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125012726948609120770059563 187519090422913681155089345)
        ·
          refine ⟨140639317817185260866317009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 187519090422913681155089345 140639317817185260866317009)
          ·
            refine ⟨105479488362888945649737757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 140639317817185260866317009 105479488362888945649737757)
            ·
              refine ⟨39554808136083354618651659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 105479488362888945649737757 39554808136083354618651659)
              ·
                refine ⟨59332212204125031927977489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39554808136083354618651659 59332212204125031927977489)
                ·
                  refine ⟨44499159153093773945983117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59332212204125031927977489 44499159153093773945983117)
                  ·
                    refine ⟨16687184682410165229743669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 44499159153093773945983117 16687184682410165229743669)
                    ·
                      refine ⟨1564423563975952990288469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16687184682410165229743669 1564423563975952990288469)
                      ·
                        rfl

theorem cell23_3046704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 1, 2, 3, 5].length) (baseStart_3046704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3046704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3046704 prefixEnd_3046704 := by exact prefixLift 3046704
  have htrace : WordTrace (prefixWord ++ tailWord_3046704) baseStart_3046704 baseEnd_3046704 := by
    simpa [prefixWord, tailWord_3046704, baseEnd_3046704] using wordTrace_append hprefix tailTrace_3046704
  have hstable : (prefixWord ++ tailWord_3046704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3046704).length < 2 ^ (prefixWord ++ tailWord_3046704).sum := by decide
  have hdescent : baseEnd_3046704 < baseStart_3046704 := by decide
  rcases family_descends (prefixWord ++ tailWord_3046704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3046778 : List Nat := [3, 1, 1, 1, 1, 1, 2, 4, 4, 3, 2]
def baseStart_3046778 : Nat := 118140960795 + 3046778 * 2 ^ 59
def prefixEnd_3046778 : Nat := 4983230072969 + 3 ^ 40 * 3046778 * 2
def baseEnd_3046778 : Nat := 1564461561544385700763129

theorem tailTrace_3046778 : CollatzResearch.WordTrace tailWord_3046778 prefixEnd_3046778 1564461561544385700763129 := by
  unfold tailWord_3046778
  simp only [CollatzResearch.WordTrace]
  refine ⟨27781280739012782275117247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74083415304034086066979325 27781280739012782275117247)
  ·
    refine ⟨41671921108519173412675871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27781280739012782275117247 41671921108519173412675871)
    ·
      refine ⟨62507881662778760119013807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41671921108519173412675871 62507881662778760119013807)
      ·
        refine ⟨93761822494168140178520711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62507881662778760119013807 93761822494168140178520711)
        ·
          refine ⟨140642733741252210267781067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93761822494168140178520711 140642733741252210267781067)
          ·
            refine ⟨210964100611878315401671601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140642733741252210267781067 210964100611878315401671601)
            ·
              refine ⟨158223075458908736551253701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 210964100611878315401671601 158223075458908736551253701)
              ·
                refine ⟨29666826648545388103360069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 158223075458908736551253701 29666826648545388103360069)
                ·
                  refine ⟨5562529996602260269380013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29666826648545388103360069 5562529996602260269380013)
                  ·
                    refine ⟨2085948748725847601017505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5562529996602260269380013 2085948748725847601017505)
                    ·
                      refine ⟨1564461561544385700763129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2085948748725847601017505 1564461561544385700763129)
                      ·
                        rfl

theorem cell23_3046778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 4, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 4, 4, 3, 2].length) (baseStart_3046778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3046778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3046778 prefixEnd_3046778 := by exact prefixLift 3046778
  have htrace : WordTrace (prefixWord ++ tailWord_3046778) baseStart_3046778 baseEnd_3046778 := by
    simpa [prefixWord, tailWord_3046778, baseEnd_3046778] using wordTrace_append hprefix tailTrace_3046778
  have hstable : (prefixWord ++ tailWord_3046778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3046778).length < 2 ^ (prefixWord ++ tailWord_3046778).sum := by decide
  have hdescent : baseEnd_3046778 < baseStart_3046778 := by decide
  rcases family_descends (prefixWord ++ tailWord_3046778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3046788 : List Nat := [2, 3, 2, 1, 1, 3, 1, 4, 1, 5]
def baseStart_3046788 : Nat := 118140960795 + 3046788 * 2 ^ 59
def prefixEnd_3046788 : Nat := 4983230072969 + 3 ^ 40 * 3046788 * 2
def baseEnd_3046788 : Nat := 521488898783643553879361

theorem tailTrace_3046788 : CollatzResearch.WordTrace tailWord_3046788 prefixEnd_3046788 521488898783643553879361 := by
  unfold tailWord_3046788
  simp only [CollatzResearch.WordTrace]
  refine ⟨55562743843007450404166509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74083658457343267205555345 55562743843007450404166509)
  ·
    refine ⟨20836028941127793901562441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55562743843007450404166509 20836028941127793901562441)
    ·
      refine ⟨15627021705845845426171831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20836028941127793901562441 15627021705845845426171831)
      ·
        refine ⟨23440532558768768139257747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15627021705845845426171831 23440532558768768139257747)
        ·
          refine ⟨35160798838153152208886621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23440532558768768139257747 35160798838153152208886621)
          ·
            refine ⟨13185299564307432078332483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35160798838153152208886621 13185299564307432078332483)
            ·
              refine ⟨19777949346461148117498725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13185299564307432078332483 19777949346461148117498725)
              ·
                refine ⟨3708365502461465272031011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19777949346461148117498725 3708365502461465272031011)
                ·
                  refine ⟨5562548253692197908046517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3708365502461465272031011 5562548253692197908046517)
                  ·
                    refine ⟨521488898783643553879361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5562548253692197908046517 521488898783643553879361)
                    ·
                      rfl

theorem cell23_3046788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 4, 1, 5].length) (baseStart_3046788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3046788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3046788 prefixEnd_3046788 := by exact prefixLift 3046788
  have htrace : WordTrace (prefixWord ++ tailWord_3046788) baseStart_3046788 baseEnd_3046788 := by
    simpa [prefixWord, tailWord_3046788, baseEnd_3046788] using wordTrace_append hprefix tailTrace_3046788
  have hstable : (prefixWord ++ tailWord_3046788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3046788).length < 2 ^ (prefixWord ++ tailWord_3046788).sum := by decide
  have hdescent : baseEnd_3046788 < baseStart_3046788 := by decide
  rcases family_descends (prefixWord ++ tailWord_3046788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3046821 : List Nat := [1, 3, 1, 2, 1, 1, 2, 1, 5, 2, 4]
def baseStart_3046821 : Nat := 118140960795 + 3046821 * 2 ^ 59
def prefixEnd_3046821 : Nat := 4983230072969 + 3 ^ 40 * 3046821 * 2
def baseEnd_3046821 : Nat := 1564483641212529032525431

theorem tailTrace_3046821 : CollatzResearch.WordTrace tailWord_3046821 prefixEnd_3046821 1564483641212529032525431 := by
  unfold tailWord_3046821
  simp only [CollatzResearch.WordTrace]
  refine ⟨111126691294895347444284317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74084460863263564962856211 111126691294895347444284317)
  ·
    refine ⟨41672509235585755291606619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111126691294895347444284317 41672509235585755291606619)
    ·
      refine ⟨62508763853378632937409929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41672509235585755291606619 62508763853378632937409929)
      ·
        refine ⟨46881572890033974703057447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62508763853378632937409929 46881572890033974703057447)
        ·
          refine ⟨70322359335050962054586171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46881572890033974703057447 70322359335050962054586171)
          ·
            refine ⟨105483539002576443081879257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70322359335050962054586171 105483539002576443081879257)
            ·
              refine ⟨79112654251932332311409443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 105483539002576443081879257 79112654251932332311409443)
              ·
                refine ⟨118668981377898498467114165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79112654251932332311409443 118668981377898498467114165)
                ·
                  refine ⟨11125217004177984231291953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 118668981377898498467114165 11125217004177984231291953)
                  ·
                    refine ⟨8343912753133488173468965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11125217004177984231291953 8343912753133488173468965)
                    ·
                      refine ⟨1564483641212529032525431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8343912753133488173468965 1564483641212529032525431)
                      ·
                        rfl

theorem cell23_3046821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 1, 5, 2, 4].length) (baseStart_3046821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3046821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3046821 prefixEnd_3046821 := by exact prefixLift 3046821
  have htrace : WordTrace (prefixWord ++ tailWord_3046821) baseStart_3046821 baseEnd_3046821 := by
    simpa [prefixWord, tailWord_3046821, baseEnd_3046821] using wordTrace_append hprefix tailTrace_3046821
  have hstable : (prefixWord ++ tailWord_3046821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3046821).length < 2 ^ (prefixWord ++ tailWord_3046821).sum := by decide
  have hdescent : baseEnd_3046821 < baseStart_3046821 := by decide
  rcases family_descends (prefixWord ++ tailWord_3046821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3046858 : List Nat := [3, 1, 2, 1, 2, 3, 1, 1, 3, 3, 3]
def baseStart_3046858 : Nat := 118140960795 + 3046858 * 2 ^ 59
def prefixEnd_3046858 : Nat := 4983230072969 + 3 ^ 40 * 3046858 * 2
def baseEnd_3046858 : Nat := 1564502639996745387762761

theorem tailTrace_3046858 : CollatzResearch.WordTrace tailWord_3046858 prefixEnd_3046858 1564502639996745387762761 := by
  unfold tailWord_3046858
  simp only [CollatzResearch.WordTrace]
  refine ⟨27782010198940325690845307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74085360530507535175587485 27782010198940325690845307)
  ·
    refine ⟨41673015298410488536267961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27782010198940325690845307 41673015298410488536267961)
    ·
      refine ⟨31254761473807866402200971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41673015298410488536267961 31254761473807866402200971)
      ·
        refine ⟨46882142210711799603301457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31254761473807866402200971 46882142210711799603301457)
        ·
          refine ⟨35161606658033849702476093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46882142210711799603301457 35161606658033849702476093)
          ·
            refine ⟨13185602496762693638428535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35161606658033849702476093 13185602496762693638428535)
            ·
              refine ⟨19778403745144040457642803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13185602496762693638428535 19778403745144040457642803)
              ·
                refine ⟨29667605617716060686464205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19778403745144040457642803 29667605617716060686464205)
                ·
                  refine ⟨11125352106643522757424077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29667605617716060686464205 11125352106643522757424077)
                  ·
                    refine ⟨4172007039991321034034029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11125352106643522757424077 4172007039991321034034029)
                    ·
                      refine ⟨1564502639996745387762761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4172007039991321034034029 1564502639996745387762761)
                      ·
                        rfl

theorem cell23_3046858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 1, 3, 3, 3].length) (baseStart_3046858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3046858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3046858 prefixEnd_3046858 := by exact prefixLift 3046858
  have htrace : WordTrace (prefixWord ++ tailWord_3046858) baseStart_3046858 baseEnd_3046858 := by
    simpa [prefixWord, tailWord_3046858, baseEnd_3046858] using wordTrace_append hprefix tailTrace_3046858
  have hstable : (prefixWord ++ tailWord_3046858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3046858).length < 2 ^ (prefixWord ++ tailWord_3046858).sum := by decide
  have hdescent : baseEnd_3046858 < baseStart_3046858 := by decide
  rcases family_descends (prefixWord ++ tailWord_3046858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3046871 : List Nat := [1, 1, 3, 2, 1, 1, 1, 4, 2, 2, 5]
def baseStart_3046871 : Nat := 118140960795 + 3046871 * 2 ^ 59
def prefixEnd_3046871 : Nat := 4983230072969 + 3 ^ 40 * 3046871 * 2
def baseEnd_3046871 : Nat := 1564509315245253836900201

theorem tailTrace_3046871 : CollatzResearch.WordTrace tailWord_3046871 prefixEnd_3046871 1564509315245253836900201 := by
  unfold tailWord_3046871
  simp only [CollatzResearch.WordTrace]
  refine ⟨111128514944714205983604467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74085676629809470655736311 111128514944714205983604467)
  ·
    refine ⟨166692772417071308975406701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111128514944714205983604467 166692772417071308975406701)
    ·
      refine ⟨62509789656401740865777513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 166692772417071308975406701 62509789656401740865777513)
      ·
        refine ⟨46882342242301305649333135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62509789656401740865777513 46882342242301305649333135)
        ·
          refine ⟨70323513363451958473999703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46882342242301305649333135 70323513363451958473999703)
          ·
            refine ⟨105485270045177937710999555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70323513363451958473999703 105485270045177937710999555)
            ·
              refine ⟨158227905067766906566499333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105485270045177937710999555 158227905067766906566499333)
              ·
                refine ⟨29667732200206294981218625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 158227905067766906566499333 29667732200206294981218625)
                ·
                  refine ⟨22250799150154721235913969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29667732200206294981218625 22250799150154721235913969)
                  ·
                    refine ⟨16688099362616040926935477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22250799150154721235913969 16688099362616040926935477)
                    ·
                      refine ⟨1564509315245253836900201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16688099362616040926935477 1564509315245253836900201)
                      ·
                        rfl

theorem cell23_3046871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 4, 2, 2, 5].length) (baseStart_3046871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3046871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3046871 prefixEnd_3046871 := by exact prefixLift 3046871
  have htrace : WordTrace (prefixWord ++ tailWord_3046871) baseStart_3046871 baseEnd_3046871 := by
    simpa [prefixWord, tailWord_3046871, baseEnd_3046871] using wordTrace_append hprefix tailTrace_3046871
  have hstable : (prefixWord ++ tailWord_3046871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3046871).length < 2 ^ (prefixWord ++ tailWord_3046871).sum := by decide
  have hdescent : baseEnd_3046871 < baseStart_3046871 := by decide
  rcases family_descends (prefixWord ++ tailWord_3046871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3046902 : List Nat := [5, 1, 1, 1, 2, 2, 2, 1, 3, 3, 2]
def baseStart_3046902 : Nat := 118140960795 + 3046902 * 2 ^ 59
def prefixEnd_3046902 : Nat := 4983230072969 + 3 ^ 40 * 3046902 * 2
def baseEnd_3046902 : Nat := 1564525233145543215612559

theorem tailTrace_3046902 : CollatzResearch.WordTrace tailWord_3046902 prefixEnd_3046902 1564525233145543215612559 := by
  unfold tailWord_3046902
  simp only [CollatzResearch.WordTrace]
  refine ⟨6945602850475118642373935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 74086430405067932185321973 6945602850475118642373935)
  ·
    refine ⟨10418404275712677963560903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6945602850475118642373935 10418404275712677963560903)
    ·
      refine ⟨15627606413569016945341355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10418404275712677963560903 15627606413569016945341355)
      ·
        refine ⟨23441409620353525418012033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15627606413569016945341355 23441409620353525418012033)
        ·
          refine ⟨17581057215265144063509025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23441409620353525418012033 17581057215265144063509025)
          ·
            refine ⟨13185792911448858047631769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17581057215265144063509025 13185792911448858047631769)
            ·
              refine ⟨9889344683586643535723827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13185792911448858047631769 9889344683586643535723827)
              ·
                refine ⟨14834017025379965303585741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9889344683586643535723827 14834017025379965303585741)
                ·
                  refine ⟨5562756384517486988844653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14834017025379965303585741 5562756384517486988844653)
                  ·
                    refine ⟨2086033644194057620816745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5562756384517486988844653 2086033644194057620816745)
                    ·
                      refine ⟨1564525233145543215612559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2086033644194057620816745 1564525233145543215612559)
                      ·
                        rfl

theorem cell23_3046902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 2, 1, 3, 3, 2].length) (baseStart_3046902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3046902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3046902 prefixEnd_3046902 := by exact prefixLift 3046902
  have htrace : WordTrace (prefixWord ++ tailWord_3046902) baseStart_3046902 baseEnd_3046902 := by
    simpa [prefixWord, tailWord_3046902, baseEnd_3046902] using wordTrace_append hprefix tailTrace_3046902
  have hstable : (prefixWord ++ tailWord_3046902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3046902).length < 2 ^ (prefixWord ++ tailWord_3046902).sum := by decide
  have hdescent : baseEnd_3046902 < baseStart_3046902 := by decide
  rcases family_descends (prefixWord ++ tailWord_3046902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3046919 : List Nat := [1, 1, 4, 3, 2, 1, 4, 1, 1, 3, 2]
def baseStart_3046919 : Nat := 118140960795 + 3046919 * 2 ^ 59
def prefixEnd_3046919 : Nat := 4983230072969 + 3 ^ 40 * 3046919 * 2
def baseEnd_3046919 : Nat := 1564533962316669649099981

theorem tailTrace_3046919 : CollatzResearch.WordTrace tailWord_3046919 prefixEnd_3046919 1564533962316669649099981 := by
  unfold tailWord_3046919
  simp only [CollatzResearch.WordTrace]
  refine ⟨111130265648540310181351811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74086843765693540120901207 111130265648540310181351811)
  ·
    refine ⟨166695398472810465272027717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111130265648540310181351811 166695398472810465272027717)
    ·
      refine ⟨31255387213651962238505197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 166695398472810465272027717 31255387213651962238505197)
      ·
        refine ⟨11720770205119485839439449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31255387213651962238505197 11720770205119485839439449)
        ·
          refine ⟨8790577653839614379579587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11720770205119485839439449 8790577653839614379579587)
          ·
            refine ⟨13185866480759421569369381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8790577653839614379579587 13185866480759421569369381)
            ·
              refine ⟨2472349965142391544256759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13185866480759421569369381 2472349965142391544256759)
              ·
                refine ⟨3708524947713587316385139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2472349965142391544256759 3708524947713587316385139)
                ·
                  refine ⟨5562787421570380974577709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3708524947713587316385139 5562787421570380974577709)
                  ·
                    refine ⟨2086045283088892865466641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5562787421570380974577709 2086045283088892865466641)
                    ·
                      refine ⟨1564533962316669649099981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2086045283088892865466641 1564533962316669649099981)
                      ·
                        rfl

theorem cell23_3046919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 4, 1, 1, 3, 2].length) (baseStart_3046919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3046919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3046919 prefixEnd_3046919 := by exact prefixLift 3046919
  have htrace : WordTrace (prefixWord ++ tailWord_3046919) baseStart_3046919 baseEnd_3046919 := by
    simpa [prefixWord, tailWord_3046919, baseEnd_3046919] using wordTrace_append hprefix tailTrace_3046919
  have hstable : (prefixWord ++ tailWord_3046919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3046919).length < 2 ^ (prefixWord ++ tailWord_3046919).sum := by decide
  have hdescent : baseEnd_3046919 < baseStart_3046919 := by decide
  rcases family_descends (prefixWord ++ tailWord_3046919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3046921 : List Nat := [1, 2, 1, 1, 3, 1, 3, 2, 9]
def baseStart_3046921 : Nat := 118140960795 + 3046921 * 2 ^ 59
def prefixEnd_3046921 : Nat := 4983230072969 + 3 ^ 40 * 3046921 * 2
def baseEnd_3046921 : Nat := 173837221030886515697219

theorem tailTrace_3046921 : CollatzResearch.WordTrace tailWord_3046921 prefixEnd_3046921 173837221030886515697219 := by
  unfold tailWord_3046921
  simp only [CollatzResearch.WordTrace]
  refine ⟨111130338594533064522924617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74086892396355376348616411 111130338594533064522924617)
  ·
    refine ⟨83347753945899798392193463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111130338594533064522924617 83347753945899798392193463)
    ·
      refine ⟨125021630918849697588290195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83347753945899798392193463 125021630918849697588290195)
      ·
        refine ⟨187532446378274546382435293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125021630918849697588290195 187532446378274546382435293)
        ·
          refine ⟨70324667391852954893413235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 187532446378274546382435293 70324667391852954893413235)
          ·
            refine ⟨105487001087779432340119853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70324667391852954893413235 105487001087779432340119853)
            ·
              refine ⟨39557625407917287127544945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 105487001087779432340119853 39557625407917287127544945)
              ·
                refine ⟨29668219055937965345658709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39557625407917287127544945 29668219055937965345658709)
                ·
                  refine ⟨173837221030886515697219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 29668219055937965345658709 173837221030886515697219)
                  ·
                    rfl

theorem cell23_3046921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 2, 9].length) (baseStart_3046921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3046921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3046921 prefixEnd_3046921 := by exact prefixLift 3046921
  have htrace : WordTrace (prefixWord ++ tailWord_3046921) baseStart_3046921 baseEnd_3046921 := by
    simpa [prefixWord, tailWord_3046921, baseEnd_3046921] using wordTrace_append hprefix tailTrace_3046921
  have hstable : (prefixWord ++ tailWord_3046921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3046921).length < 2 ^ (prefixWord ++ tailWord_3046921).sum := by decide
  have hdescent : baseEnd_3046921 < baseStart_3046921 := by decide
  rcases family_descends (prefixWord ++ tailWord_3046921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3046926 : List Nat := [4, 1, 1, 2, 5, 1, 1, 2, 2, 1, 3]
def baseStart_3046926 : Nat := 118140960795 + 3046926 * 2 ^ 59
def prefixEnd_3046926 : Nat := 4983230072969 + 3 ^ 40 * 3046926 * 2
def baseEnd_3046926 : Nat := 1564537556681251121712449

theorem tailTrace_3046926 : CollatzResearch.WordTrace tailWord_3046926 prefixEnd_3046926 1564537556681251121712449 := by
  unfold tailWord_3046926
  simp only [CollatzResearch.WordTrace]
  refine ⟨13891315119939368797107079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74087013973009966917904421 13891315119939368797107079)
  ·
    refine ⟨20836972679909053195660619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13891315119939368797107079 20836972679909053195660619)
    ·
      refine ⟨31255459019863579793490929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20836972679909053195660619 31255459019863579793490929)
      ·
        refine ⟨23441594264897684845118197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31255459019863579793490929 23441594264897684845118197)
        ·
          refine ⟨2197649462334157954229831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 23441594264897684845118197 2197649462334157954229831)
          ·
            refine ⟨3296474193501236931344747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2197649462334157954229831 3296474193501236931344747)
            ·
              refine ⟨4944711290251855397017121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3296474193501236931344747 4944711290251855397017121)
              ·
                refine ⟨3708533467688891547762841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4944711290251855397017121 3708533467688891547762841)
                ·
                  refine ⟨2781400100766668660822131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3708533467688891547762841 2781400100766668660822131)
                  ·
                    refine ⟨4172100151150002991233197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2781400100766668660822131 4172100151150002991233197)
                    ·
                      refine ⟨1564537556681251121712449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4172100151150002991233197 1564537556681251121712449)
                      ·
                        rfl

theorem cell23_3046926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 1, 1, 2, 2, 1, 3].length) (baseStart_3046926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3046926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3046926 prefixEnd_3046926 := by exact prefixLift 3046926
  have htrace : WordTrace (prefixWord ++ tailWord_3046926) baseStart_3046926 baseEnd_3046926 := by
    simpa [prefixWord, tailWord_3046926, baseEnd_3046926] using wordTrace_append hprefix tailTrace_3046926
  have hstable : (prefixWord ++ tailWord_3046926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3046926).length < 2 ^ (prefixWord ++ tailWord_3046926).sum := by decide
  have hdescent : baseEnd_3046926 < baseStart_3046926 := by decide
  rcases family_descends (prefixWord ++ tailWord_3046926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3046968 : List Nat := [2, 1, 2, 1, 4, 2, 2, 1, 1, 7]
def baseStart_3046968 : Nat := 118140960795 + 3046968 * 2 ^ 59
def prefixEnd_3046968 : Nat := 4983230072969 + 3 ^ 40 * 3046968 * 2
def baseEnd_3046968 : Nat := 521519707622913319129085

theorem tailTrace_3046968 : CollatzResearch.WordTrace tailWord_3046968 prefixEnd_3046968 521519707622913319129085 := by
  unfold tailWord_3046968
  simp only [CollatzResearch.WordTrace]
  refine ⟨55566026412681395774942779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74088035216908527699923705 55566026412681395774942779)
  ·
    refine ⟨83349039619022093662414169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55566026412681395774942779 83349039619022093662414169)
    ·
      refine ⟨62511779714266570246810627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83349039619022093662414169 62511779714266570246810627)
      ·
        refine ⟨93767669571399855370215941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62511779714266570246810627 93767669571399855370215941)
        ·
          refine ⟨17581438044637472881915489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 93767669571399855370215941 17581438044637472881915489)
          ·
            refine ⟨13186078533478104661436617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17581438044637472881915489 13186078533478104661436617)
            ·
              refine ⟨9889558900108578496077463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13186078533478104661436617 9889558900108578496077463)
              ·
                refine ⟨14834338350162867744116195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9889558900108578496077463 14834338350162867744116195)
                ·
                  refine ⟨22251507525244301616174293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14834338350162867744116195 22251507525244301616174293)
                  ·
                    refine ⟨521519707622913319129085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 22251507525244301616174293 521519707622913319129085)
                    ·
                      rfl

theorem cell23_3046968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 1, 1, 7].length) (baseStart_3046968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3046968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3046968 prefixEnd_3046968 := by exact prefixLift 3046968
  have htrace : WordTrace (prefixWord ++ tailWord_3046968) baseStart_3046968 baseEnd_3046968 := by
    simpa [prefixWord, tailWord_3046968, baseEnd_3046968] using wordTrace_append hprefix tailTrace_3046968
  have hstable : (prefixWord ++ tailWord_3046968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3046968).length < 2 ^ (prefixWord ++ tailWord_3046968).sum := by decide
  have hdescent : baseEnd_3046968 < baseStart_3046968 := by decide
  rcases family_descends (prefixWord ++ tailWord_3046968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3046989 : List Nat := [1, 6, 1, 1, 4, 1, 1, 1, 7]
def baseStart_3046989 : Nat := 118140960795 + 3046989 * 2 ^ 59
def prefixEnd_3046989 : Nat := 4983230072969 + 3 ^ 40 * 3046989 * 2
def baseEnd_3046989 : Nat := 173841100662498263913851

theorem tailTrace_3046989 : CollatzResearch.WordTrace tailWord_3046989 prefixEnd_3046989 173841100662498263913851 := by
  unfold tailWord_3046989
  simp only [CollatzResearch.WordTrace]
  refine ⟨111132818758286712136400021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74088545838857808090933347 111132818758286712136400021)
  ·
    refine ⟨5209350879294689631393751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 111132818758286712136400021 5209350879294689631393751)
    ·
      refine ⟨7814026318942034447090627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5209350879294689631393751 7814026318942034447090627)
      ·
        refine ⟨11721039478413051670635941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7814026318942034447090627 11721039478413051670635941)
        ·
          refine ⟨2197694902202447188244239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11721039478413051670635941 2197694902202447188244239)
          ·
            refine ⟨3296542353303670782366359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2197694902202447188244239 3296542353303670782366359)
            ·
              refine ⟨4944813529955506173549539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3296542353303670782366359 4944813529955506173549539)
              ·
                refine ⟨7417220294933259260324309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4944813529955506173549539 7417220294933259260324309)
                ·
                  refine ⟨173841100662498263913851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7417220294933259260324309 173841100662498263913851)
                  ·
                    rfl

theorem cell23_3046989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 1, 1, 1, 7].length) (baseStart_3046989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3046989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3046989 prefixEnd_3046989 := by exact prefixLift 3046989
  have htrace : WordTrace (prefixWord ++ tailWord_3046989) baseStart_3046989 baseEnd_3046989 := by
    simpa [prefixWord, tailWord_3046989, baseEnd_3046989] using wordTrace_append hprefix tailTrace_3046989
  have hstable : (prefixWord ++ tailWord_3046989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3046989).length < 2 ^ (prefixWord ++ tailWord_3046989).sum := by decide
  have hdescent : baseEnd_3046989 < baseStart_3046989 := by decide
  rcases family_descends (prefixWord ++ tailWord_3046989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3047015 : List Nat := [1, 1, 5, 1, 1, 1, 2, 4, 3, 4]
def baseStart_3047015 : Nat := 118140960795 + 3047015 * 2 ^ 59
def prefixEnd_3047015 : Nat := 4983230072969 + 3 ^ 40 * 3047015 * 2
def baseEnd_3047015 : Nat := 521527752153167091166513

theorem tailTrace_3047015 : CollatzResearch.WordTrace tailWord_3047015 prefixEnd_3047015 521527752153167091166513 := by
  unfold tailWord_3047015
  simp only [CollatzResearch.WordTrace]
  refine ⟨111133767056192518576846499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74089178037461679051230999 111133767056192518576846499)
  ·
    refine ⟨166700650584288777865269749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111133767056192518576846499 166700650584288777865269749)
    ·
      refine ⟨15628185992277072924869039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 166700650584288777865269749 15628185992277072924869039)
      ·
        refine ⟨23442278988415609387303559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15628185992277072924869039 23442278988415609387303559)
        ·
          refine ⟨35163418482623414080955339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23442278988415609387303559 35163418482623414080955339)
          ·
            refine ⟨52745127723935121121433009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35163418482623414080955339 52745127723935121121433009)
            ·
              refine ⟨39558845792951340841074757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52745127723935121121433009 39558845792951340841074757)
              ·
                refine ⟨7417283586178376407701517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39558845792951340841074757 7417283586178376407701517)
                ·
                  refine ⟨2781481344816891152888069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7417283586178376407701517 2781481344816891152888069)
                  ·
                    refine ⟨521527752153167091166513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2781481344816891152888069 521527752153167091166513)
                    ·
                      rfl

theorem cell23_3047015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 4, 3, 4].length) (baseStart_3047015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3047015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3047015 prefixEnd_3047015 := by exact prefixLift 3047015
  have htrace : WordTrace (prefixWord ++ tailWord_3047015) baseStart_3047015 baseEnd_3047015 := by
    simpa [prefixWord, tailWord_3047015, baseEnd_3047015] using wordTrace_append hprefix tailTrace_3047015
  have hstable : (prefixWord ++ tailWord_3047015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3047015).length < 2 ^ (prefixWord ++ tailWord_3047015).sum := by decide
  have hdescent : baseEnd_3047015 < baseStart_3047015 := by decide
  rcases family_descends (prefixWord ++ tailWord_3047015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3047045 : List Nat := [1, 3, 1, 1, 4, 1, 4, 2, 6]
def baseStart_3047045 : Nat := 118140960795 + 3047045 * 2 ^ 59
def prefixEnd_3047045 : Nat := 4983230072969 + 3 ^ 40 * 3047045 * 2
def baseEnd_3047045 : Nat := 173844295653237350680489

theorem tailTrace_3047045 : CollatzResearch.WordTrace tailWord_3047045 prefixEnd_3047045 173844295653237350680489 := by
  unfold tailWord_3047045
  simp only [CollatzResearch.WordTrace]
  refine ⟨111134861246083833700438589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74089907497389222466959059 111134861246083833700438589)
  ·
    refine ⟨41675572967281437637664471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111134861246083833700438589 41675572967281437637664471)
    ·
      refine ⟨62513359450922156456496707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41675572967281437637664471 62513359450922156456496707)
      ·
        refine ⟨93770039176383234684745061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62513359450922156456496707 93770039176383234684745061)
        ·
          refine ⟨17581882345571856503389699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 93770039176383234684745061 17581882345571856503389699)
          ·
            refine ⟨26372823518357784755084549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17581882345571856503389699 26372823518357784755084549)
            ·
              refine ⟨4944904409692084641578353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26372823518357784755084549 4944904409692084641578353)
              ·
                refine ⟨3708678307269063481183765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4944904409692084641578353 3708678307269063481183765)
                ·
                  refine ⟨173844295653237350680489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3708678307269063481183765 173844295653237350680489)
                  ·
                    rfl

theorem cell23_3047045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 4, 2, 6].length) (baseStart_3047045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3047045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3047045 prefixEnd_3047045 := by exact prefixLift 3047045
  have htrace : WordTrace (prefixWord ++ tailWord_3047045) baseStart_3047045 baseEnd_3047045 := by
    simpa [prefixWord, tailWord_3047045, baseEnd_3047045] using wordTrace_append hprefix tailTrace_3047045
  have hstable : (prefixWord ++ tailWord_3047045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3047045).length < 2 ^ (prefixWord ++ tailWord_3047045).sum := by decide
  have hdescent : baseEnd_3047045 < baseStart_3047045 := by decide
  rcases family_descends (prefixWord ++ tailWord_3047045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3047049 : List Nat := [1, 2, 1, 1, 4, 1, 6, 2, 1, 4]
def baseStart_3047049 : Nat := 118140960795 + 3047049 * 2 ^ 59
def prefixEnd_3047049 : Nat := 4983230072969 + 3 ^ 40 * 3047049 * 2
def baseEnd_3047049 : Nat := 521533571600584713491461

theorem tailTrace_3047049 : CollatzResearch.WordTrace tailWord_3047049 prefixEnd_3047049 521533571600584713491461 := by
  unfold tailWord_3047049
  simp only [CollatzResearch.WordTrace]
  refine ⟨111135007138069342383584201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74090004758712894922389467 111135007138069342383584201)
  ·
    refine ⟨83351255353552006787688151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111135007138069342383584201 83351255353552006787688151)
    ·
      refine ⟨125026883030328010181532227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83351255353552006787688151 125026883030328010181532227)
      ·
        refine ⟨187540324545492015272298341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125026883030328010181532227 187540324545492015272298341)
        ·
          refine ⟨35163810852279752863555939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 187540324545492015272298341 35163810852279752863555939)
          ·
            refine ⟨52745716278419629295333909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35163810852279752863555939 52745716278419629295333909)
            ·
              refine ⟨2472455450550920123218777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 52745716278419629295333909 2472455450550920123218777)
              ·
                refine ⟨1854341587913190092414083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2472455450550920123218777 1854341587913190092414083)
                ·
                  refine ⟨2781512381869785138621125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1854341587913190092414083 2781512381869785138621125)
                  ·
                    refine ⟨521533571600584713491461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2781512381869785138621125 521533571600584713491461)
                    ·
                      rfl

theorem cell23_3047049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 6, 2, 1, 4].length) (baseStart_3047049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3047049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3047049 prefixEnd_3047049 := by exact prefixLift 3047049
  have htrace : WordTrace (prefixWord ++ tailWord_3047049) baseStart_3047049 baseEnd_3047049 := by
    simpa [prefixWord, tailWord_3047049, baseEnd_3047049] using wordTrace_append hprefix tailTrace_3047049
  have hstable : (prefixWord ++ tailWord_3047049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3047049).length < 2 ^ (prefixWord ++ tailWord_3047049).sum := by decide
  have hdescent : baseEnd_3047049 < baseStart_3047049 := by decide
  rcases family_descends (prefixWord ++ tailWord_3047049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3047072 : List Nat := [2, 1, 1, 4, 3, 1, 1, 1, 5, 1, 3]
def baseStart_3047072 : Nat := 118140960795 + 3047072 * 2 ^ 59
def prefixEnd_3047072 : Nat := 4983230072969 + 3 ^ 40 * 3047072 * 2
def baseEnd_3047072 : Nat := 1564612524856807550486777

theorem tailTrace_3047072 : CollatzResearch.WordTrace tailWord_3047072 prefixEnd_3047072 1564612524856807550486777 := by
  unfold tailWord_3047072
  simp only [CollatzResearch.WordTrace]
  refine ⟨55567923008493008655835735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74090564011324011541114313 55567923008493008655835735)
  ·
    refine ⟨83351884512739512983753603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55567923008493008655835735 83351884512739512983753603)
    ·
      refine ⟨125027826769109269475630405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83351884512739512983753603 125027826769109269475630405)
      ·
        refine ⟨23442717519207988026680701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 125027826769109269475630405 23442717519207988026680701)
        ·
          refine ⟨8791019069702995510005263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23442717519207988026680701 8791019069702995510005263)
          ·
            refine ⟨13186528604554493265007895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8791019069702995510005263 13186528604554493265007895)
            ·
              refine ⟨19779792906831739897511843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13186528604554493265007895 19779792906831739897511843)
              ·
                refine ⟨29669689360247609846267765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19779792906831739897511843 29669689360247609846267765)
                ·
                  refine ⟨2781533377523213423087603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 29669689360247609846267765 2781533377523213423087603)
                  ·
                    refine ⟨4172300066284820134631405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2781533377523213423087603 4172300066284820134631405)
                    ·
                      refine ⟨1564612524856807550486777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4172300066284820134631405 1564612524856807550486777)
                      ·
                        rfl

theorem cell23_3047072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 1, 5, 1, 3].length) (baseStart_3047072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3047072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3047072 prefixEnd_3047072 := by exact prefixLift 3047072
  have htrace : WordTrace (prefixWord ++ tailWord_3047072) baseStart_3047072 baseEnd_3047072 := by
    simpa [prefixWord, tailWord_3047072, baseEnd_3047072] using wordTrace_append hprefix tailTrace_3047072
  have hstable : (prefixWord ++ tailWord_3047072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3047072).length < 2 ^ (prefixWord ++ tailWord_3047072).sum := by decide
  have hdescent : baseEnd_3047072 < baseStart_3047072 := by decide
  rcases family_descends (prefixWord ++ tailWord_3047072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3047075 : List Nat := [1, 1, 1, 4, 1, 1, 4, 4, 1, 5]
def baseStart_3047075 : Nat := 118140960795 + 3047075 * 2 ^ 59
def prefixEnd_3047075 : Nat := 4983230072969 + 3 ^ 40 * 3047075 * 2
def baseEnd_3047075 : Nat := 521538021766257012916421

theorem tailTrace_3047075 : CollatzResearch.WordTrace tailWord_3047075 prefixEnd_3047075 521538021766257012916421 := by
  unfold tailWord_3047075
  simp only [CollatzResearch.WordTrace]
  refine ⟨111135955435975148824030679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74090636957316765882687119 111135955435975148824030679)
  ·
    refine ⟨166703933153962723236046019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111135955435975148824030679 166703933153962723236046019)
    ·
      refine ⟨250055899730944084854069029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166703933153962723236046019 250055899730944084854069029)
      ·
        refine ⟨46885481199552015910137943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 250055899730944084854069029 46885481199552015910137943)
        ·
          refine ⟨70328221799328023865206915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46885481199552015910137943 70328221799328023865206915)
          ·
            refine ⟨105492332698992035797810373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70328221799328023865206915 105492332698992035797810373)
            ·
              refine ⟨19779812381061006712089445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 105492332698992035797810373 19779812381061006712089445)
              ·
                refine ⟨3708714821448938758516771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19779812381061006712089445 3708714821448938758516771)
                ·
                  refine ⟨5563072232173408137775157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3708714821448938758516771 5563072232173408137775157)
                  ·
                    refine ⟨521538021766257012916421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5563072232173408137775157 521538021766257012916421)
                    ·
                      rfl

theorem cell23_3047075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 4, 1, 5].length) (baseStart_3047075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3047075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3047075 prefixEnd_3047075 := by exact prefixLift 3047075
  have htrace : WordTrace (prefixWord ++ tailWord_3047075) baseStart_3047075 baseEnd_3047075 := by
    simpa [prefixWord, tailWord_3047075, baseEnd_3047075] using wordTrace_append hprefix tailTrace_3047075
  have hstable : (prefixWord ++ tailWord_3047075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3047075).length < 2 ^ (prefixWord ++ tailWord_3047075).sum := by decide
  have hdescent : baseEnd_3047075 < baseStart_3047075 := by decide
  rcases family_descends (prefixWord ++ tailWord_3047075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3047115 : List Nat := [1, 1, 1, 1, 3, 2, 1, 3, 5, 2, 3]
def baseStart_3047115 : Nat := 118140960795 + 3047115 * 2 ^ 59
def prefixEnd_3047115 : Nat := 4983230072969 + 3 ^ 40 * 3047115 * 2
def baseEnd_3047115 : Nat := 1564634604524950882249079

theorem tailTrace_3047115 : CollatzResearch.WordTrace tailWord_3047115 prefixEnd_3047115 1564634604524950882249079 := by
  unfold tailWord_3047115
  simp only [CollatzResearch.WordTrace]
  refine ⟨111137414355830235655486799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74091609570553490436991199 111137414355830235655486799)
  ·
    refine ⟨166706121533745353483230199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111137414355830235655486799 166706121533745353483230199)
    ·
      refine ⟨250059182300618030224845299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166706121533745353483230199 250059182300618030224845299)
      ·
        refine ⟨375088773450927045337267949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 250059182300618030224845299 375088773450927045337267949)
        ·
          refine ⟨140658290044097642001475481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 375088773450927045337267949 140658290044097642001475481)
          ·
            refine ⟨105493717533073231501106611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 140658290044097642001475481 105493717533073231501106611)
            ·
              refine ⟨158240576299609847251659917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105493717533073231501106611 158240576299609847251659917)
              ·
                refine ⟨59340216112353692719372469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 158240576299609847251659917 59340216112353692719372469)
                ·
                  refine ⟨5563145260533158692441169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 59340216112353692719372469 5563145260533158692441169)
                  ·
                    refine ⟨4172358945399869019330877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5563145260533158692441169 4172358945399869019330877)
                    ·
                      refine ⟨1564634604524950882249079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4172358945399869019330877 1564634604524950882249079)
                      ·
                        rfl

theorem cell23_3047115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 3, 5, 2, 3].length) (baseStart_3047115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3047115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3047115 prefixEnd_3047115 := by exact prefixLift 3047115
  have htrace : WordTrace (prefixWord ++ tailWord_3047115) baseStart_3047115 baseEnd_3047115 := by
    simpa [prefixWord, tailWord_3047115, baseEnd_3047115] using wordTrace_append hprefix tailTrace_3047115
  have hstable : (prefixWord ++ tailWord_3047115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3047115).length < 2 ^ (prefixWord ++ tailWord_3047115).sum := by decide
  have hdescent : baseEnd_3047115 < baseStart_3047115 := by decide
  rcases family_descends (prefixWord ++ tailWord_3047115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3047122 : List Nat := [3, 2, 2, 2, 2, 1, 3, 1, 1, 6]
def baseStart_3047122 : Nat := 118140960795 + 3047122 * 2 ^ 59
def prefixEnd_3047122 : Nat := 4983230072969 + 3 ^ 40 * 3047122 * 2
def baseEnd_3047122 : Nat := 521546066296510784953849

theorem tailTrace_3047122 : CollatzResearch.WordTrace tailWord_3047122 prefixEnd_3047122 521546066296510784953849 := by
  unfold tailWord_3047122
  simp only [CollatzResearch.WordTrace]
  refine ⟨27784417416701218962747905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74091779777869917233994413 27784417416701218962747905)
  ·
    refine ⟨20838313062525914222060929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27784417416701218962747905 20838313062525914222060929)
    ·
      refine ⟨15628734796894435666545697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20838313062525914222060929 15628734796894435666545697)
      ·
        refine ⟨11721551097670826749909273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15628734796894435666545697 11721551097670826749909273)
        ·
          refine ⟨8791163323253120062431955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11721551097670826749909273 8791163323253120062431955)
          ·
            refine ⟨13186744984879680093647933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8791163323253120062431955 13186744984879680093647933)
            ·
              refine ⟨4945029369329880035117975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13186744984879680093647933 4945029369329880035117975)
              ·
                refine ⟨7417544053994820052676963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4945029369329880035117975 7417544053994820052676963)
                ·
                  refine ⟨11126316080992230079015445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7417544053994820052676963 11126316080992230079015445)
                  ·
                    refine ⟨521546066296510784953849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11126316080992230079015445 521546066296510784953849)
                    ·
                      rfl

theorem cell23_3047122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 3, 1, 1, 6].length) (baseStart_3047122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3047122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3047122 prefixEnd_3047122 := by exact prefixLift 3047122
  have htrace : WordTrace (prefixWord ++ tailWord_3047122) baseStart_3047122 baseEnd_3047122 := by
    simpa [prefixWord, tailWord_3047122, baseEnd_3047122] using wordTrace_append hprefix tailTrace_3047122
  have hstable : (prefixWord ++ tailWord_3047122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3047122).length < 2 ^ (prefixWord ++ tailWord_3047122).sum := by decide
  have hdescent : baseEnd_3047122 < baseStart_3047122 := by decide
  rcases family_descends (prefixWord ++ tailWord_3047122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3047129 : List Nat := [1, 2, 1, 2, 3, 3, 2, 2, 3, 2, 2]
def baseStart_3047129 : Nat := 118140960795 + 3047129 * 2 ^ 59
def prefixEnd_3047129 : Nat := 4983230072969 + 3 ^ 40 * 3047129 * 2
def baseEnd_3047129 : Nat := 1564641793254113827474015

theorem tailTrace_3047129 : CollatzResearch.WordTrace tailWord_3047129 prefixEnd_3047129 1564641793254113827474015 := by
  unfold tailWord_3047129
  simp only [CollatzResearch.WordTrace]
  refine ⟨111137924977779516046496441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74091949985186344030997627 111137924977779516046496441)
  ·
    refine ⟨83353443733334637034872331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111137924977779516046496441 83353443733334637034872331)
    ·
      refine ⟨125030165600001955552308497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83353443733334637034872331 125030165600001955552308497)
      ·
        refine ⟨93772624200001466664231373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125030165600001955552308497 93772624200001466664231373)
        ·
          refine ⟨35164734075000549999086765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 93772624200001466664231373 35164734075000549999086765)
          ·
            refine ⟨13186775278125206249657537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35164734075000549999086765 13186775278125206249657537)
            ·
              refine ⟨9890081458593904687243153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13186775278125206249657537 9890081458593904687243153)
              ·
                refine ⟨7417561093945428515432365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9890081458593904687243153 7417561093945428515432365)
                ·
                  refine ⟨2781585410229535693287137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7417561093945428515432365 2781585410229535693287137)
                  ·
                    refine ⟨2086189057672151769965353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2781585410229535693287137 2086189057672151769965353)
                    ·
                      refine ⟨1564641793254113827474015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2086189057672151769965353 1564641793254113827474015)
                      ·
                        rfl

theorem cell23_3047129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 2, 2, 3, 2, 2].length) (baseStart_3047129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3047129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3047129 prefixEnd_3047129 := by exact prefixLift 3047129
  have htrace : WordTrace (prefixWord ++ tailWord_3047129) baseStart_3047129 baseEnd_3047129 := by
    simpa [prefixWord, tailWord_3047129, baseEnd_3047129] using wordTrace_append hprefix tailTrace_3047129
  have hstable : (prefixWord ++ tailWord_3047129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3047129).length < 2 ^ (prefixWord ++ tailWord_3047129).sum := by decide
  have hdescent : baseEnd_3047129 < baseStart_3047129 := by decide
  rcases family_descends (prefixWord ++ tailWord_3047129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3047145 : List Nat := [1, 2, 1, 1, 1, 2, 3, 3, 3, 3, 3]
def baseStart_3047145 : Nat := 118140960795 + 3047145 * 2 ^ 59
def prefixEnd_3047145 : Nat := 4983230072969 + 3 ^ 40 * 3047145 * 2
def baseEnd_3047145 : Nat := 1564650008944585764873941

theorem tailTrace_3047145 : CollatzResearch.WordTrace tailWord_3047145 prefixEnd_3047145 1564650008944585764873941 := by
  unfold tailWord_3047145
  simp only [CollatzResearch.WordTrace]
  refine ⟨111138508545721550779078889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74092339030481033852719259 111138508545721550779078889)
  ·
    refine ⟨83353881409291163084309167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111138508545721550779078889 83353881409291163084309167)
    ·
      refine ⟨125030822113936744626463751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83353881409291163084309167 125030822113936744626463751)
      ·
        refine ⟨187546233170905116939695627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125030822113936744626463751 187546233170905116939695627)
        ·
          refine ⟨281319349756357675409543441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 187546233170905116939695627 281319349756357675409543441)
          ·
            refine ⟨210989512317268256557157581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 281319349756357675409543441 210989512317268256557157581)
            ·
              refine ⟨79121067118975596208934093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 210989512317268256557157581 79121067118975596208934093)
              ·
                refine ⟨29670400169615848578350285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 79121067118975596208934093 29670400169615848578350285)
                ·
                  refine ⟨11126400063605943216881357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29670400169615848578350285 11126400063605943216881357)
                  ·
                    refine ⟨4172400023852228706330509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11126400063605943216881357 4172400023852228706330509)
                    ·
                      refine ⟨1564650008944585764873941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4172400023852228706330509 1564650008944585764873941)
                      ·
                        rfl

theorem cell23_3047145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 3, 3, 3, 3].length) (baseStart_3047145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3047145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3047145 prefixEnd_3047145 := by exact prefixLift 3047145
  have htrace : WordTrace (prefixWord ++ tailWord_3047145) baseStart_3047145 baseEnd_3047145 := by
    simpa [prefixWord, tailWord_3047145, baseEnd_3047145] using wordTrace_append hprefix tailTrace_3047145
  have hstable : (prefixWord ++ tailWord_3047145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3047145).length < 2 ^ (prefixWord ++ tailWord_3047145).sum := by decide
  have hdescent : baseEnd_3047145 < baseStart_3047145 := by decide
  rcases family_descends (prefixWord ++ tailWord_3047145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3047149 : List Nat := [1, 5, 1, 2, 1, 2, 2, 3, 1, 2, 3]
def baseStart_3047149 : Nat := 118140960795 + 3047149 * 2 ^ 59
def prefixEnd_3047149 : Nat := 4983230072969 + 3 ^ 40 * 3047149 * 2
def baseEnd_3047149 : Nat := 1564652062867203749223923

theorem tailTrace_3047149 : CollatzResearch.WordTrace tailWord_3047149 prefixEnd_3047149 1564652062867203749223923 := by
  unfold tailWord_3047149
  simp only [CollatzResearch.WordTrace]
  refine ⟨111138654437707059462224501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74092436291804706308149667 111138654437707059462224501)
  ·
    refine ⟨10419248853535036824583547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 111138654437707059462224501 10419248853535036824583547)
    ·
      refine ⟨15628873280302555236875321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10419248853535036824583547 15628873280302555236875321)
      ·
        refine ⟨11721654960226916427656491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15628873280302555236875321 11721654960226916427656491)
        ·
          refine ⟨17582482440340374641484737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11721654960226916427656491 17582482440340374641484737)
          ·
            refine ⟨13186861830255280981113553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17582482440340374641484737 13186861830255280981113553)
            ·
              refine ⟨9890146372691460735835165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13186861830255280981113553 9890146372691460735835165)
              ·
                refine ⟨3708804889759297775938187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9890146372691460735835165 3708804889759297775938187)
                ·
                  refine ⟨5563207334638946663907281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3708804889759297775938187 5563207334638946663907281)
                  ·
                    refine ⟨4172405500979209997930461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5563207334638946663907281 4172405500979209997930461)
                    ·
                      refine ⟨1564652062867203749223923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4172405500979209997930461 1564652062867203749223923)
                      ·
                        rfl

theorem cell23_3047149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 2, 3, 1, 2, 3].length) (baseStart_3047149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3047149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3047149 prefixEnd_3047149 := by exact prefixLift 3047149
  have htrace : WordTrace (prefixWord ++ tailWord_3047149) baseStart_3047149 baseEnd_3047149 := by
    simpa [prefixWord, tailWord_3047149, baseEnd_3047149] using wordTrace_append hprefix tailTrace_3047149
  have hstable : (prefixWord ++ tailWord_3047149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3047149).length < 2 ^ (prefixWord ++ tailWord_3047149).sum := by decide
  have hdescent : baseEnd_3047149 < baseStart_3047149 := by decide
  rcases family_descends (prefixWord ++ tailWord_3047149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3047156 : List Nat := [2, 6, 1, 1, 1, 1, 2, 1, 4, 4]
def baseStart_3047156 : Nat := 118140960795 + 3047156 * 2 ^ 59
def prefixEnd_3047156 : Nat := 4983230072969 + 3 ^ 40 * 3047156 * 2
def baseEnd_3047156 : Nat := 521551885743928407278797

theorem tailTrace_3047156 : CollatzResearch.WordTrace tailWord_3047156 prefixEnd_3047156 521551885743928407278797 := by
  unfold tailWord_3047156
  simp only [CollatzResearch.WordTrace]
  refine ⟨55569454874340849828864661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74092606499121133105152881 55569454874340849828864661)
  ·
    refine ⟨2604818197234727335728031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 55569454874340849828864661 2604818197234727335728031)
    ·
      refine ⟨3907227295852091003592047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2604818197234727335728031 3907227295852091003592047)
      ·
        refine ⟨5860840943778136505388071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3907227295852091003592047 5860840943778136505388071)
        ·
          refine ⟨8791261415667204758082107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5860840943778136505388071 8791261415667204758082107)
          ·
            refine ⟨13186892123500807137123161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8791261415667204758082107 13186892123500807137123161)
            ·
              refine ⟨9890169092625605352842371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13186892123500807137123161 9890169092625605352842371)
              ·
                refine ⟨14835253638938408029263557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9890169092625605352842371 14835253638938408029263557)
                ·
                  refine ⟨2781610057300951505486917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14835253638938408029263557 2781610057300951505486917)
                  ·
                    refine ⟨521551885743928407278797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2781610057300951505486917 521551885743928407278797)
                    ·
                      rfl

theorem cell23_3047156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 2, 1, 4, 4].length) (baseStart_3047156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3047156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3047156 prefixEnd_3047156 := by exact prefixLift 3047156
  have htrace : WordTrace (prefixWord ++ tailWord_3047156) baseStart_3047156 baseEnd_3047156 := by
    simpa [prefixWord, tailWord_3047156, baseEnd_3047156] using wordTrace_append hprefix tailTrace_3047156
  have hstable : (prefixWord ++ tailWord_3047156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3047156).length < 2 ^ (prefixWord ++ tailWord_3047156).sum := by decide
  have hdescent : baseEnd_3047156 < baseStart_3047156 := by decide
  rcases family_descends (prefixWord ++ tailWord_3047156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3047189 : List Nat := [1, 3, 2, 1, 2, 4, 1, 1, 3, 3, 2]
def baseStart_3047189 : Nat := 118140960795 + 3047189 * 2 ^ 59
def prefixEnd_3047189 : Nat := 4983230072969 + 3 ^ 40 * 3047189 * 2
def baseEnd_3047189 : Nat := 1564672602093383592723739

theorem tailTrace_3047189 : CollatzResearch.WordTrace tailWord_3047189 prefixEnd_3047189 1564672602093383592723739 := by
  unfold tailWord_3047189
  simp only [CollatzResearch.WordTrace]
  refine ⟨111140113357562146293680621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74093408905041430862453747 111140113357562146293680621)
  ·
    refine ⟨41677542509085804860130233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111140113357562146293680621 41677542509085804860130233)
    ·
      refine ⟨31258156881814353645097675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41677542509085804860130233 31258156881814353645097675)
      ·
        refine ⟨46887235322721530467646513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31258156881814353645097675 46887235322721530467646513)
        ·
          refine ⟨35165426492041147850734885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46887235322721530467646513 35165426492041147850734885)
          ·
            refine ⟨6593517467257715222012791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35165426492041147850734885 6593517467257715222012791)
            ·
              refine ⟨9890276200886572833019187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6593517467257715222012791 9890276200886572833019187)
              ·
                refine ⟨14835414301329859249528781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9890276200886572833019187 14835414301329859249528781)
                ·
                  refine ⟨5563280362998697218573293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14835414301329859249528781 5563280362998697218573293)
                  ·
                    refine ⟨2086230136124511456964985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5563280362998697218573293 2086230136124511456964985)
                    ·
                      refine ⟨1564672602093383592723739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2086230136124511456964985 1564672602093383592723739)
                      ·
                        rfl

theorem cell23_3047189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 1, 1, 3, 3, 2].length) (baseStart_3047189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3047189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3047189 prefixEnd_3047189 := by exact prefixLift 3047189
  have htrace : WordTrace (prefixWord ++ tailWord_3047189) baseStart_3047189 baseEnd_3047189 := by
    simpa [prefixWord, tailWord_3047189, baseEnd_3047189] using wordTrace_append hprefix tailTrace_3047189
  have hstable : (prefixWord ++ tailWord_3047189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3047189).length < 2 ^ (prefixWord ++ tailWord_3047189).sum := by decide
  have hdescent : baseEnd_3047189 < baseStart_3047189 := by decide
  rcases family_descends (prefixWord ++ tailWord_3047189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3047214 : List Nat := [4, 1, 3, 2, 3, 1, 2, 2, 1, 2, 2]
def baseStart_3047214 : Nat := 118140960795 + 3047214 * 2 ^ 59
def prefixEnd_3047214 : Nat := 4983230072969 + 3 ^ 40 * 3047214 * 2
def baseEnd_3047214 : Nat := 1564685439109745994911125

theorem tailTrace_3047214 : CollatzResearch.WordTrace tailWord_3047214 prefixEnd_3047214 1564685439109745994911125 := by
  unfold tailWord_3047214
  simp only [CollatzResearch.WordTrace]
  refine ⟨13892628147808946945417587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74094016788314383708893797 13892628147808946945417587)
  ·
    refine ⟨20838942221713420418126381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13892628147808946945417587 20838942221713420418126381)
    ·
      refine ⟨7814603333142532656797393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20838942221713420418126381 7814603333142532656797393)
      ·
        refine ⟨5860952499856899492598045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7814603333142532656797393 5860952499856899492598045)
        ·
          refine ⟨2197857187446337309724267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5860952499856899492598045 2197857187446337309724267)
          ·
            refine ⟨3296785781169505964586401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2197857187446337309724267 3296785781169505964586401)
            ·
              refine ⟨2472589335877129473439801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3296785781169505964586401 2472589335877129473439801)
              ·
                refine ⟨1854442001907847105079851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2472589335877129473439801 1854442001907847105079851)
                ·
                  refine ⟨2781663002861770657619777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1854442001907847105079851 2781663002861770657619777)
                  ·
                    refine ⟨2086247252146327993214833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2781663002861770657619777 2086247252146327993214833)
                    ·
                      refine ⟨1564685439109745994911125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2086247252146327993214833 1564685439109745994911125)
                      ·
                        rfl

theorem cell23_3047214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 1, 2, 2, 1, 2, 2].length) (baseStart_3047214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3047214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3047214 prefixEnd_3047214 := by exact prefixLift 3047214
  have htrace : WordTrace (prefixWord ++ tailWord_3047214) baseStart_3047214 baseEnd_3047214 := by
    simpa [prefixWord, tailWord_3047214, baseEnd_3047214] using wordTrace_append hprefix tailTrace_3047214
  have hstable : (prefixWord ++ tailWord_3047214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3047214).length < 2 ^ (prefixWord ++ tailWord_3047214).sum := by decide
  have hdescent : baseEnd_3047214 < baseStart_3047214 := by decide
  rcases family_descends (prefixWord ++ tailWord_3047214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3047215 : List Nat := [1, 1, 2, 1, 2, 1, 2, 3, 4, 2, 4]
def baseStart_3047215 : Nat := 118140960795 + 3047215 * 2 ^ 59
def prefixEnd_3047215 : Nat := 4983230072969 + 3 ^ 40 * 3047215 * 2
def baseEnd_3047215 : Nat := 1564685952590400490998619

theorem tailTrace_3047215 : CollatzResearch.WordTrace tailWord_3047215 prefixEnd_3047215 1564685952590400490998619 := by
  unfold tailWord_3047215
  simp only [CollatzResearch.WordTrace]
  refine ⟨111141061655467952734127099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74094041103645301822751399 111141061655467952734127099)
  ·
    refine ⟨166711592483201929101190649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111141061655467952734127099 166711592483201929101190649)
    ·
      refine ⟨125033694362401446825892987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166711592483201929101190649 125033694362401446825892987)
      ·
        refine ⟨187550541543602170238839481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125033694362401446825892987 187550541543602170238839481)
        ·
          refine ⟨140662906157701627679129611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 187550541543602170238839481 140662906157701627679129611)
          ·
            refine ⟨210994359236552441518694417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140662906157701627679129611 210994359236552441518694417)
            ·
              refine ⟨158245769427414331139020813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 210994359236552441518694417 158245769427414331139020813)
              ·
                refine ⟨59342163535280374177132805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 158245769427414331139020813 59342163535280374177132805)
                ·
                  refine ⟨11126655662865070158212401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 59342163535280374177132805 11126655662865070158212401)
                  ·
                    refine ⟨8344991747148802618659301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11126655662865070158212401 8344991747148802618659301)
                    ·
                      refine ⟨1564685952590400490998619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8344991747148802618659301 1564685952590400490998619)
                      ·
                        rfl

theorem cell23_3047215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 3, 4, 2, 4].length) (baseStart_3047215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3047215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3047215 prefixEnd_3047215 := by exact prefixLift 3047215
  have htrace : WordTrace (prefixWord ++ tailWord_3047215) baseStart_3047215 baseEnd_3047215 := by
    simpa [prefixWord, tailWord_3047215, baseEnd_3047215] using wordTrace_append hprefix tailTrace_3047215
  have hstable : (prefixWord ++ tailWord_3047215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3047215).length < 2 ^ (prefixWord ++ tailWord_3047215).sum := by decide
  have hdescent : baseEnd_3047215 < baseStart_3047215 := by decide
  rcases family_descends (prefixWord ++ tailWord_3047215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3047272 : List Nat := [2, 1, 4, 2, 1, 1, 2, 1, 4, 5]
def baseStart_3047272 : Nat := 118140960795 + 3047272 * 2 ^ 59
def prefixEnd_3047272 : Nat := 4983230072969 + 3 ^ 40 * 3047272 * 2
def baseEnd_3047272 : Nat := 521571740329235589328619

theorem tailTrace_3047272 : CollatzResearch.WordTrace tailWord_3047272 prefixEnd_3047272 521571740329235589328619 := by
  unfold tailWord_3047272
  simp only [CollatzResearch.WordTrace]
  refine ⟨55571570308130725734476035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74095427077507634312634713 55571570308130725734476035)
  ·
    refine ⟨83357355462196088601714053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55571570308130725734476035 83357355462196088601714053)
    ·
      refine ⟨15629504149161766612821385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 83357355462196088601714053 15629504149161766612821385)
      ·
        refine ⟨11722128111871324959616039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15629504149161766612821385 11722128111871324959616039)
        ·
          refine ⟨17583192167806987439424059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11722128111871324959616039 17583192167806987439424059)
          ·
            refine ⟨26374788251710481159136089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17583192167806987439424059 26374788251710481159136089)
            ·
              refine ⟨19781091188782860869352067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26374788251710481159136089 19781091188782860869352067)
              ·
                refine ⟨29671636783174291304028101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19781091188782860869352067 29671636783174291304028101)
                ·
                  refine ⟨5563431896845179619505269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29671636783174291304028101 5563431896845179619505269)
                  ·
                    refine ⟨521571740329235589328619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5563431896845179619505269 521571740329235589328619)
                    ·
                      rfl

theorem cell23_3047272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 1, 4, 5].length) (baseStart_3047272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3047272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3047272 prefixEnd_3047272 := by exact prefixLift 3047272
  have htrace : WordTrace (prefixWord ++ tailWord_3047272) baseStart_3047272 baseEnd_3047272 := by
    simpa [prefixWord, tailWord_3047272, baseEnd_3047272] using wordTrace_append hprefix tailTrace_3047272
  have hstable : (prefixWord ++ tailWord_3047272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3047272).length < 2 ^ (prefixWord ++ tailWord_3047272).sum := by decide
  have hdescent : baseEnd_3047272 < baseStart_3047272 := by decide
  rcases family_descends (prefixWord ++ tailWord_3047272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3047310 : List Nat := [4, 1, 1, 5, 2, 1, 1, 3, 5]
def baseStart_3047310 : Nat := 118140960795 + 3047310 * 2 ^ 59
def prefixEnd_3047310 : Nat := 4983230072969 + 3 ^ 40 * 3047310 * 2
def baseEnd_3047310 : Nat := 173859414805841957701187

theorem tailTrace_3047310 : CollatzResearch.WordTrace tailWord_3047310 prefixEnd_3047310 173859414805841957701187 := by
  unfold tailWord_3047310
  simp only [CollatzResearch.WordTrace]
  refine ⟨13893065823765472994854423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74096351060082522639223589 13893065823765472994854423)
  ·
    refine ⟨20839598735648209492281635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13893065823765472994854423 20839598735648209492281635)
    ·
      refine ⟨31259398103472314238422453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20839598735648209492281635 31259398103472314238422453)
      ·
        refine ⟨2930568572200529459852105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 31259398103472314238422453 2930568572200529459852105)
        ·
          refine ⟨2197926429150397094889079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2930568572200529459852105 2197926429150397094889079)
          ·
            refine ⟨3296889643725595642333619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2197926429150397094889079 3296889643725595642333619)
            ·
              refine ⟨4945334465588393463500429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3296889643725595642333619 4945334465588393463500429)
              ·
                refine ⟨1854500424595647548812661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4945334465588393463500429 1854500424595647548812661)
                ·
                  refine ⟨173859414805841957701187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1854500424595647548812661 173859414805841957701187)
                  ·
                    rfl

theorem cell23_3047310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 1, 1, 3, 5].length) (baseStart_3047310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3047310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3047310 prefixEnd_3047310 := by exact prefixLift 3047310
  have htrace : WordTrace (prefixWord ++ tailWord_3047310) baseStart_3047310 baseEnd_3047310 := by
    simpa [prefixWord, tailWord_3047310, baseEnd_3047310] using wordTrace_append hprefix tailTrace_3047310
  have hstable : (prefixWord ++ tailWord_3047310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3047310).length < 2 ^ (prefixWord ++ tailWord_3047310).sum := by decide
  have hdescent : baseEnd_3047310 < baseStart_3047310 := by decide
  rcases family_descends (prefixWord ++ tailWord_3047310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3047332 : List Nat := [2, 3, 1, 2, 1, 3, 2, 1, 8]
def baseStart_3047332 : Nat := 118140960795 + 3047332 * 2 ^ 59
def prefixEnd_3047332 : Nat := 4983230072969 + 3 ^ 40 * 3047332 * 2
def baseEnd_3047332 : Nat := 173860669980775170359509

theorem tailTrace_3047332 : CollatzResearch.WordTrace tailWord_3047332 prefixEnd_3047332 173860669980775170359509 := by
  unfold tailWord_3047332
  simp only [CollatzResearch.WordTrace]
  refine ⟨55572664498022040858068125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74096885997362721144090833 55572664498022040858068125)
  ·
    refine ⟨20839749186758265321775547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55572664498022040858068125 20839749186758265321775547)
    ·
      refine ⟨31259623780137397982663321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20839749186758265321775547 31259623780137397982663321)
      ·
        refine ⟨23444717835103048486997491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31259623780137397982663321 23444717835103048486997491)
        ·
          refine ⟨35167076752654572730496237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23444717835103048486997491 35167076752654572730496237)
          ·
            refine ⟨13187653782245464773936089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35167076752654572730496237 13187653782245464773936089)
            ·
              refine ⟨9890740336684098580452067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13187653782245464773936089 9890740336684098580452067)
              ·
                refine ⟨14836110505026147870678101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9890740336684098580452067 14836110505026147870678101)
                ·
                  refine ⟨173860669980775170359509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 14836110505026147870678101 173860669980775170359509)
                  ·
                    rfl

theorem cell23_3047332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 2, 1, 8].length) (baseStart_3047332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3047332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3047332 prefixEnd_3047332 := by exact prefixLift 3047332
  have htrace : WordTrace (prefixWord ++ tailWord_3047332) baseStart_3047332 baseEnd_3047332 := by
    simpa [prefixWord, tailWord_3047332, baseEnd_3047332] using wordTrace_append hprefix tailTrace_3047332
  have hstable : (prefixWord ++ tailWord_3047332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3047332).length < 2 ^ (prefixWord ++ tailWord_3047332).sum := by decide
  have hdescent : baseEnd_3047332 < baseStart_3047332 := by decide
  rcases family_descends (prefixWord ++ tailWord_3047332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3047349 : List Nat := [1, 3, 3, 2, 1, 3, 1, 3, 6]
def baseStart_3047349 : Nat := 118140960795 + 3047349 * 2 ^ 59
def prefixEnd_3047349 : Nat := 4983230072969 + 3 ^ 40 * 3047349 * 2
def baseEnd_3047349 : Nat := 173861639888678107413667

theorem tailTrace_3047349 : CollatzResearch.WordTrace tailWord_3047349 prefixEnd_3047349 173861639888678107413667 := by
  unfold tailWord_3047349
  simp only [CollatzResearch.WordTrace]
  refine ⟨111145949036982493619505101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74097299357988329079670067 111145949036982493619505101)
  ·
    refine ⟨41679730888868435107314413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111145949036982493619505101 41679730888868435107314413)
    ·
      refine ⟨15629899083325663165242905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41679730888868435107314413 15629899083325663165242905)
      ·
        refine ⟨11722424312494247373932179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15629899083325663165242905 11722424312494247373932179)
        ·
          refine ⟨17583636468741371060898269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11722424312494247373932179 17583636468741371060898269)
          ·
            refine ⟨6593863675778014147836851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17583636468741371060898269 6593863675778014147836851)
            ·
              refine ⟨9890795513667021221755277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6593863675778014147836851 9890795513667021221755277)
              ·
                refine ⟨3709048317625132958158229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9890795513667021221755277 3709048317625132958158229)
                ·
                  refine ⟨173861639888678107413667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3709048317625132958158229 173861639888678107413667)
                  ·
                    rfl

theorem cell23_3047349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 1, 3, 6].length) (baseStart_3047349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3047349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3047349 prefixEnd_3047349 := by exact prefixLift 3047349
  have htrace : WordTrace (prefixWord ++ tailWord_3047349) baseStart_3047349 baseEnd_3047349 := by
    simpa [prefixWord, tailWord_3047349, baseEnd_3047349] using wordTrace_append hprefix tailTrace_3047349
  have hstable : (prefixWord ++ tailWord_3047349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3047349).length < 2 ^ (prefixWord ++ tailWord_3047349).sum := by decide
  have hdescent : baseEnd_3047349 < baseStart_3047349 := by decide
  rcases family_descends (prefixWord ++ tailWord_3047349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3047359 : List Nat := [1, 1, 2, 2, 2, 1, 4, 1, 5, 1, 3]
def baseStart_3047359 : Nat := 118140960795 + 3047359 * 2 ^ 59
def prefixEnd_3047359 : Nat := 4983230072969 + 3 ^ 40 * 3047359 * 2
def baseEnd_3047359 : Nat := 1564759893804647927597957

theorem tailTrace_3047359 : CollatzResearch.WordTrace tailWord_3047359 prefixEnd_3047359 1564759893804647927597957 := by
  unfold tailWord_3047359
  simp only [CollatzResearch.WordTrace]
  refine ⟨111146313766946265327369131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74097542511297510218246087 111146313766946265327369131)
  ·
    refine ⟨166719470650419397991053697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111146313766946265327369131 166719470650419397991053697)
    ·
      refine ⟨125039602987814548493290273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166719470650419397991053697 125039602987814548493290273)
      ·
        refine ⟨93779702240860911369967705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125039602987814548493290273 93779702240860911369967705)
        ·
          refine ⟨70334776680645683527475779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93779702240860911369967705 70334776680645683527475779)
          ·
            refine ⟨105502165020968525291213669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70334776680645683527475779 105502165020968525291213669)
            ·
              refine ⟨19781655941431598492102563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 105502165020968525291213669 19781655941431598492102563)
              ·
                refine ⟨29672483912147397738153845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19781655941431598492102563 29672483912147397738153845)
                ·
                  refine ⟨2781795366763818537951923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 29672483912147397738153845 2781795366763818537951923)
                  ·
                    refine ⟨4172693050145727806927885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2781795366763818537951923 4172693050145727806927885)
                    ·
                      refine ⟨1564759893804647927597957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4172693050145727806927885 1564759893804647927597957)
                      ·
                        rfl

theorem cell23_3047359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 1, 5, 1, 3].length) (baseStart_3047359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3047359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3047359 prefixEnd_3047359 := by exact prefixLift 3047359
  have htrace : WordTrace (prefixWord ++ tailWord_3047359) baseStart_3047359 baseEnd_3047359 := by
    simpa [prefixWord, tailWord_3047359, baseEnd_3047359] using wordTrace_append hprefix tailTrace_3047359
  have hstable : (prefixWord ++ tailWord_3047359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3047359).length < 2 ^ (prefixWord ++ tailWord_3047359).sum := by decide
  have hdescent : baseEnd_3047359 < baseStart_3047359 := by decide
  rcases family_descends (prefixWord ++ tailWord_3047359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3047369 : List Nat := [1, 2, 1, 1, 2, 1, 2, 2, 6, 3, 2]
def baseStart_3047369 : Nat := 118140960795 + 3047369 * 2 ^ 59
def prefixEnd_3047369 : Nat := 4983230072969 + 3 ^ 40 * 3047369 * 2
def baseEnd_3047369 : Nat := 1564765028611192888472911

theorem tailTrace_3047369 : CollatzResearch.WordTrace tailWord_3047369 prefixEnd_3047369 1564765028611192888472911 := by
  unfold tailWord_3047369
  simp only [CollatzResearch.WordTrace]
  refine ⟨111146678496910037035233161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74097785664606691356822107 111146678496910037035233161)
  ·
    refine ⟨83360008872682527776424871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111146678496910037035233161 83360008872682527776424871)
    ·
      refine ⟨125040013309023791664637307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83360008872682527776424871 125040013309023791664637307)
      ·
        refine ⟨187560019963535687496955961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125040013309023791664637307 187560019963535687496955961)
        ·
          refine ⟨140670014972651765622716971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 187560019963535687496955961 140670014972651765622716971)
          ·
            refine ⟨211005022458977648434075457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140670014972651765622716971 211005022458977648434075457)
            ·
              refine ⟨158253766844233236325556593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 211005022458977648434075457 158253766844233236325556593)
              ·
                refine ⟨118690325133174927244167445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 158253766844233236325556593 118690325133174927244167445)
                ·
                  refine ⟨5563608990617574714570349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 118690325133174927244167445 5563608990617574714570349)
                  ·
                    refine ⟨2086353371481590517963881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5563608990617574714570349 2086353371481590517963881)
                    ·
                      refine ⟨1564765028611192888472911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2086353371481590517963881 1564765028611192888472911)
                      ·
                        rfl

theorem cell23_3047369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 2, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 2, 6, 3, 2].length) (baseStart_3047369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3047369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3047369 prefixEnd_3047369 := by exact prefixLift 3047369
  have htrace : WordTrace (prefixWord ++ tailWord_3047369) baseStart_3047369 baseEnd_3047369 := by
    simpa [prefixWord, tailWord_3047369, baseEnd_3047369] using wordTrace_append hprefix tailTrace_3047369
  have hstable : (prefixWord ++ tailWord_3047369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3047369).length < 2 ^ (prefixWord ++ tailWord_3047369).sum := by decide
  have hdescent : baseEnd_3047369 < baseStart_3047369 := by decide
  rcases family_descends (prefixWord ++ tailWord_3047369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3047416 : List Nat := [2, 1, 2, 1, 1, 3, 3, 1, 5, 2, 2]
def baseStart_3047416 : Nat := 118140960795 + 3047416 * 2 ^ 59
def prefixEnd_3047416 : Nat := 4983230072969 + 3 ^ 40 * 3047416 * 2
def baseEnd_3047416 : Nat := 1564789162201954204585195

theorem tailTrace_3047416 : CollatzResearch.WordTrace tailWord_3047416 prefixEnd_3047416 1564789162201954204585195 := by
  unfold tailWord_3047416
  simp only [CollatzResearch.WordTrace]
  refine ⟨55574196363869882031097051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74098928485159842708129401 55574196363869882031097051)
  ·
    refine ⟨83361294545804823046645577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55574196363869882031097051 83361294545804823046645577)
    ·
      refine ⟨62520970909353617284984183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83361294545804823046645577 62520970909353617284984183)
      ·
        refine ⟨93781456364030425927476275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62520970909353617284984183 93781456364030425927476275)
        ·
          refine ⟨140672184546045638891214413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93781456364030425927476275 140672184546045638891214413)
          ·
            refine ⟨52752069204767114584205405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 140672184546045638891214413 52752069204767114584205405)
            ·
              refine ⟨19782025951787667969077027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52752069204767114584205405 19782025951787667969077027)
              ·
                refine ⟨29673038927681501953615541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19782025951787667969077027 29673038927681501953615541)
                ·
                  refine ⟨2781847399470140808151457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 29673038927681501953615541 2781847399470140808151457)
                  ·
                    refine ⟨2086385549602605606113593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2781847399470140808151457 2086385549602605606113593)
                    ·
                      refine ⟨1564789162201954204585195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2086385549602605606113593 1564789162201954204585195)
                      ·
                        rfl

theorem cell23_3047416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 1, 5, 2, 2].length) (baseStart_3047416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3047416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3047416 prefixEnd_3047416 := by exact prefixLift 3047416
  have htrace : WordTrace (prefixWord ++ tailWord_3047416) baseStart_3047416 baseEnd_3047416 := by
    simpa [prefixWord, tailWord_3047416, baseEnd_3047416] using wordTrace_append hprefix tailTrace_3047416
  have hstable : (prefixWord ++ tailWord_3047416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3047416).length < 2 ^ (prefixWord ++ tailWord_3047416).sum := by decide
  have hdescent : baseEnd_3047416 < baseStart_3047416 := by decide
  rcases family_descends (prefixWord ++ tailWord_3047416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3047419 : List Nat := [1, 1, 1, 1, 1, 3, 6, 1, 3, 2, 3]
def baseStart_3047419 : Nat := 118140960795 + 3047419 * 2 ^ 59
def prefixEnd_3047419 : Nat := 4983230072969 + 3 ^ 40 * 3047419 * 2
def baseEnd_3047419 : Nat := 1564790702643917692847681

theorem tailTrace_3047419 : CollatzResearch.WordTrace tailWord_3047419 prefixEnd_3047419 1564790702643917692847681 := by
  unfold tailWord_3047419
  simp only [CollatzResearch.WordTrace]
  refine ⟨111148502146728895574553311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74099001431152597049702207 111148502146728895574553311)
  ·
    refine ⟨166722753220093343361829967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111148502146728895574553311 166722753220093343361829967)
    ·
      refine ⟨250084129830140015042744951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166722753220093343361829967 250084129830140015042744951)
      ·
        refine ⟨375126194745210022564117427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 250084129830140015042744951 375126194745210022564117427)
        ·
          refine ⟨562689292117815033846176141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 375126194745210022564117427 562689292117815033846176141)
          ·
            refine ⟨211008484544180637692316053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 562689292117815033846176141 211008484544180637692316053)
            ·
              refine ⟨9891022713008467391827315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 211008484544180637692316053 9891022713008467391827315)
              ·
                refine ⟨14836534069512701087740973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9891022713008467391827315 14836534069512701087740973)
                ·
                  refine ⟨5563700276067262907902865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14836534069512701087740973 5563700276067262907902865)
                  ·
                    refine ⟨4172775207050447180927149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5563700276067262907902865 4172775207050447180927149)
                    ·
                      refine ⟨1564790702643917692847681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4172775207050447180927149 1564790702643917692847681)
                      ·
                        rfl

theorem cell23_3047419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 6, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 6, 1, 3, 2, 3].length) (baseStart_3047419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3047419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3047419 prefixEnd_3047419 := by exact prefixLift 3047419
  have htrace : WordTrace (prefixWord ++ tailWord_3047419) baseStart_3047419 baseEnd_3047419 := by
    simpa [prefixWord, tailWord_3047419, baseEnd_3047419] using wordTrace_append hprefix tailTrace_3047419
  have hstable : (prefixWord ++ tailWord_3047419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3047419).length < 2 ^ (prefixWord ++ tailWord_3047419).sum := by decide
  have hdescent : baseEnd_3047419 < baseStart_3047419 := by decide
  rcases family_descends (prefixWord ++ tailWord_3047419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3047429 : List Nat := [1, 3, 1, 1, 2, 4, 2, 2, 1, 2, 4]
def baseStart_3047429 : Nat := 118140960795 + 3047429 * 2 ^ 59
def prefixEnd_3047429 : Nat := 4983230072969 + 3 ^ 40 * 3047429 * 2
def baseEnd_3047429 : Nat := 1564795837450462653722635

theorem tailTrace_3047429 : CollatzResearch.WordTrace tailWord_3047429 prefixEnd_3047429 1564795837450462653722635 := by
  unfold tailWord_3047429
  simp only [CollatzResearch.WordTrace]
  refine ⟨111148866876692667282417341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74099244584461778188278227 111148866876692667282417341)
  ·
    refine ⟨41680825078759750230906503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111148866876692667282417341 41680825078759750230906503)
    ·
      refine ⟨62521237618139625346359755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41680825078759750230906503 62521237618139625346359755)
      ·
        refine ⟨93781856427209438019539633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62521237618139625346359755 93781856427209438019539633)
        ·
          refine ⟨70336392320407078514654725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93781856427209438019539633 70336392320407078514654725)
          ·
            refine ⟨13188073560076327221497761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 70336392320407078514654725 13188073560076327221497761)
            ·
              refine ⟨9891055170057245416123321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13188073560076327221497761 9891055170057245416123321)
              ·
                refine ⟨7418291377542934062092491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9891055170057245416123321 7418291377542934062092491)
                ·
                  refine ⟨11127437066314401093138737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7418291377542934062092491 11127437066314401093138737)
                  ·
                    refine ⟨8345577799735800819854053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11127437066314401093138737 8345577799735800819854053)
                    ·
                      refine ⟨1564795837450462653722635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8345577799735800819854053 1564795837450462653722635)
                      ·
                        rfl

theorem cell23_3047429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 2, 2, 1, 2, 4].length) (baseStart_3047429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3047429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3047429 prefixEnd_3047429 := by exact prefixLift 3047429
  have htrace : WordTrace (prefixWord ++ tailWord_3047429) baseStart_3047429 baseEnd_3047429 := by
    simpa [prefixWord, tailWord_3047429, baseEnd_3047429] using wordTrace_append hprefix tailTrace_3047429
  have hstable : (prefixWord ++ tailWord_3047429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3047429).length < 2 ^ (prefixWord ++ tailWord_3047429).sum := by decide
  have hdescent : baseEnd_3047429 < baseStart_3047429 := by decide
  rcases family_descends (prefixWord ++ tailWord_3047429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3047436 : List Nat := [2, 2, 1, 2, 3, 1, 3, 3, 1, 2, 3]
def baseStart_3047436 : Nat := 118140960795 + 3047436 * 2 ^ 59
def prefixEnd_3047436 : Nat := 4983230072969 + 3 ^ 40 * 3047436 * 2
def baseEnd_3047436 : Nat := 1564799431815044126335103

theorem tailTrace_3047436 : CollatzResearch.WordTrace tailWord_3047436 prefixEnd_3047436 1564799431815044126335103 := by
  unfold tailWord_3047436
  simp only [CollatzResearch.WordTrace]
  refine ⟨55574561093833653738961081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74099414791778204985281441 55574561093833653738961081)
  ·
    refine ⟨41680920820375240304220811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55574561093833653738961081 41680920820375240304220811)
    ·
      refine ⟨62521381230562860456331217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41680920820375240304220811 62521381230562860456331217)
      ·
        refine ⟨46891035922922145342248413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62521381230562860456331217 46891035922922145342248413)
        ·
          refine ⟨17584138471095804503343155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46891035922922145342248413 17584138471095804503343155)
          ·
            refine ⟨26376207706643706755014733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17584138471095804503343155 26376207706643706755014733)
            ·
              refine ⟨9891077889991390033130525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26376207706643706755014733 9891077889991390033130525)
              ·
                refine ⟨3709154208746771262423947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9891077889991390033130525 3709154208746771262423947)
                ·
                  refine ⟨5563731313120156893635921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3709154208746771262423947 5563731313120156893635921)
                  ·
                    refine ⟨4172798484840117670226941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5563731313120156893635921 4172798484840117670226941)
                    ·
                      refine ⟨1564799431815044126335103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4172798484840117670226941 1564799431815044126335103)
                      ·
                        rfl

theorem cell23_3047436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 3, 3, 1, 2, 3].length) (baseStart_3047436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3047436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3047436 prefixEnd_3047436 := by exact prefixLift 3047436
  have htrace : WordTrace (prefixWord ++ tailWord_3047436) baseStart_3047436 baseEnd_3047436 := by
    simpa [prefixWord, tailWord_3047436, baseEnd_3047436] using wordTrace_append hprefix tailTrace_3047436
  have hstable : (prefixWord ++ tailWord_3047436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3047436).length < 2 ^ (prefixWord ++ tailWord_3047436).sum := by decide
  have hdescent : baseEnd_3047436 < baseStart_3047436 := by decide
  rcases family_descends (prefixWord ++ tailWord_3047436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3047450 : List Nat := [3, 1, 1, 3, 1, 3, 2, 4, 1, 2, 2]
def baseStart_3047450 : Nat := 118140960795 + 3047450 * 2 ^ 59
def prefixEnd_3047450 : Nat := 4983230072969 + 3 ^ 40 * 3047450 * 2
def baseEnd_3047450 : Nat := 1564806620544207071560039

theorem tailTrace_3047450 : CollatzResearch.WordTrace tailWord_3047450 prefixEnd_3047450 1564806620544207071560039 := by
  unfold tailWord_3047450
  simp only [CollatzResearch.WordTrace]
  refine ⟨27787408202404146967232951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74099755206411058579287869 27787408202404146967232951)
  ·
    refine ⟨41681112303606220450849427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27787408202404146967232951 41681112303606220450849427)
    ·
      refine ⟨62521668455409330676274141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41681112303606220450849427 62521668455409330676274141)
      ·
        refine ⟨23445625670778499003602803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62521668455409330676274141 23445625670778499003602803)
        ·
          refine ⟨35168438506167748505404205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23445625670778499003602803 35168438506167748505404205)
          ·
            refine ⟨13188164439812905689526577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35168438506167748505404205 13188164439812905689526577)
            ·
              refine ⟨9891123329859679267144933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13188164439812905689526577 9891123329859679267144933)
              ·
                refine ⟨1854585624348689862589675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9891123329859679267144933 1854585624348689862589675)
                ·
                  refine ⟨2781878436523034793884513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1854585624348689862589675 2781878436523034793884513)
                  ·
                    refine ⟨2086408827392276095413385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2781878436523034793884513 2086408827392276095413385)
                    ·
                      refine ⟨1564806620544207071560039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2086408827392276095413385 1564806620544207071560039)
                      ·
                        rfl

theorem cell23_3047450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 2, 4, 1, 2, 2].length) (baseStart_3047450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3047450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3047450 prefixEnd_3047450 := by exact prefixLift 3047450
  have htrace : WordTrace (prefixWord ++ tailWord_3047450) baseStart_3047450 baseEnd_3047450 := by
    simpa [prefixWord, tailWord_3047450, baseEnd_3047450] using wordTrace_append hprefix tailTrace_3047450
  have hstable : (prefixWord ++ tailWord_3047450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3047450).length < 2 ^ (prefixWord ++ tailWord_3047450).sum := by decide
  have hdescent : baseEnd_3047450 < baseStart_3047450 := by decide
  rcases family_descends (prefixWord ++ tailWord_3047450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3047460 : List Nat := [2, 3, 1, 4, 2, 1, 3, 1, 2, 4]
def baseStart_3047460 : Nat := 118140960795 + 3047460 * 2 ^ 59
def prefixEnd_3047460 : Nat := 4983230072969 + 3 ^ 40 * 3047460 * 2
def baseEnd_3047460 : Nat := 521603918450250677478331

theorem tailTrace_3047460 : CollatzResearch.WordTrace tailWord_3047460 prefixEnd_3047460 521603918450250677478331 := by
  unfold tailWord_3047460
  simp only [CollatzResearch.WordTrace]
  refine ⟨55574998769790179788397917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74099998359720239717863889 55574998769790179788397917)
  ·
    refine ⟨20840624538671317420649219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55574998769790179788397917 20840624538671317420649219)
    ·
      refine ⟨31260936808006976130973829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20840624538671317420649219 31260936808006976130973829)
      ·
        refine ⟨5861425651501308024557593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31260936808006976130973829 5861425651501308024557593)
        ·
          refine ⟨4396069238625981018418195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5861425651501308024557593 4396069238625981018418195)
          ·
            refine ⟨6594103857938971527627293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4396069238625981018418195 6594103857938971527627293)
            ·
              refine ⟨2472788946727114322860235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6594103857938971527627293 2472788946727114322860235)
              ·
                refine ⟨3709183420090671484290353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2472788946727114322860235 3709183420090671484290353)
                ·
                  refine ⟨2781887565068003613217765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3709183420090671484290353 2781887565068003613217765)
                  ·
                    refine ⟨521603918450250677478331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2781887565068003613217765 521603918450250677478331)
                    ·
                      rfl

theorem cell23_3047460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 3, 1, 2, 4].length) (baseStart_3047460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3047460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3047460 prefixEnd_3047460 := by exact prefixLift 3047460
  have htrace : WordTrace (prefixWord ++ tailWord_3047460) baseStart_3047460 baseEnd_3047460 := by
    simpa [prefixWord, tailWord_3047460, baseEnd_3047460] using wordTrace_append hprefix tailTrace_3047460
  have hstable : (prefixWord ++ tailWord_3047460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3047460).length < 2 ^ (prefixWord ++ tailWord_3047460).sum := by decide
  have hdescent : baseEnd_3047460 < baseStart_3047460 := by decide
  rcases family_descends (prefixWord ++ tailWord_3047460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3047517 : List Nat := [1, 4, 4, 1, 1, 1, 4, 1, 2, 1, 3]
def baseStart_3047517 : Nat := 118140960795 + 3047517 * 2 ^ 59
def prefixEnd_3047517 : Nat := 4983230072969 + 3 ^ 40 * 3047517 * 2
def baseEnd_3047517 : Nat := 1564841023748058309422231

theorem tailTrace_3047517 : CollatzResearch.WordTrace tailWord_3047517 prefixEnd_3047517 1564841023748058309422231 := by
  unfold tailWord_3047517
  simp only [CollatzResearch.WordTrace]
  refine ⟨111152076500373858311620805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74101384333582572207747203 111152076500373858311620805)
  ·
    refine ⟨20841014343820098433428901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 111152076500373858311620805 20841014343820098433428901)
    ·
      refine ⟨3907690189466268456267919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20841014343820098433428901 3907690189466268456267919)
      ·
        refine ⟨5861535284199402684401879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3907690189466268456267919 5861535284199402684401879)
        ·
          refine ⟨8792302926299104026602819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5861535284199402684401879 8792302926299104026602819)
          ·
            refine ⟨13188454389448656039904229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8792302926299104026602819 13188454389448656039904229)
            ·
              refine ⟨2472835198021623007482043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13188454389448656039904229 2472835198021623007482043)
              ·
                refine ⟨3709252797032434511223065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2472835198021623007482043 3709252797032434511223065)
                ·
                  refine ⟨2781939597774325883417299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3709252797032434511223065 2781939597774325883417299)
                  ·
                    refine ⟨4172909396661488825125949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2781939597774325883417299 4172909396661488825125949)
                    ·
                      refine ⟨1564841023748058309422231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4172909396661488825125949 1564841023748058309422231)
                      ·
                        rfl

theorem cell23_3047517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 4, 1, 2, 1, 3].length) (baseStart_3047517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3047517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3047517 prefixEnd_3047517 := by exact prefixLift 3047517
  have htrace : WordTrace (prefixWord ++ tailWord_3047517) baseStart_3047517 baseEnd_3047517 := by
    simpa [prefixWord, tailWord_3047517, baseEnd_3047517] using wordTrace_append hprefix tailTrace_3047517
  have hstable : (prefixWord ++ tailWord_3047517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3047517).length < 2 ^ (prefixWord ++ tailWord_3047517).sum := by decide
  have hdescent : baseEnd_3047517 < baseStart_3047517 := by decide
  rcases family_descends (prefixWord ++ tailWord_3047517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3047556 : List Nat := [2, 3, 2, 1, 2, 1, 2, 2, 2, 3, 3]
def baseStart_3047556 : Nat := 118140960795 + 3047556 * 2 ^ 59
def prefixEnd_3047556 : Nat := 4983230072969 + 3 ^ 40 * 3047556 * 2
def baseEnd_3047556 : Nat := 1564861049493583656834551

theorem tailTrace_3047556 : CollatzResearch.WordTrace tailWord_3047556 prefixEnd_3047556 1564861049493583656834551 := by
  unfold tailWord_3047556
  simp only [CollatzResearch.WordTrace]
  refine ⟨55576749473616283986145261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74102332631488378648193681 55576749473616283986145261)
  ·
    refine ⟨20841281052606106494804473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55576749473616283986145261 20841281052606106494804473)
    ·
      refine ⟨15630960789454579871103355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20841281052606106494804473 15630960789454579871103355)
      ·
        refine ⟨23446441184181869806655033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15630960789454579871103355 23446441184181869806655033)
        ·
          refine ⟨17584830888136402354991275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23446441184181869806655033 17584830888136402354991275)
          ·
            refine ⟨26377246332204603532486913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17584830888136402354991275 26377246332204603532486913)
            ·
              refine ⟨19782934749153452649365185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26377246332204603532486913 19782934749153452649365185)
              ·
                refine ⟨14837201061865089487023889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19782934749153452649365185 14837201061865089487023889)
                ·
                  refine ⟨11127900796398817115267917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14837201061865089487023889 11127900796398817115267917)
                  ·
                    refine ⟨4172962798649556418225469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11127900796398817115267917 4172962798649556418225469)
                    ·
                      refine ⟨1564861049493583656834551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4172962798649556418225469 1564861049493583656834551)
                      ·
                        rfl

theorem cell23_3047556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 2, 2, 3, 3].length) (baseStart_3047556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3047556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3047556 prefixEnd_3047556 := by exact prefixLift 3047556
  have htrace : WordTrace (prefixWord ++ tailWord_3047556) baseStart_3047556 baseEnd_3047556 := by
    simpa [prefixWord, tailWord_3047556, baseEnd_3047556] using wordTrace_append hprefix tailTrace_3047556
  have hstable : (prefixWord ++ tailWord_3047556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3047556).length < 2 ^ (prefixWord ++ tailWord_3047556).sum := by decide
  have hdescent : baseEnd_3047556 < baseStart_3047556 := by decide
  rcases family_descends (prefixWord ++ tailWord_3047556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3047609 : List Nat := [1, 2, 1, 4, 1, 2, 1, 1, 1, 3, 6]
def baseStart_3047609 : Nat := 118140960795 + 3047609 * 2 ^ 59
def prefixEnd_3047609 : Nat := 4983230072969 + 3 ^ 40 * 3047609 * 2
def baseEnd_3047609 : Nat := 1564888263968271949471807

theorem tailTrace_3047609 : CollatzResearch.WordTrace tailWord_3047609 prefixEnd_3047609 1564888263968271949471807 := by
  unfold tailWord_3047609
  simp only [CollatzResearch.WordTrace]
  refine ⟨111155432016040558023969881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74103621344027038682646587 111155432016040558023969881)
  ·
    refine ⟨83366574012030418517977411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111155432016040558023969881 83366574012030418517977411)
    ·
      refine ⟨125049861018045627776966117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83366574012030418517977411 125049861018045627776966117)
      ·
        refine ⟨23446848940883555208181147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 125049861018045627776966117 23446848940883555208181147)
        ·
          refine ⟨35170273411325332812271721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23446848940883555208181147 35170273411325332812271721)
          ·
            refine ⟨26377705058493999609203791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35170273411325332812271721 26377705058493999609203791)
            ·
              refine ⟨39566557587740999413805687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26377705058493999609203791 39566557587740999413805687)
              ·
                refine ⟨59349836381611499120708531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39566557587740999413805687 59349836381611499120708531)
                ·
                  refine ⟨89024754572417248681062797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59349836381611499120708531 89024754572417248681062797)
                  ·
                    refine ⟨33384282964656468255398549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 89024754572417248681062797 33384282964656468255398549)
                    ·
                      refine ⟨1564888263968271949471807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 33384282964656468255398549 1564888263968271949471807)
                      ·
                        rfl

theorem cell23_3047609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 1, 1, 3, 6].length) (baseStart_3047609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3047609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3047609 prefixEnd_3047609 := by exact prefixLift 3047609
  have htrace : WordTrace (prefixWord ++ tailWord_3047609) baseStart_3047609 baseEnd_3047609 := by
    simpa [prefixWord, tailWord_3047609, baseEnd_3047609] using wordTrace_append hprefix tailTrace_3047609
  have hstable : (prefixWord ++ tailWord_3047609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3047609).length < 2 ^ (prefixWord ++ tailWord_3047609).sum := by decide
  have hdescent : baseEnd_3047609 < baseStart_3047609 := by decide
  rcases family_descends (prefixWord ++ tailWord_3047609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3047639 : List Nat := [1, 1, 3, 2, 1, 2, 1, 1, 3, 2, 6]
def baseStart_3047639 : Nat := 118140960795 + 3047639 * 2 ^ 59
def prefixEnd_3047639 : Nat := 4983230072969 + 3 ^ 40 * 3047639 * 2
def baseEnd_3047639 : Nat := 1564903668387906832096669

theorem tailTrace_3047639 : CollatzResearch.WordTrace tailWord_3047639 prefixEnd_3047639 1564903668387906832096669 := by
  unfold tailWord_3047639
  simp only [CollatzResearch.WordTrace]
  refine ⟨111156526205931873147561971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74104350803954582098374647 111156526205931873147561971)
  ·
    refine ⟨166734789308897809721342957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111156526205931873147561971 166734789308897809721342957)
    ·
      refine ⟨62525545990836678645503609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 166734789308897809721342957 62525545990836678645503609)
      ·
        refine ⟨46894159493127508984127707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62525545990836678645503609 46894159493127508984127707)
        ·
          refine ⟨70341239239691263476191561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46894159493127508984127707 70341239239691263476191561)
          ·
            refine ⟨52755929429768447607143671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70341239239691263476191561 52755929429768447607143671)
            ·
              refine ⟨79133894144652671410715507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52755929429768447607143671 79133894144652671410715507)
              ·
                refine ⟨118700841216979007116073261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79133894144652671410715507 118700841216979007116073261)
                ·
                  refine ⟨44512815456367127668527473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 118700841216979007116073261 44512815456367127668527473)
                  ·
                    refine ⟨33384611592275345751395605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 44512815456367127668527473 33384611592275345751395605)
                    ·
                      refine ⟨1564903668387906832096669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 33384611592275345751395605 1564903668387906832096669)
                      ·
                        rfl

theorem cell23_3047639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 1, 3, 2, 6].length) (baseStart_3047639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3047639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3047639 prefixEnd_3047639 := by exact prefixLift 3047639
  have htrace : WordTrace (prefixWord ++ tailWord_3047639) baseStart_3047639 baseEnd_3047639 := by
    simpa [prefixWord, tailWord_3047639, baseEnd_3047639] using wordTrace_append hprefix tailTrace_3047639
  have hstable : (prefixWord ++ tailWord_3047639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3047639).length < 2 ^ (prefixWord ++ tailWord_3047639).sum := by decide
  have hdescent : baseEnd_3047639 < baseStart_3047639 := by decide
  rcases family_descends (prefixWord ++ tailWord_3047639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3047680 : List Nat := [2, 1, 1, 2, 1, 1, 4, 6, 1, 1, 3]
def baseStart_3047680 : Nat := 118140960795 + 3047680 * 2 ^ 59
def prefixEnd_3047680 : Nat := 4983230072969 + 3 ^ 40 * 3047680 * 2
def baseEnd_3047680 : Nat := 1564924721094741171683981

theorem tailTrace_3047680 : CollatzResearch.WordTrace tailWord_3047680 prefixEnd_3047680 1564924721094741171683981 := by
  unfold tailWord_3047680
  simp only [CollatzResearch.WordTrace]
  refine ⟨55579010799391668574902247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74105347732522224766536329 55579010799391668574902247)
  ·
    refine ⟨83368516199087502862353371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55579010799391668574902247 83368516199087502862353371)
    ·
      refine ⟨125052774298631254293530057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83368516199087502862353371 125052774298631254293530057)
      ·
        refine ⟨93789580723973440720147543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125052774298631254293530057 93789580723973440720147543)
        ·
          refine ⟨140684371085960161080221315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93789580723973440720147543 140684371085960161080221315)
          ·
            refine ⟨211026556628940241620331973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140684371085960161080221315 211026556628940241620331973)
            ·
              refine ⟨39567479367926295303812245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 211026556628940241620331973 39567479367926295303812245)
              ·
                refine ⟨1854725595371545092366199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 39567479367926295303812245 1854725595371545092366199)
                ·
                  refine ⟨2782088393057317638549299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1854725595371545092366199 2782088393057317638549299)
                  ·
                    refine ⟨4173132589585976457823949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2782088393057317638549299 4173132589585976457823949)
                    ·
                      refine ⟨1564924721094741171683981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4173132589585976457823949 1564924721094741171683981)
                      ·
                        rfl

theorem cell23_3047680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 6, 1, 1, 3].length) (baseStart_3047680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3047680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3047680 prefixEnd_3047680 := by exact prefixLift 3047680
  have htrace : WordTrace (prefixWord ++ tailWord_3047680) baseStart_3047680 baseEnd_3047680 := by
    simpa [prefixWord, tailWord_3047680, baseEnd_3047680] using wordTrace_append hprefix tailTrace_3047680
  have hstable : (prefixWord ++ tailWord_3047680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3047680).length < 2 ^ (prefixWord ++ tailWord_3047680).sum := by decide
  have hdescent : baseEnd_3047680 < baseStart_3047680 := by decide
  rcases family_descends (prefixWord ++ tailWord_3047680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3047687 : List Nat := [1, 1, 4, 5, 1, 2, 2, 1, 6]
def baseStart_3047687 : Nat := 118140960795 + 3047687 * 2 ^ 59
def prefixEnd_3047687 : Nat := 4983230072969 + 3 ^ 40 * 3047687 * 2
def baseEnd_3047687 : Nat := 173880923939924738255161

theorem tailTrace_3047687 : CollatzResearch.WordTrace tailWord_3047687 prefixEnd_3047687 173880923939924738255161 := by
  unfold tailWord_3047687
  simp only [CollatzResearch.WordTrace]
  refine ⟨111158276909757977345309315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74105517939838651563539543 111158276909757977345309315)
  ·
    refine ⟨166737415364636966017963973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111158276909757977345309315 166737415364636966017963973)
    ·
      refine ⟨31263265380869431128368245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 166737415364636966017963973 31263265380869431128368245)
      ·
        refine ⟨2930931129456509168284523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 31263265380869431128368245 2930931129456509168284523)
        ·
          refine ⟨4396396694184763752426785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2930931129456509168284523 4396396694184763752426785)
          ·
            refine ⟨3297297520638572814320089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4396396694184763752426785 3297297520638572814320089)
            ·
              refine ⟨2472973140478929610740067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3297297520638572814320089 2472973140478929610740067)
              ·
                refine ⟨3709459710718394416110101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2472973140478929610740067 3709459710718394416110101)
                ·
                  refine ⟨173880923939924738255161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3709459710718394416110101 173880923939924738255161)
                  ·
                    rfl

theorem cell23_3047687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 2, 2, 1, 6].length) (baseStart_3047687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3047687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3047687 prefixEnd_3047687 := by exact prefixLift 3047687
  have htrace : WordTrace (prefixWord ++ tailWord_3047687) baseStart_3047687 baseEnd_3047687 := by
    simpa [prefixWord, tailWord_3047687, baseEnd_3047687] using wordTrace_append hprefix tailTrace_3047687
  have hstable : (prefixWord ++ tailWord_3047687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3047687).length < 2 ^ (prefixWord ++ tailWord_3047687).sum := by decide
  have hdescent : baseEnd_3047687 < baseStart_3047687 := by decide
  rcases family_descends (prefixWord ++ tailWord_3047687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3047703 : List Nat := [1, 1, 3, 4, 1, 3, 1, 1, 3, 1, 4]
def baseStart_3047703 : Nat := 118140960795 + 3047703 * 2 ^ 59
def prefixEnd_3047703 : Nat := 4983230072969 + 3 ^ 40 * 3047703 * 2
def baseEnd_3047703 : Nat := 1564936531149794581696375

theorem tailTrace_3047703 : CollatzResearch.WordTrace tailWord_3047703 prefixEnd_3047703 1564936531149794581696375 := by
  unfold tailWord_3047703
  simp only [CollatzResearch.WordTrace]
  refine ⟨111158860477700012077891763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74105906985133341385261175 111158860477700012077891763)
  ·
    refine ⟨166738290716550018116837645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111158860477700012077891763 166738290716550018116837645)
    ·
      refine ⟨62526859018706256793814117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 166738290716550018116837645 62526859018706256793814117)
      ·
        refine ⟨11723786066007423148840147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 62526859018706256793814117 11723786066007423148840147)
        ·
          refine ⟨17585679099011134723260221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11723786066007423148840147 17585679099011134723260221)
          ·
            refine ⟨6594629662129175521222583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17585679099011134723260221 6594629662129175521222583)
            ·
              refine ⟨9891944493193763281833875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6594629662129175521222583 9891944493193763281833875)
              ·
                refine ⟨14837916739790644922750813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9891944493193763281833875 14837916739790644922750813)
                ·
                  refine ⟨5564218777421491846031555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14837916739790644922750813 5564218777421491846031555)
                  ·
                    refine ⟨8346328166132237769047333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5564218777421491846031555 8346328166132237769047333)
                    ·
                      refine ⟨1564936531149794581696375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8346328166132237769047333 1564936531149794581696375)
                      ·
                        rfl

theorem cell23_3047703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 1, 1, 3, 1, 4].length) (baseStart_3047703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3047703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3047703 prefixEnd_3047703 := by exact prefixLift 3047703
  have htrace : WordTrace (prefixWord ++ tailWord_3047703) baseStart_3047703 baseEnd_3047703 := by
    simpa [prefixWord, tailWord_3047703, baseEnd_3047703] using wordTrace_append hprefix tailTrace_3047703
  have hstable : (prefixWord ++ tailWord_3047703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3047703).length < 2 ^ (prefixWord ++ tailWord_3047703).sum := by decide
  have hdescent : baseEnd_3047703 < baseStart_3047703 := by decide
  rcases family_descends (prefixWord ++ tailWord_3047703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3047753 : List Nat := [1, 2, 1, 1, 2, 3, 1, 2, 6, 1, 3]
def baseStart_3047753 : Nat := 118140960795 + 3047753 * 2 ^ 59
def prefixEnd_3047753 : Nat := 4983230072969 + 3 ^ 40 * 3047753 * 2
def baseEnd_3047753 : Nat := 1564962205182519386071145

theorem tailTrace_3047753 : CollatzResearch.WordTrace tailWord_3047753 prefixEnd_3047753 1564962205182519386071145 := by
  unfold tailWord_3047753
  simp only [CollatzResearch.WordTrace]
  refine ⟨111160684127518870617211913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74107122751679247078141275 111160684127518870617211913)
  ·
    refine ⟨83370513095639152962908935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111160684127518870617211913 83370513095639152962908935)
    ·
      refine ⟨125055769643458729444363403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83370513095639152962908935 125055769643458729444363403)
      ·
        refine ⟨187583654465188094166545105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125055769643458729444363403 187583654465188094166545105)
        ·
          refine ⟨140687740848891070624908829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 187583654465188094166545105 140687740848891070624908829)
          ·
            refine ⟨52757902818334151484340811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 140687740848891070624908829 52757902818334151484340811)
            ·
              refine ⟨79136854227501227226511217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52757902818334151484340811 79136854227501227226511217)
              ·
                refine ⟨59352640670625920419883413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79136854227501227226511217 59352640670625920419883413)
                ·
                  refine ⟨2782155031435590019682035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 59352640670625920419883413 2782155031435590019682035)
                  ·
                    refine ⟨4173232547153385029523053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2782155031435590019682035 4173232547153385029523053)
                    ·
                      refine ⟨1564962205182519386071145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4173232547153385029523053 1564962205182519386071145)
                      ·
                        rfl

theorem cell23_3047753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 2, 6, 1, 3].length) (baseStart_3047753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3047753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3047753 prefixEnd_3047753 := by exact prefixLift 3047753
  have htrace : WordTrace (prefixWord ++ tailWord_3047753) baseStart_3047753 baseEnd_3047753 := by
    simpa [prefixWord, tailWord_3047753, baseEnd_3047753] using wordTrace_append hprefix tailTrace_3047753
  have hstable : (prefixWord ++ tailWord_3047753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3047753).length < 2 ^ (prefixWord ++ tailWord_3047753).sum := by decide
  have hdescent : baseEnd_3047753 < baseStart_3047753 := by decide
  rcases family_descends (prefixWord ++ tailWord_3047753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3047756 : List Nat := [2, 2, 1, 3, 2, 1, 1, 2, 2, 7]
def baseStart_3047756 : Nat := 118140960795 + 3047756 * 2 ^ 59
def prefixEnd_3047756 : Nat := 4983230072969 + 3 ^ 40 * 3047756 * 2
def baseEnd_3047756 : Nat := 521654581874827624777877

theorem tailTrace_3047756 : CollatzResearch.WordTrace tailWord_3047756 prefixEnd_3047756 521654581874827624777877 := by
  unfold tailWord_3047756
  simp only [CollatzResearch.WordTrace]
  refine ⟨55580396773254001064785561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74107195697672001419714081 55580396773254001064785561)
  ·
    refine ⟨41685297579940500798589171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55580396773254001064785561 41685297579940500798589171)
    ·
      refine ⟨62527946369910751197883757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41685297579940500798589171 62527946369910751197883757)
      ·
        refine ⟨23447979888716531699206409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62527946369910751197883757 23447979888716531699206409)
        ·
          refine ⟨17585984916537398774404807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23447979888716531699206409 17585984916537398774404807)
          ·
            refine ⟨26378977374806098161607211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17585984916537398774404807 26378977374806098161607211)
            ·
              refine ⟨39568466062209147242410817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26378977374806098161607211 39568466062209147242410817)
              ·
                refine ⟨29676349546656860431808113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39568466062209147242410817 29676349546656860431808113)
                ·
                  refine ⟨22257262159992645323856085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29676349546656860431808113 22257262159992645323856085)
                  ·
                    refine ⟨521654581874827624777877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 22257262159992645323856085 521654581874827624777877)
                    ·
                      rfl

theorem cell23_3047756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 2, 2, 7].length) (baseStart_3047756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3047756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3047756 prefixEnd_3047756 := by exact prefixLift 3047756
  have htrace : WordTrace (prefixWord ++ tailWord_3047756) baseStart_3047756 baseEnd_3047756 := by
    simpa [prefixWord, tailWord_3047756, baseEnd_3047756] using wordTrace_append hprefix tailTrace_3047756
  have hstable : (prefixWord ++ tailWord_3047756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3047756).length < 2 ^ (prefixWord ++ tailWord_3047756).sum := by decide
  have hdescent : baseEnd_3047756 < baseStart_3047756 := by decide
  rcases family_descends (prefixWord ++ tailWord_3047756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3047880 : List Nat := [2, 1, 3, 1, 3, 3, 2, 1, 2, 5]
def baseStart_3047880 : Nat := 118140960795 + 3047880 * 2 ^ 59
def prefixEnd_3047880 : Nat := 4983230072969 + 3 ^ 40 * 3047880 * 2
def baseEnd_3047880 : Nat := 521675805741880129727687

theorem tailTrace_3047880 : CollatzResearch.WordTrace tailWord_3047880 prefixEnd_3047880 521675805741880129727687 := by
  unfold tailWord_3047880
  simp only [CollatzResearch.WordTrace]
  refine ⟨55582658099029385653542547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74110210798705847538056729 55582658099029385653542547)
  ·
    refine ⟨83373987148544078480313821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55582658099029385653542547 83373987148544078480313821)
    ·
      refine ⟨31265245180704029430117683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83373987148544078480313821 31265245180704029430117683)
      ·
        refine ⟨46897867771056044145176525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31265245180704029430117683 46897867771056044145176525)
        ·
          refine ⟨17586700414146016554441197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46897867771056044145176525 17586700414146016554441197)
          ·
            refine ⟨6595012655304756207915449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17586700414146016554441197 6595012655304756207915449)
            ·
              refine ⟨4946259491478567155936587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6595012655304756207915449 4946259491478567155936587)
              ·
                refine ⟨7419389237217850733904881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4946259491478567155936587 7419389237217850733904881)
                ·
                  refine ⟨5564541927913388050428661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7419389237217850733904881 5564541927913388050428661)
                  ·
                    refine ⟨521675805741880129727687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5564541927913388050428661 521675805741880129727687)
                    ·
                      rfl

theorem cell23_3047880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 2, 1, 2, 5].length) (baseStart_3047880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3047880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3047880 prefixEnd_3047880 := by exact prefixLift 3047880
  have htrace : WordTrace (prefixWord ++ tailWord_3047880) baseStart_3047880 baseEnd_3047880 := by
    simpa [prefixWord, tailWord_3047880, baseEnd_3047880] using wordTrace_append hprefix tailTrace_3047880
  have hstable : (prefixWord ++ tailWord_3047880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3047880).length < 2 ^ (prefixWord ++ tailWord_3047880).sum := by decide
  have hdescent : baseEnd_3047880 < baseStart_3047880 := by decide
  rcases family_descends (prefixWord ++ tailWord_3047880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3047917 : List Nat := [1, 5, 1, 3, 1, 1, 1, 1, 1, 6, 2]
def baseStart_3047917 : Nat := 118140960795 + 3047917 * 2 ^ 59
def prefixEnd_3047917 : Nat := 4983230072969 + 3 ^ 40 * 3047917 * 2
def baseEnd_3047917 : Nat := 1565046416009856744420391

theorem tailTrace_3047917 : CollatzResearch.WordTrace tailWord_3047917 prefixEnd_3047917 1565046416009856744420391 := by
  unfold tailWord_3047917
  simp only [CollatzResearch.WordTrace]
  refine ⟨111166665698924726626182005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74111110465949817750788003 111166665698924726626182005)
  ·
    refine ⟨10421874909274193121204563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 111166665698924726626182005 10421874909274193121204563)
    ·
      refine ⟨15632812363911289681806845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10421874909274193121204563 15632812363911289681806845)
      ·
        refine ⟨5862304636466733630677567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15632812363911289681806845 5862304636466733630677567)
        ·
          refine ⟨8793456954700100446016351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5862304636466733630677567 8793456954700100446016351)
          ·
            refine ⟨13190185432050150669024527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8793456954700100446016351 13190185432050150669024527)
            ·
              refine ⟨19785278148075226003536791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13190185432050150669024527 19785278148075226003536791)
              ·
                refine ⟨29677917222112839005305187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19785278148075226003536791 29677917222112839005305187)
                ·
                  refine ⟨44516875833169258507957781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29677917222112839005305187 44516875833169258507957781)
                  ·
                    refine ⟨2086728554679808992560521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 44516875833169258507957781 2086728554679808992560521)
                    ·
                      refine ⟨1565046416009856744420391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2086728554679808992560521 1565046416009856744420391)
                      ·
                        rfl

theorem cell23_3047917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 1, 1, 6, 2].length) (baseStart_3047917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3047917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3047917 prefixEnd_3047917 := by exact prefixLift 3047917
  have htrace : WordTrace (prefixWord ++ tailWord_3047917) baseStart_3047917 baseEnd_3047917 := by
    simpa [prefixWord, tailWord_3047917, baseEnd_3047917] using wordTrace_append hprefix tailTrace_3047917
  have hstable : (prefixWord ++ tailWord_3047917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3047917).length < 2 ^ (prefixWord ++ tailWord_3047917).sum := by decide
  have hdescent : baseEnd_3047917 < baseStart_3047917 := by decide
  rcases family_descends (prefixWord ++ tailWord_3047917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3047923 : List Nat := [1, 1, 1, 2, 2, 2, 3, 5, 6]
def baseStart_3047923 : Nat := 118140960795 + 3047923 * 2 ^ 59
def prefixEnd_3047923 : Nat := 4983230072969 + 3 ^ 40 * 3047923 * 2
def baseEnd_3047923 : Nat := 173894388543753746771707

theorem tailTrace_3047923 : CollatzResearch.WordTrace tailWord_3047923 prefixEnd_3047923 173894388543753746771707 := by
  unfold tailWord_3047923
  simp only [CollatzResearch.WordTrace]
  refine ⟨111166884536902989650900423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74111256357935326433933615 111166884536902989650900423)
  ·
    refine ⟨166750326805354484476350635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111166884536902989650900423 166750326805354484476350635)
    ·
      refine ⟨250125490208031726714525953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166750326805354484476350635 250125490208031726714525953)
      ·
        refine ⟨187594117656023795035894465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 250125490208031726714525953 187594117656023795035894465)
        ·
          refine ⟨140695588242017846276920849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 187594117656023795035894465 140695588242017846276920849)
          ·
            refine ⟨105521691181513384707690637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 140695588242017846276920849 105521691181513384707690637)
            ·
              refine ⟨39570634193067519265383989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 105521691181513384707690637 39570634193067519265383989)
              ·
                refine ⟨3709746955600079931129749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 39570634193067519265383989 3709746955600079931129749)
                ·
                  refine ⟨173894388543753746771707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3709746955600079931129749 173894388543753746771707)
                  ·
                    rfl

theorem cell23_3047923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 5, 6].length) (baseStart_3047923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3047923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3047923 prefixEnd_3047923 := by exact prefixLift 3047923
  have htrace : WordTrace (prefixWord ++ tailWord_3047923) baseStart_3047923 baseEnd_3047923 := by
    simpa [prefixWord, tailWord_3047923, baseEnd_3047923] using wordTrace_append hprefix tailTrace_3047923
  have hstable : (prefixWord ++ tailWord_3047923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3047923).length < 2 ^ (prefixWord ++ tailWord_3047923).sum := by decide
  have hdescent : baseEnd_3047923 < baseStart_3047923 := by decide
  rcases family_descends (prefixWord ++ tailWord_3047923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3047937 : List Nat := [1, 2, 4, 1, 3, 1, 3, 1, 2, 2, 3]
def baseStart_3047937 : Nat := 118140960795 + 3047937 * 2 ^ 59
def prefixEnd_3047937 : Nat := 4983230072969 + 3 ^ 40 * 3047937 * 2
def baseEnd_3047937 : Nat := 1565056685622946666170299

theorem tailTrace_3047937 : CollatzResearch.WordTrace tailWord_3047937 prefixEnd_3047937 1565056685622946666170299 := by
  unfold tailWord_3047937
  simp only [CollatzResearch.WordTrace]
  refine ⟨111167395158852270041910065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74111596772568180027940043 111167395158852270041910065)
  ·
    refine ⟨83375546369139202531432549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111167395158852270041910065 83375546369139202531432549)
    ·
      refine ⟨15632914944213600474643603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 83375546369139202531432549 15632914944213600474643603)
      ·
        refine ⟨23449372416320400711965405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15632914944213600474643603 23449372416320400711965405)
        ·
          refine ⟨8793514656120150266987027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23449372416320400711965405 8793514656120150266987027)
          ·
            refine ⟨13190271984180225400480541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8793514656120150266987027 13190271984180225400480541)
            ·
              refine ⟨4946351994067584525180203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13190271984180225400480541 4946351994067584525180203)
              ·
                refine ⟨7419527991101376787770305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4946351994067584525180203 7419527991101376787770305)
                ·
                  refine ⟨5564645993326032590827729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7419527991101376787770305 5564645993326032590827729)
                  ·
                    refine ⟨4173484494994524443120797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5564645993326032590827729 4173484494994524443120797)
                    ·
                      refine ⟨1565056685622946666170299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4173484494994524443120797 1565056685622946666170299)
                      ·
                        rfl

theorem cell23_3047937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 3, 1, 2, 2, 3].length) (baseStart_3047937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3047937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3047937 prefixEnd_3047937 := by exact prefixLift 3047937
  have htrace : WordTrace (prefixWord ++ tailWord_3047937) baseStart_3047937 baseEnd_3047937 := by
    simpa [prefixWord, tailWord_3047937, baseEnd_3047937] using wordTrace_append hprefix tailTrace_3047937
  have hstable : (prefixWord ++ tailWord_3047937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3047937).length < 2 ^ (prefixWord ++ tailWord_3047937).sum := by decide
  have hdescent : baseEnd_3047937 < baseStart_3047937 := by decide
  rcases family_descends (prefixWord ++ tailWord_3047937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3047953 : List Nat := [1, 2, 2, 1, 1, 2, 2, 2, 5, 5]
def baseStart_3047953 : Nat := 118140960795 + 3047953 * 2 ^ 59
def prefixEnd_3047953 : Nat := 4983230072969 + 3 ^ 40 * 3047953 * 2
def baseEnd_3047953 : Nat := 521688300437806201190075

theorem tailTrace_3047953 : CollatzResearch.WordTrace tailWord_3047953 prefixEnd_3047953 521688300437806201190075 := by
  unfold tailWord_3047953
  simp only [CollatzResearch.WordTrace]
  refine ⟨111167978726794304774492513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74111985817862869849661675 111167978726794304774492513)
  ·
    refine ⟨83375984045095728580869385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111167978726794304774492513 83375984045095728580869385)
    ·
      refine ⟨62531988033821796435652039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83375984045095728580869385 62531988033821796435652039)
      ·
        refine ⟨93797982050732694653478059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62531988033821796435652039 93797982050732694653478059)
        ·
          refine ⟨140696973076099041980217089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93797982050732694653478059 140696973076099041980217089)
          ·
            refine ⟨105522729807074281485162817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 140696973076099041980217089 105522729807074281485162817)
            ·
              refine ⟨79142047355305711113872113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 105522729807074281485162817 79142047355305711113872113)
              ·
                refine ⟨59356535516479283335404085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79142047355305711113872113 59356535516479283335404085)
                ·
                  refine ⟨5564675204669932812694133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 59356535516479283335404085 5564675204669932812694133)
                  ·
                    refine ⟨521688300437806201190075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5564675204669932812694133 521688300437806201190075)
                    ·
                      rfl

theorem cell23_3047953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 5].length) (baseStart_3047953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3047953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3047953 prefixEnd_3047953 := by exact prefixLift 3047953
  have htrace : WordTrace (prefixWord ++ tailWord_3047953) baseStart_3047953 baseEnd_3047953 := by
    simpa [prefixWord, tailWord_3047953, baseEnd_3047953] using wordTrace_append hprefix tailTrace_3047953
  have hstable : (prefixWord ++ tailWord_3047953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3047953).length < 2 ^ (prefixWord ++ tailWord_3047953).sum := by decide
  have hdescent : baseEnd_3047953 < baseStart_3047953 := by decide
  rcases family_descends (prefixWord ++ tailWord_3047953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3048000 : List Nat := [2, 1, 1, 2, 2, 2, 3, 2, 4, 4]
def baseStart_3048000 : Nat := 118140960795 + 3048000 * 2 ^ 59
def prefixEnd_3048000 : Nat := 4983230072969 + 3 ^ 40 * 3048000 * 2
def baseEnd_3048000 : Nat := 521696344968059973227503

theorem tailTrace_3048000 : CollatzResearch.WordTrace tailWord_3048000 prefixEnd_3048000 521696344968059973227503 := by
  unfold tailWord_3048000
  simp only [CollatzResearch.WordTrace]
  refine ⟨55584846478812015900726727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74113128638416021200968969 55584846478812015900726727)
  ·
    refine ⟨83377269718218023851090091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55584846478812015900726727 83377269718218023851090091)
    ·
      refine ⟨125065904577327035776635137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83377269718218023851090091 125065904577327035776635137)
      ·
        refine ⟨93799428432995276832476353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125065904577327035776635137 93799428432995276832476353)
        ·
          refine ⟨70349571324746457624357265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93799428432995276832476353 70349571324746457624357265)
          ·
            refine ⟨52762178493559843218267949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70349571324746457624357265 52762178493559843218267949)
            ·
              refine ⟨19785816935084941206850481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52762178493559843218267949 19785816935084941206850481)
              ·
                refine ⟨14839362701313705905137861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19785816935084941206850481 14839362701313705905137861)
                ·
                  refine ⟨2782380506496319857213349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14839362701313705905137861 2782380506496319857213349)
                  ·
                    refine ⟨521696344968059973227503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2782380506496319857213349 521696344968059973227503)
                    ·
                      rfl

theorem cell23_3048000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 2, 4, 4].length) (baseStart_3048000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3048000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3048000 prefixEnd_3048000 := by exact prefixLift 3048000
  have htrace : WordTrace (prefixWord ++ tailWord_3048000) baseStart_3048000 baseEnd_3048000 := by
    simpa [prefixWord, tailWord_3048000, baseEnd_3048000] using wordTrace_append hprefix tailTrace_3048000
  have hstable : (prefixWord ++ tailWord_3048000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3048000).length < 2 ^ (prefixWord ++ tailWord_3048000).sum := by decide
  have hdescent : baseEnd_3048000 < baseStart_3048000 := by decide
  rcases family_descends (prefixWord ++ tailWord_3048000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3048001 : List Nat := [1, 2, 5, 1, 1, 2, 3, 3, 1, 1, 3]
def baseStart_3048001 : Nat := 118140960795 + 3048001 * 2 ^ 59
def prefixEnd_3048001 : Nat := 4983230072969 + 3 ^ 40 * 3048001 * 2
def baseEnd_3048001 : Nat := 1565089548384834415770005

theorem tailTrace_3048001 : CollatzResearch.WordTrace tailWord_3048001 prefixEnd_3048001 1565089548384834415770005 := by
  unfold tailWord_3048001
  simp only [CollatzResearch.WordTrace]
  refine ⟨111169729430620408972239857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74113152953746939314826571 111169729430620408972239857)
  ·
    refine ⟨83377297072965306729179893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111169729430620408972239857 83377297072965306729179893)
    ·
      refine ⟨7816621600590497505860615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 83377297072965306729179893 7816621600590497505860615)
      ·
        refine ⟨11724932400885746258790923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7816621600590497505860615 11724932400885746258790923)
        ·
          refine ⟨17587398601328619388186385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11724932400885746258790923 17587398601328619388186385)
          ·
            refine ⟨13190548950996464541139789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17587398601328619388186385 13190548950996464541139789)
            ·
              refine ⟨4946455856623674202927421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13190548950996464541139789 4946455856623674202927421)
              ·
                refine ⟨1854920946233877826097783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4946455856623674202927421 1854920946233877826097783)
                ·
                  refine ⟨2782381419350816739146675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1854920946233877826097783 2782381419350816739146675)
                  ·
                    refine ⟨4173572129026225108720013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2782381419350816739146675 4173572129026225108720013)
                    ·
                      refine ⟨1565089548384834415770005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4173572129026225108720013 1565089548384834415770005)
                      ·
                        rfl

theorem cell23_3048001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 3, 3, 1, 1, 3].length) (baseStart_3048001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3048001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3048001 prefixEnd_3048001 := by exact prefixLift 3048001
  have htrace : WordTrace (prefixWord ++ tailWord_3048001) baseStart_3048001 baseEnd_3048001 := by
    simpa [prefixWord, tailWord_3048001, baseEnd_3048001] using wordTrace_append hprefix tailTrace_3048001
  have hstable : (prefixWord ++ tailWord_3048001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3048001).length < 2 ^ (prefixWord ++ tailWord_3048001).sum := by decide
  have hdescent : baseEnd_3048001 < baseStart_3048001 := by decide
  rcases family_descends (prefixWord ++ tailWord_3048001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3048007 : List Nat := [1, 1, 4, 1, 4, 1, 2, 3, 1, 1, 4]
def baseStart_3048007 : Nat := 118140960795 + 3048007 * 2 ^ 59
def prefixEnd_3048007 : Nat := 4983230072969 + 3 ^ 40 * 3048007 * 2
def baseEnd_3048007 : Nat := 1565092629268761392294977

theorem tailTrace_3048007 : CollatzResearch.WordTrace tailWord_3048007 prefixEnd_3048007 1565092629268761392294977 := by
  unfold tailWord_3048007
  simp only [CollatzResearch.WordTrace]
  refine ⟨111169948268598671996958275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74113298845732447997972183 111169948268598671996958275)
  ·
    refine ⟨166754922402898007995437413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111169948268598671996958275 166754922402898007995437413)
    ·
      refine ⟨31266547950543376499144515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 166754922402898007995437413 31266547950543376499144515)
      ·
        refine ⟨46899821925815064748716773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31266547950543376499144515 46899821925815064748716773)
        ·
          refine ⟨8793716611090324640384395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46899821925815064748716773 8793716611090324640384395)
          ·
            refine ⟨13190574916635486960576593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8793716611090324640384395 13190574916635486960576593)
            ·
              refine ⟨9892931187476615220432445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13190574916635486960576593 9892931187476615220432445)
              ·
                refine ⟨3709849195303730707662167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9892931187476615220432445 3709849195303730707662167)
                ·
                  refine ⟨5564773792955596061493251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3709849195303730707662167 5564773792955596061493251)
                  ·
                    refine ⟨8347160689433394092239877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5564773792955596061493251 8347160689433394092239877)
                    ·
                      refine ⟨1565092629268761392294977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8347160689433394092239877 1565092629268761392294977)
                      ·
                        rfl

theorem cell23_3048007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 2, 3, 1, 1, 4].length) (baseStart_3048007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3048007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3048007 prefixEnd_3048007 := by exact prefixLift 3048007
  have htrace : WordTrace (prefixWord ++ tailWord_3048007) baseStart_3048007 baseEnd_3048007 := by
    simpa [prefixWord, tailWord_3048007, baseEnd_3048007] using wordTrace_append hprefix tailTrace_3048007
  have hstable : (prefixWord ++ tailWord_3048007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3048007).length < 2 ^ (prefixWord ++ tailWord_3048007).sum := by decide
  have hdescent : baseEnd_3048007 < baseStart_3048007 := by decide
  rcases family_descends (prefixWord ++ tailWord_3048007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3048010 : List Nat := [3, 1, 2, 1, 1, 4, 1, 3, 1, 1, 5]
def baseStart_3048010 : Nat := 118140960795 + 3048010 * 2 ^ 59
def prefixEnd_3048010 : Nat := 4983230072969 + 3 ^ 40 * 3048010 * 2
def baseEnd_3048010 : Nat := 1565094169710724880557463

theorem tailTrace_3048010 : CollatzResearch.WordTrace tailWord_3048010 prefixEnd_3048010 1565094169710724880557463 := by
  unfold tailWord_3048010
  simp only [CollatzResearch.WordTrace]
  refine ⟨27792514421896950877329371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74113371791725202339544989 27792514421896950877329371)
  ·
    refine ⟨41688771632845426315994057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27792514421896950877329371 41688771632845426315994057)
    ·
      refine ⟨31266578724634069736995543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41688771632845426315994057 31266578724634069736995543)
      ·
        refine ⟨46899868086951104605493315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31266578724634069736995543 46899868086951104605493315)
        ·
          refine ⟨70349802130426656908239973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46899868086951104605493315 70349802130426656908239973)
          ·
            refine ⟨13190587899454998170294995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 70349802130426656908239973 13190587899454998170294995)
            ·
              refine ⟨19785881849182497255442493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13190587899454998170294995 19785881849182497255442493)
              ·
                refine ⟨7419705693443436470790935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19785881849182497255442493 7419705693443436470790935)
                ·
                  refine ⟨11129558540165154706186403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7419705693443436470790935 11129558540165154706186403)
                  ·
                    refine ⟨16694337810247732059279605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11129558540165154706186403 16694337810247732059279605)
                    ·
                      refine ⟨1565094169710724880557463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16694337810247732059279605 1565094169710724880557463)
                      ·
                        rfl

theorem cell23_3048010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 3, 1, 1, 5].length) (baseStart_3048010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3048010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3048010 prefixEnd_3048010 := by exact prefixLift 3048010
  have htrace : WordTrace (prefixWord ++ tailWord_3048010) baseStart_3048010 baseEnd_3048010 := by
    simpa [prefixWord, tailWord_3048010, baseEnd_3048010] using wordTrace_append hprefix tailTrace_3048010
  have hstable : (prefixWord ++ tailWord_3048010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3048010).length < 2 ^ (prefixWord ++ tailWord_3048010).sum := by decide
  have hdescent : baseEnd_3048010 < baseStart_3048010 := by decide
  rcases family_descends (prefixWord ++ tailWord_3048010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3048020 : List Nat := [2, 4, 1, 1, 1, 3, 1, 2, 1, 1, 6]
def baseStart_3048020 : Nat := 118140960795 + 3048020 * 2 ^ 59
def prefixEnd_3048020 : Nat := 4983230072969 + 3 ^ 40 * 3048020 * 2
def baseEnd_3048020 : Nat := 1565099304517269841432417

theorem tailTrace_3048020 : CollatzResearch.WordTrace tailWord_3048020 prefixEnd_3048020 1565099304517269841432417 := by
  unfold tailWord_3048020
  simp only [CollatzResearch.WordTrace]
  refine ⟨55585211208775787608590757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74113614945034383478121009 55585211208775787608590757)
  ·
    refine ⟨10422227101645460176610767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55585211208775787608590757 10422227101645460176610767)
    ·
      refine ⟨15633340652468190264916151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10422227101645460176610767 15633340652468190264916151)
      ·
        refine ⟨23450010978702285397374227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15633340652468190264916151 23450010978702285397374227)
        ·
          refine ⟨35175016468053428096061341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23450010978702285397374227 35175016468053428096061341)
          ·
            refine ⟨13190631175520035536023003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35175016468053428096061341 13190631175520035536023003)
            ·
              refine ⟨19785946763280053304034505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13190631175520035536023003 19785946763280053304034505)
              ·
                refine ⟨14839460072460039978025879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19785946763280053304034505 14839460072460039978025879)
                ·
                  refine ⟨22259190108690059967038819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14839460072460039978025879 22259190108690059967038819)
                  ·
                    refine ⟨33388785163035089950558229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22259190108690059967038819 33388785163035089950558229)
                    ·
                      refine ⟨1565099304517269841432417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 33388785163035089950558229 1565099304517269841432417)
                      ·
                        rfl

theorem cell23_3048020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 2, 1, 1, 6].length) (baseStart_3048020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3048020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3048020 prefixEnd_3048020 := by exact prefixLift 3048020
  have htrace : WordTrace (prefixWord ++ tailWord_3048020) baseStart_3048020 baseEnd_3048020 := by
    simpa [prefixWord, tailWord_3048020, baseEnd_3048020] using wordTrace_append hprefix tailTrace_3048020
  have hstable : (prefixWord ++ tailWord_3048020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3048020).length < 2 ^ (prefixWord ++ tailWord_3048020).sum := by decide
  have hdescent : baseEnd_3048020 < baseStart_3048020 := by decide
  rcases family_descends (prefixWord ++ tailWord_3048020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3048024 : List Nat := [2, 1, 2, 2, 1, 2, 5, 1, 3, 2, 2]
def baseStart_3048024 : Nat := 118140960795 + 3048024 * 2 ^ 59
def prefixEnd_3048024 : Nat := 4983230072969 + 3 ^ 40 * 3048024 * 2
def baseEnd_3048024 : Nat := 1565101358439887825782399

theorem tailTrace_3048024 : CollatzResearch.WordTrace tailWord_3048024 prefixEnd_3048024 1565101358439887825782399 := by
  unfold tailWord_3048024
  simp only [CollatzResearch.WordTrace]
  refine ⟨55585284154768541950163563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74113712206358055933551417 55585284154768541950163563)
  ·
    refine ⟨83377926232152812925245345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55585284154768541950163563 83377926232152812925245345)
    ·
      refine ⟨62533444674114609693934009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83377926232152812925245345 62533444674114609693934009)
      ·
        refine ⟨46900083505585957270450507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62533444674114609693934009 46900083505585957270450507)
        ·
          refine ⟨70350125258378935905675761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46900083505585957270450507 70350125258378935905675761)
          ·
            refine ⟨52762593943784201929256821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70350125258378935905675761 52762593943784201929256821)
            ·
              refine ⟨4946493182229768930867827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 52762593943784201929256821 4946493182229768930867827)
              ·
                refine ⟨7419739773344653396301741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4946493182229768930867827 7419739773344653396301741)
                ·
                  refine ⟨2782402415004245023613153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7419739773344653396301741 2782402415004245023613153)
                  ·
                    refine ⟨2086801811253183767709865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2782402415004245023613153 2086801811253183767709865)
                    ·
                      refine ⟨1565101358439887825782399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2086801811253183767709865 1565101358439887825782399)
                      ·
                        rfl

theorem cell23_3048024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 5, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 5, 1, 3, 2, 2].length) (baseStart_3048024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3048024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3048024 prefixEnd_3048024 := by exact prefixLift 3048024
  have htrace : WordTrace (prefixWord ++ tailWord_3048024) baseStart_3048024 baseEnd_3048024 := by
    simpa [prefixWord, tailWord_3048024, baseEnd_3048024] using wordTrace_append hprefix tailTrace_3048024
  have hstable : (prefixWord ++ tailWord_3048024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3048024).length < 2 ^ (prefixWord ++ tailWord_3048024).sum := by decide
  have hdescent : baseEnd_3048024 < baseStart_3048024 := by decide
  rcases family_descends (prefixWord ++ tailWord_3048024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3048043 : List Nat := [1, 1, 1, 1, 2, 2, 1, 3, 4, 7]
def baseStart_3048043 : Nat := 118140960795 + 3048043 * 2 ^ 59
def prefixEnd_3048043 : Nat := 4983230072969 + 3 ^ 40 * 3048043 * 2
def baseEnd_3048043 : Nat := 521703704857441083814937

theorem tailTrace_3048043 : CollatzResearch.WordTrace tailWord_3048043 prefixEnd_3048043 521703704857441083814937 := by
  unfold tailWord_3048043
  simp only [CollatzResearch.WordTrace]
  refine ⟨111171261296468250145268783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74114174197645500096845855 111171261296468250145268783)
  ·
    refine ⟨166756891944702375217903175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111171261296468250145268783 166756891944702375217903175)
    ·
      refine ⟨250135337917053562826854763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166756891944702375217903175 250135337917053562826854763)
      ·
        refine ⟨375203006875580344240282145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 250135337917053562826854763 375203006875580344240282145)
        ·
          refine ⟨281402255156685258180211609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 375203006875580344240282145 281402255156685258180211609)
          ·
            refine ⟨211051691367513943635158707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 281402255156685258180211609 211051691367513943635158707)
            ·
              refine ⟨316577537051270915452738061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 211051691367513943635158707 316577537051270915452738061)
              ·
                refine ⟨118716576394226593294776773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 316577537051270915452738061 118716576394226593294776773)
                ·
                  refine ⟨22259358073917486242770645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 118716576394226593294776773 22259358073917486242770645)
                  ·
                    refine ⟨521703704857441083814937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 22259358073917486242770645 521703704857441083814937)
                    ·
                      rfl

theorem cell23_3048043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 3, 4, 7].length) (baseStart_3048043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3048043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3048043 prefixEnd_3048043 := by exact prefixLift 3048043
  have htrace : WordTrace (prefixWord ++ tailWord_3048043) baseStart_3048043 baseEnd_3048043 := by
    simpa [prefixWord, tailWord_3048043, baseEnd_3048043] using wordTrace_append hprefix tailTrace_3048043
  have hstable : (prefixWord ++ tailWord_3048043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3048043).length < 2 ^ (prefixWord ++ tailWord_3048043).sum := by decide
  have hdescent : baseEnd_3048043 < baseStart_3048043 := by decide
  rcases family_descends (prefixWord ++ tailWord_3048043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3048054 : List Nat := [5, 1, 1, 2, 3, 1, 1, 2, 1, 2, 4]
def baseStart_3048054 : Nat := 118140960795 + 3048054 * 2 ^ 59
def prefixEnd_3048054 : Nat := 4983230072969 + 3 ^ 40 * 3048054 * 2
def baseEnd_3048054 : Nat := 1565116762859522708407261

theorem tailTrace_3048054 : CollatzResearch.WordTrace tailWord_3048054 prefixEnd_3048054 1565116762859522708407261 := by
  unfold tailWord_3048054
  simp only [CollatzResearch.WordTrace]
  refine ⟨6948228906214274938994951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 74114441666285599349279477 6948228906214274938994951)
  ·
    refine ⟨10422343359321412408492427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6948228906214274938994951 10422343359321412408492427)
    ·
      refine ⟨15633515038982118612738641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10422343359321412408492427 15633515038982118612738641)
      ·
        refine ⟨11725136279236588959553981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15633515038982118612738641 11725136279236588959553981)
        ·
          refine ⟨4396926104713720859832743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11725136279236588959553981 4396926104713720859832743)
          ·
            refine ⟨6595389157070581289749115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4396926104713720859832743 6595389157070581289749115)
            ·
              refine ⟨9893083735605871934623673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6595389157070581289749115 9893083735605871934623673)
              ·
                refine ⟨7419812801704403950967755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9893083735605871934623673 7419812801704403950967755)
                ·
                  refine ⟨11129719202556605926451633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7419812801704403950967755 11129719202556605926451633)
                  ·
                    refine ⟨8347289401917454444838725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11129719202556605926451633 8347289401917454444838725)
                    ·
                      refine ⟨1565116762859522708407261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8347289401917454444838725 1565116762859522708407261)
                      ·
                        rfl

theorem cell23_3048054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 1, 2, 1, 2, 4].length) (baseStart_3048054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3048054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3048054 prefixEnd_3048054 := by exact prefixLift 3048054
  have htrace : WordTrace (prefixWord ++ tailWord_3048054) baseStart_3048054 baseEnd_3048054 := by
    simpa [prefixWord, tailWord_3048054, baseEnd_3048054] using wordTrace_append hprefix tailTrace_3048054
  have hstable : (prefixWord ++ tailWord_3048054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3048054).length < 2 ^ (prefixWord ++ tailWord_3048054).sum := by decide
  have hdescent : baseEnd_3048054 < baseStart_3048054 := by decide
  rcases family_descends (prefixWord ++ tailWord_3048054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3048057 : List Nat := [1, 2, 1, 3, 3, 3, 1, 2, 1, 3, 3]
def baseStart_3048057 : Nat := 118140960795 + 3048057 * 2 ^ 59
def prefixEnd_3048057 : Nat := 4983230072969 + 3 ^ 40 * 3048057 * 2
def baseEnd_3048057 : Nat := 1565118303301486196669747

theorem tailTrace_3048057 : CollatzResearch.WordTrace tailWord_3048057 prefixEnd_3048057 1565118303301486196669747 := by
  unfold tailWord_3048057
  simp only [CollatzResearch.WordTrace]
  refine ⟨111171771918417530536278425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74114514612278353690852283 111171771918417530536278425)
  ·
    refine ⟨83378828938813147902208819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111171771918417530536278425 83378828938813147902208819)
    ·
      refine ⟨125068243408219721853313229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83378828938813147902208819 125068243408219721853313229)
      ·
        refine ⟨46900591278082395694992461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 125068243408219721853313229 46900591278082395694992461)
        ·
          refine ⟨17587721729280898385622173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46900591278082395694992461 17587721729280898385622173)
          ·
            refine ⟨6595395648480336894608315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17587721729280898385622173 6595395648480336894608315)
            ·
              refine ⟨9893093472720505341912473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6595395648480336894608315 9893093472720505341912473)
              ·
                refine ⟨7419820104540379006434355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9893093472720505341912473 7419820104540379006434355)
                ·
                  refine ⟨11129730156810568509651533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7419820104540379006434355 11129730156810568509651533)
                  ·
                    refine ⟨4173648808803963191119325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11129730156810568509651533 4173648808803963191119325)
                    ·
                      refine ⟨1565118303301486196669747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4173648808803963191119325 1565118303301486196669747)
                      ·
                        rfl

theorem cell23_3048057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 1, 2, 1, 3, 3].length) (baseStart_3048057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3048057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3048057 prefixEnd_3048057 := by exact prefixLift 3048057
  have htrace : WordTrace (prefixWord ++ tailWord_3048057) baseStart_3048057 baseEnd_3048057 := by
    simpa [prefixWord, tailWord_3048057, baseEnd_3048057] using wordTrace_append hprefix tailTrace_3048057
  have hstable : (prefixWord ++ tailWord_3048057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3048057).length < 2 ^ (prefixWord ++ tailWord_3048057).sum := by decide
  have hdescent : baseEnd_3048057 < baseStart_3048057 := by decide
  rcases family_descends (prefixWord ++ tailWord_3048057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3048061 : List Nat := [1, 4, 1, 1, 5, 1, 3, 1, 1, 2, 3]
def baseStart_3048061 : Nat := 118140960795 + 3048061 * 2 ^ 59
def prefixEnd_3048061 : Nat := 4983230072969 + 3 ^ 40 * 3048061 * 2
def baseEnd_3048061 : Nat := 1565120357224104181019729

theorem tailTrace_3048061 : CollatzResearch.WordTrace tailWord_3048061 prefixEnd_3048061 1565120357224104181019729 := by
  unfold tailWord_3048061
  simp only [CollatzResearch.WordTrace]
  refine ⟨111171917810403039219424037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74114611873602026146282691 111171917810403039219424037)
  ·
    refine ⟨20844734589450569853642007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 111171917810403039219424037 20844734589450569853642007)
    ·
      refine ⟨31267101884175854780463011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20844734589450569853642007 31267101884175854780463011)
      ·
        refine ⟨46900652826263782170694517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31267101884175854780463011 46900652826263782170694517)
        ·
          refine ⟨4396936202462229578502611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 46900652826263782170694517 4396936202462229578502611)
          ·
            refine ⟨6595404303693344367753917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4396936202462229578502611 6595404303693344367753917)
            ·
              refine ⟨2473276613885004137907719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6595404303693344367753917 2473276613885004137907719)
              ·
                refine ⟨3709914920827506206861579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2473276613885004137907719 3709914920827506206861579)
                ·
                  refine ⟨5564872381241259310292369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3709914920827506206861579 5564872381241259310292369)
                  ·
                    refine ⟨4173654285930944482719277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5564872381241259310292369 4173654285930944482719277)
                    ·
                      refine ⟨1565120357224104181019729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4173654285930944482719277 1565120357224104181019729)
                      ·
                        rfl

theorem cell23_3048061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 3, 1, 1, 2, 3].length) (baseStart_3048061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3048061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3048061 prefixEnd_3048061 := by exact prefixLift 3048061
  have htrace : WordTrace (prefixWord ++ tailWord_3048061) baseStart_3048061 baseEnd_3048061 := by
    simpa [prefixWord, tailWord_3048061, baseEnd_3048061] using wordTrace_append hprefix tailTrace_3048061
  have hstable : (prefixWord ++ tailWord_3048061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3048061).length < 2 ^ (prefixWord ++ tailWord_3048061).sum := by decide
  have hdescent : baseEnd_3048061 < baseStart_3048061 := by decide
  rcases family_descends (prefixWord ++ tailWord_3048061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3048114 : List Nat := [3, 2, 1, 1, 1, 2, 1, 4, 4, 2, 2]
def baseStart_3048114 : Nat := 118140960795 + 3048114 * 2 ^ 59
def prefixEnd_3048114 : Nat := 4983230072969 + 3 ^ 40 * 3048114 * 2
def baseEnd_3048114 : Nat := 1565147571698792473656985

theorem tailTrace_3048114 : CollatzResearch.WordTrace tailWord_3048114 prefixEnd_3048114 1565147571698792473656985 := by
  unfold tailWord_3048114
  simp only [CollatzResearch.WordTrace]
  refine ⟨27793462719802757317775849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74115900586140686180735597 27793462719802757317775849)
  ·
    refine ⟨20845097039852067988331887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27793462719802757317775849 20845097039852067988331887)
    ·
      refine ⟨31267645559778101982497831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20845097039852067988331887 31267645559778101982497831)
      ·
        refine ⟨46901468339667152973746747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31267645559778101982497831 46901468339667152973746747)
        ·
          refine ⟨70352202509500729460620121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46901468339667152973746747 70352202509500729460620121)
          ·
            refine ⟨52764151882125547095465091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70352202509500729460620121 52764151882125547095465091)
            ·
              refine ⟨79146227823188320643197637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52764151882125547095465091 79146227823188320643197637)
              ·
                refine ⟨14839917716847810120599557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 79146227823188320643197637 14839917716847810120599557)
                ·
                  refine ⟨2782484571908964397612417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14839917716847810120599557 2782484571908964397612417)
                  ·
                    refine ⟨2086863428931723298209313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2782484571908964397612417 2086863428931723298209313)
                    ·
                      refine ⟨1565147571698792473656985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2086863428931723298209313 1565147571698792473656985)
                      ·
                        rfl

theorem cell23_3048114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 4, 4, 2, 2].length) (baseStart_3048114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3048114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3048114 prefixEnd_3048114 := by exact prefixLift 3048114
  have htrace : WordTrace (prefixWord ++ tailWord_3048114) baseStart_3048114 baseEnd_3048114 := by
    simpa [prefixWord, tailWord_3048114, baseEnd_3048114] using wordTrace_append hprefix tailTrace_3048114
  have hstable : (prefixWord ++ tailWord_3048114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3048114).length < 2 ^ (prefixWord ++ tailWord_3048114).sum := by decide
  have hdescent : baseEnd_3048114 < baseStart_3048114 := by decide
  rcases family_descends (prefixWord ++ tailWord_3048114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3048148 : List Nat := [2, 4, 1, 3, 2, 2, 1, 1, 1, 4, 2]
def baseStart_3048148 : Nat := 118140960795 + 3048148 * 2 ^ 59
def prefixEnd_3048148 : Nat := 4983230072969 + 3 ^ 40 * 3048148 * 2
def baseEnd_3048148 : Nat := 1565165030041045340631829

theorem tailTrace_3048148 : CollatzResearch.WordTrace tailWord_3048148 prefixEnd_3048148 1565165030041045340631829 := by
  unfold tailWord_3048148
  simp only [CollatzResearch.WordTrace]
  refine ⟨55587545480543926538920549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74116727307391902051894065 55587545480543926538920549)
  ·
    refine ⟨10422664777601986226047603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55587545480543926538920549 10422664777601986226047603)
    ·
      refine ⟨15633997166402979339071405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10422664777601986226047603 15633997166402979339071405)
      ·
        refine ⟨5862748937401117252151777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15633997166402979339071405 5862748937401117252151777)
        ·
          refine ⟨4397061703050837939113833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5862748937401117252151777 4397061703050837939113833)
          ·
            refine ⟨3297796277288128454335375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4397061703050837939113833 3297796277288128454335375)
            ·
              refine ⟨4946694415932192681503063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3297796277288128454335375 4946694415932192681503063)
              ·
                refine ⟨7420041623898289022254595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4946694415932192681503063 7420041623898289022254595)
                ·
                  refine ⟨11130062435847433533381893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7420041623898289022254595 11130062435847433533381893)
                  ·
                    refine ⟨2086886706721393787509105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11130062435847433533381893 2086886706721393787509105)
                    ·
                      refine ⟨1565165030041045340631829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2086886706721393787509105 1565165030041045340631829)
                      ·
                        rfl

theorem cell23_3048148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 2, 1, 1, 1, 4, 2].length) (baseStart_3048148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3048148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3048148 prefixEnd_3048148 := by exact prefixLift 3048148
  have htrace : WordTrace (prefixWord ++ tailWord_3048148) baseStart_3048148 baseEnd_3048148 := by
    simpa [prefixWord, tailWord_3048148, baseEnd_3048148] using wordTrace_append hprefix tailTrace_3048148
  have hstable : (prefixWord ++ tailWord_3048148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3048148).length < 2 ^ (prefixWord ++ tailWord_3048148).sum := by decide
  have hdescent : baseEnd_3048148 < baseStart_3048148 := by decide
  rcases family_descends (prefixWord ++ tailWord_3048148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3048160 : List Nat := [2, 1, 1, 3, 1, 2, 1, 2, 3, 2, 5]
def baseStart_3048160 : Nat := 118140960795 + 3048160 * 2 ^ 59
def prefixEnd_3048160 : Nat := 4983230072969 + 3 ^ 40 * 3048160 * 2
def baseEnd_3048160 : Nat := 1565171191808899293681773

theorem tailTrace_3048160 : CollatzResearch.WordTrace tailWord_3048160 prefixEnd_3048160 1565171191808899293681773 := by
  unfold tailWord_3048160
  simp only [CollatzResearch.WordTrace]
  refine ⟨55587764318522189563638967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74117019091362919418185289 55587764318522189563638967)
  ·
    refine ⟨83381646477783284345458451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55587764318522189563638967 83381646477783284345458451)
    ·
      refine ⟨125072469716674926518187677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83381646477783284345458451 125072469716674926518187677)
      ·
        refine ⟨46902176143753097444320379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 125072469716674926518187677 46902176143753097444320379)
        ·
          refine ⟨70353264215629646166480569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46902176143753097444320379 70353264215629646166480569)
          ·
            refine ⟨52764948161722234624860427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70353264215629646166480569 52764948161722234624860427)
            ·
              refine ⟨79147422242583351937290641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52764948161722234624860427 79147422242583351937290641)
              ·
                refine ⟨59360566681937513952967981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79147422242583351937290641 59360566681937513952967981)
                ·
                  refine ⟨22260212505726567732362993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59360566681937513952967981 22260212505726567732362993)
                  ·
                    refine ⟨16695159379294925799272245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22260212505726567732362993 16695159379294925799272245)
                    ·
                      refine ⟨1565171191808899293681773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16695159379294925799272245 1565171191808899293681773)
                      ·
                        rfl

theorem cell23_3048160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 2, 3, 2, 5].length) (baseStart_3048160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3048160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3048160 prefixEnd_3048160 := by exact prefixLift 3048160
  have htrace : WordTrace (prefixWord ++ tailWord_3048160) baseStart_3048160 baseEnd_3048160 := by
    simpa [prefixWord, tailWord_3048160, baseEnd_3048160] using wordTrace_append hprefix tailTrace_3048160
  have hstable : (prefixWord ++ tailWord_3048160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3048160).length < 2 ^ (prefixWord ++ tailWord_3048160).sum := by decide
  have hdescent : baseEnd_3048160 < baseStart_3048160 := by decide
  rcases family_descends (prefixWord ++ tailWord_3048160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3048194 : List Nat := [3, 4, 1, 1, 1, 3, 1, 1, 1, 2, 5]
def baseStart_3048194 : Nat := 118140960795 + 3048194 * 2 ^ 59
def prefixEnd_3048194 : Nat := 4983230072969 + 3 ^ 40 * 3048194 * 2
def baseEnd_3048194 : Nat := 1565188650151152160656617

theorem tailTrace_3048194 : CollatzResearch.WordTrace tailWord_3048194 prefixEnd_3048194 1565188650151152160656617 := by
  unfold tailWord_3048194
  simp only [CollatzResearch.WordTrace]
  refine ⟨27794192179730300733503909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74117845812614135289343757 27794192179730300733503909)
  ·
    refine ⟨5211411033699431387531983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27794192179730300733503909 5211411033699431387531983)
    ·
      refine ⟨7817116550549147081297975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5211411033699431387531983 7817116550549147081297975)
      ·
        refine ⟨11725674825823720621946963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7817116550549147081297975 11725674825823720621946963)
        ·
          refine ⟨17588512238735580932920445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11725674825823720621946963 17588512238735580932920445)
          ·
            refine ⟨6595692089525842849845167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17588512238735580932920445 6595692089525842849845167)
            ·
              refine ⟨9893538134288764274767751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6595692089525842849845167 9893538134288764274767751)
              ·
                refine ⟨14840307201433146412151627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9893538134288764274767751 14840307201433146412151627)
                ·
                  refine ⟨22260460802149719618227441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14840307201433146412151627 22260460802149719618227441)
                  ·
                    refine ⟨16695345601612289713670581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22260460802149719618227441 16695345601612289713670581)
                    ·
                      refine ⟨1565188650151152160656617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16695345601612289713670581 1565188650151152160656617)
                      ·
                        rfl

theorem cell23_3048194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 1, 1, 1, 2, 5].length) (baseStart_3048194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3048194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3048194 prefixEnd_3048194 := by exact prefixLift 3048194
  have htrace : WordTrace (prefixWord ++ tailWord_3048194) baseStart_3048194 baseEnd_3048194 := by
    simpa [prefixWord, tailWord_3048194, baseEnd_3048194] using wordTrace_append hprefix tailTrace_3048194
  have hstable : (prefixWord ++ tailWord_3048194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3048194).length < 2 ^ (prefixWord ++ tailWord_3048194).sum := by decide
  have hdescent : baseEnd_3048194 < baseStart_3048194 := by decide
  rcases family_descends (prefixWord ++ tailWord_3048194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3048207 : List Nat := [1, 1, 2, 1, 1, 1, 5, 2, 4, 2, 3]
def baseStart_3048207 : Nat := 118140960795 + 3048207 * 2 ^ 59
def prefixEnd_3048207 : Nat := 4983230072969 + 3 ^ 40 * 3048207 * 2
def baseEnd_3048207 : Nat := 1565195325399660609794057

theorem tailTrace_3048207 : CollatzResearch.WordTrace tailWord_3048207 prefixEnd_3048207 1565195325399660609794057 := by
  unfold tailWord_3048207
  simp only [CollatzResearch.WordTrace]
  refine ⟨111177242867874106154238875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74118161911916070769492583 111177242867874106154238875)
  ·
    refine ⟨166765864301811159231358313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111177242867874106154238875 166765864301811159231358313)
    ·
      refine ⟨125074398226358369423518735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166765864301811159231358313 125074398226358369423518735)
      ·
        refine ⟨187611597339537554135278103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125074398226358369423518735 187611597339537554135278103)
        ·
          refine ⟨281417396009306331202917155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 187611597339537554135278103 281417396009306331202917155)
          ·
            refine ⟨422126094013959496804375733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 281417396009306331202917155 422126094013959496804375733)
            ·
              refine ⟨39574321313808702825410225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 422126094013959496804375733 39574321313808702825410225)
              ·
                refine ⟨29680740985356527119057669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39574321313808702825410225 29680740985356527119057669)
                ·
                  refine ⟨5565138934754348834823313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29680740985356527119057669 5565138934754348834823313)
                  ·
                    refine ⟨4173854201065761626117485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5565138934754348834823313 4173854201065761626117485)
                    ·
                      refine ⟨1565195325399660609794057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4173854201065761626117485 1565195325399660609794057)
                      ·
                        rfl

theorem cell23_3048207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 2, 4, 2, 3].length) (baseStart_3048207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3048207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3048207 prefixEnd_3048207 := by exact prefixLift 3048207
  have htrace : WordTrace (prefixWord ++ tailWord_3048207) baseStart_3048207 baseEnd_3048207 := by
    simpa [prefixWord, tailWord_3048207, baseEnd_3048207] using wordTrace_append hprefix tailTrace_3048207
  have hstable : (prefixWord ++ tailWord_3048207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3048207).length < 2 ^ (prefixWord ++ tailWord_3048207).sum := by decide
  have hdescent : baseEnd_3048207 < baseStart_3048207 := by decide
  rcases family_descends (prefixWord ++ tailWord_3048207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3048224 : List Nat := [2, 1, 1, 5, 1, 2, 1, 3, 2, 2, 3]
def baseStart_3048224 : Nat := 118140960795 + 3048224 * 2 ^ 59
def prefixEnd_3048224 : Nat := 4983230072969 + 3 ^ 40 * 3048224 * 2
def baseEnd_3048224 : Nat := 1565204054570787043281479

theorem tailTrace_3048224 : CollatzResearch.WordTrace tailWord_3048224 prefixEnd_3048224 1565204054570787043281479 := by
  unfold tailWord_3048224
  simp only [CollatzResearch.WordTrace]
  refine ⟨55588931454406259028803863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74118575272541678705071817 55588931454406259028803863)
  ·
    refine ⟨83383397181609388543205795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55588931454406259028803863 83383397181609388543205795)
    ·
      refine ⟨125075095772414082814808693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83383397181609388543205795 125075095772414082814808693)
      ·
        refine ⟨11725790228663820263888315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 125075095772414082814808693 11725790228663820263888315)
        ·
          refine ⟨17588685342995730395832473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11725790228663820263888315 17588685342995730395832473)
          ·
            refine ⟨13191514007246797796874355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17588685342995730395832473 13191514007246797796874355)
            ·
              refine ⟨19787271010870196695311533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13191514007246797796874355 19787271010870196695311533)
              ·
                refine ⟨7420226629076323760741825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19787271010870196695311533 7420226629076323760741825)
                ·
                  refine ⟨5565169971807242820556369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7420226629076323760741825 5565169971807242820556369)
                  ·
                    refine ⟨4173877478855432115417277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5565169971807242820556369 4173877478855432115417277)
                    ·
                      refine ⟨1565204054570787043281479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4173877478855432115417277 1565204054570787043281479)
                      ·
                        rfl

theorem cell23_3048224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 3, 2, 2, 3].length) (baseStart_3048224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3048224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3048224 prefixEnd_3048224 := by exact prefixLift 3048224
  have htrace : WordTrace (prefixWord ++ tailWord_3048224) baseStart_3048224 baseEnd_3048224 := by
    simpa [prefixWord, tailWord_3048224, baseEnd_3048224] using wordTrace_append hprefix tailTrace_3048224
  have hstable : (prefixWord ++ tailWord_3048224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3048224).length < 2 ^ (prefixWord ++ tailWord_3048224).sum := by decide
  have hdescent : baseEnd_3048224 < baseStart_3048224 := by decide
  rcases family_descends (prefixWord ++ tailWord_3048224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3048264 : List Nat := [2, 1, 3, 1, 1, 3, 2, 2, 1, 5, 2]
def baseStart_3048264 : Nat := 118140960795 + 3048264 * 2 ^ 59
def prefixEnd_3048264 : Nat := 4983230072969 + 3 ^ 40 * 3048264 * 2
def baseEnd_3048264 : Nat := 1565224593796966886781295

theorem tailTrace_3048264 : CollatzResearch.WordTrace tailWord_3048264 prefixEnd_3048264 1565224593796966886781295 := by
  unfold tailWord_3048264
  simp only [CollatzResearch.WordTrace]
  refine ⟨55589660914333802444531923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74119547885778403259375897 55589660914333802444531923)
  ·
    refine ⟨83384491371500703666797885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55589660914333802444531923 83384491371500703666797885)
    ·
      refine ⟨31269184264312763875049207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83384491371500703666797885 31269184264312763875049207)
      ·
        refine ⟨46903776396469145812573811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31269184264312763875049207 46903776396469145812573811)
        ·
          refine ⟨70355664594703718718860717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46903776396469145812573811 70355664594703718718860717)
          ·
            refine ⟨26383374223013894519572769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70355664594703718718860717 26383374223013894519572769)
            ·
              refine ⟨19787530667260420889679577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26383374223013894519572769 19787530667260420889679577)
              ·
                refine ⟨14840648000445315667259683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19787530667260420889679577 14840648000445315667259683)
                ·
                  refine ⟨22260972000667973500889525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14840648000445315667259683 22260972000667973500889525)
                  ·
                    refine ⟨2086966125062622515708393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 22260972000667973500889525 2086966125062622515708393)
                    ·
                      refine ⟨1565224593796966886781295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2086966125062622515708393 1565224593796966886781295)
                      ·
                        rfl

theorem cell23_3048264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 2, 1, 5, 2].length) (baseStart_3048264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3048264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3048264 prefixEnd_3048264 := by exact prefixLift 3048264
  have htrace : WordTrace (prefixWord ++ tailWord_3048264) baseStart_3048264 baseEnd_3048264 := by
    simpa [prefixWord, tailWord_3048264, baseEnd_3048264] using wordTrace_append hprefix tailTrace_3048264
  have hstable : (prefixWord ++ tailWord_3048264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3048264).length < 2 ^ (prefixWord ++ tailWord_3048264).sum := by decide
  have hdescent : baseEnd_3048264 < baseStart_3048264 := by decide
  rcases family_descends (prefixWord ++ tailWord_3048264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3048274 : List Nat := [3, 2, 2, 1, 1, 2, 2, 4, 1, 5]
def baseStart_3048274 : Nat := 118140960795 + 3048274 * 2 ^ 59
def prefixEnd_3048274 : Nat := 4983230072969 + 3 ^ 40 * 3048274 * 2
def baseEnd_3048274 : Nat := 521743242867837282552083

theorem tailTrace_3048274 : CollatzResearch.WordTrace tailWord_3048274 prefixEnd_3048274 521743242867837282552083 := by
  unfold tailWord_3048274
  simp only [CollatzResearch.WordTrace]
  refine ⟨27794921639657844149231969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74119791039087584397951917 27794921639657844149231969)
  ·
    refine ⟨20846191229743383111923977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27794921639657844149231969 20846191229743383111923977)
    ·
      refine ⟨15634643422307537333942983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20846191229743383111923977 15634643422307537333942983)
      ·
        refine ⟨23451965133461306000914475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15634643422307537333942983 23451965133461306000914475)
        ·
          refine ⟨35177947700191959001371713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23451965133461306000914475 35177947700191959001371713)
          ·
            refine ⟨26383460775143969251028785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35177947700191959001371713 26383460775143969251028785)
            ·
              refine ⟨19787595581357976938271589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26383460775143969251028785 19787595581357976938271589)
              ·
                refine ⟨3710174171504620675925923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19787595581357976938271589 3710174171504620675925923)
                ·
                  refine ⟨5565261257256931013888885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3710174171504620675925923 5565261257256931013888885)
                  ·
                    refine ⟨521743242867837282552083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5565261257256931013888885 521743242867837282552083)
                    ·
                      rfl

theorem cell23_3048274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 4, 1, 5].length) (baseStart_3048274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3048274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3048274 prefixEnd_3048274 := by exact prefixLift 3048274
  have htrace : WordTrace (prefixWord ++ tailWord_3048274) baseStart_3048274 baseEnd_3048274 := by
    simpa [prefixWord, tailWord_3048274, baseEnd_3048274] using wordTrace_append hprefix tailTrace_3048274
  have hstable : (prefixWord ++ tailWord_3048274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3048274).length < 2 ^ (prefixWord ++ tailWord_3048274).sum := by decide
  have hdescent : baseEnd_3048274 < baseStart_3048274 := by decide
  rcases family_descends (prefixWord ++ tailWord_3048274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3048281 : List Nat := [1, 2, 1, 2, 2, 4, 3, 1, 2, 3, 2]
def baseStart_3048281 : Nat := 118140960795 + 3048281 * 2 ^ 59
def prefixEnd_3048281 : Nat := 4983230072969 + 3 ^ 40 * 3048281 * 2
def baseEnd_3048281 : Nat := 1565233322968093320268717

theorem tailTrace_3048281 : CollatzResearch.WordTrace tailWord_3048281 prefixEnd_3048281 1565233322968093320268717 := by
  unfold tailWord_3048281
  simp only [CollatzResearch.WordTrace]
  refine ⟨111179941869606016792432697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74119961246404011194955131 111179941869606016792432697)
  ·
    refine ⟨83384956402204512594324523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111179941869606016792432697 83384956402204512594324523)
    ·
      refine ⟨125077434603306768891486785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83384956402204512594324523 125077434603306768891486785)
      ·
        refine ⟨93808075952480076668615089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125077434603306768891486785 93808075952480076668615089)
        ·
          refine ⟨70356056964360057501461317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93808075952480076668615089 70356056964360057501461317)
          ·
            refine ⟨13191760680817510781523997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 70356056964360057501461317 13191760680817510781523997)
            ·
              refine ⟨4946910255306566543071499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13191760680817510781523997 4946910255306566543071499)
              ·
                refine ⟨7420365382959849814607249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4946910255306566543071499 7420365382959849814607249)
                ·
                  refine ⟨5565274037219887360955437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7420365382959849814607249 5565274037219887360955437)
                  ·
                    refine ⟨2086977763957457760358289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5565274037219887360955437 2086977763957457760358289)
                    ·
                      refine ⟨1565233322968093320268717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2086977763957457760358289 1565233322968093320268717)
                      ·
                        rfl

theorem cell23_3048281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 3, 1, 2, 3, 2].length) (baseStart_3048281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3048281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3048281 prefixEnd_3048281 := by exact prefixLift 3048281
  have htrace : WordTrace (prefixWord ++ tailWord_3048281) baseStart_3048281 baseEnd_3048281 := by
    simpa [prefixWord, tailWord_3048281, baseEnd_3048281] using wordTrace_append hprefix tailTrace_3048281
  have hstable : (prefixWord ++ tailWord_3048281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3048281).length < 2 ^ (prefixWord ++ tailWord_3048281).sum := by decide
  have hdescent : baseEnd_3048281 < baseStart_3048281 := by decide
  rcases family_descends (prefixWord ++ tailWord_3048281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3048287 : List Nat := [1, 1, 2, 3, 1, 3, 1, 4, 1, 6]
def baseStart_3048287 : Nat := 118140960795 + 3048287 * 2 ^ 59
def prefixEnd_3048287 : Nat := 4983230072969 + 3 ^ 40 * 3048287 * 2
def baseEnd_3048287 : Nat := 521745467950673432264563

theorem tailTrace_3048287 : CollatzResearch.WordTrace tailWord_3048287 prefixEnd_3048287 521745467950673432264563 := by
  unfold tailWord_3048287
  simp only [CollatzResearch.WordTrace]
  refine ⟨111180160707584279817151115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74120107138389519878100743 111180160707584279817151115)
  ·
    refine ⟨166770241061376419725726673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111180160707584279817151115 166770241061376419725726673)
    ·
      refine ⟨125077680796032314794295005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166770241061376419725726673 125077680796032314794295005)
      ·
        refine ⟨46904130298512118047860627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 125077680796032314794295005 46904130298512118047860627)
        ·
          refine ⟨70356195447768177071790941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46904130298512118047860627 70356195447768177071790941)
          ·
            refine ⟨26383573292913066401921603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70356195447768177071790941 26383573292913066401921603)
            ·
              refine ⟨39575359939369599602882405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26383573292913066401921603 39575359939369599602882405)
              ·
                refine ⟨7420379988631799925540451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39575359939369599602882405 7420379988631799925540451)
                ·
                  refine ⟨11130569982947699888310677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7420379988631799925540451 11130569982947699888310677)
                  ·
                    refine ⟨521745467950673432264563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11130569982947699888310677 521745467950673432264563)
                    ·
                      rfl

theorem cell23_3048287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 4, 1, 6].length) (baseStart_3048287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3048287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3048287 prefixEnd_3048287 := by exact prefixLift 3048287
  have htrace : WordTrace (prefixWord ++ tailWord_3048287) baseStart_3048287 baseEnd_3048287 := by
    simpa [prefixWord, tailWord_3048287, baseEnd_3048287] using wordTrace_append hprefix tailTrace_3048287
  have hstable : (prefixWord ++ tailWord_3048287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3048287).length < 2 ^ (prefixWord ++ tailWord_3048287).sum := by decide
  have hdescent : baseEnd_3048287 < baseStart_3048287 := by decide
  rcases family_descends (prefixWord ++ tailWord_3048287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3048288 : List Nat := [2, 1, 1, 3, 3, 1, 4, 3, 1, 1, 3]
def baseStart_3048288 : Nat := 118140960795 + 3048288 * 2 ^ 59
def prefixEnd_3048288 : Nat := 4983230072969 + 3 ^ 40 * 3048288 * 2
def baseEnd_3048288 : Nat := 1565236917332674792881185

theorem tailTrace_3048288 : CollatzResearch.WordTrace tailWord_3048288 prefixEnd_3048288 1565236917332674792881185 := by
  unfold tailWord_3048288
  simp only [CollatzResearch.WordTrace]
  refine ⟨55590098590290328493968759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74120131453720437991958345 55590098590290328493968759)
  ·
    refine ⟨83385147885435492740953139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55590098590290328493968759 83385147885435492740953139)
    ·
      refine ⟨125077721828153239111429709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83385147885435492740953139 125077721828153239111429709)
      ·
        refine ⟨46904145685557464666786141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 125077721828153239111429709 46904145685557464666786141)
        ·
          refine ⟨17589054632084049250044803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46904145685557464666786141 17589054632084049250044803)
          ·
            refine ⟨26383581948126073875067205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17589054632084049250044803 26383581948126073875067205)
            ·
              refine ⟨4946921615273638851575101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26383581948126073875067205 4946921615273638851575101)
              ·
                refine ⟨1855095605727614569340663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4946921615273638851575101 1855095605727614569340663)
                ·
                  refine ⟨2782643408591421854010995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1855095605727614569340663 2782643408591421854010995)
                  ·
                    refine ⟨4173965112887132781016493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2782643408591421854010995 4173965112887132781016493)
                    ·
                      refine ⟨1565236917332674792881185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4173965112887132781016493 1565236917332674792881185)
                      ·
                        rfl

theorem cell23_3048288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 4, 3, 1, 1, 3].length) (baseStart_3048288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3048288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3048288 prefixEnd_3048288 := by exact prefixLift 3048288
  have htrace : WordTrace (prefixWord ++ tailWord_3048288) baseStart_3048288 baseEnd_3048288 := by
    simpa [prefixWord, tailWord_3048288, baseEnd_3048288] using wordTrace_append hprefix tailTrace_3048288
  have hstable : (prefixWord ++ tailWord_3048288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3048288).length < 2 ^ (prefixWord ++ tailWord_3048288).sum := by decide
  have hdescent : baseEnd_3048288 < baseStart_3048288 := by decide
  rcases family_descends (prefixWord ++ tailWord_3048288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3048291 : List Nat := [1, 1, 1, 5, 3, 1, 4, 1, 1, 5]
def baseStart_3048291 : Nat := 118140960795 + 3048291 * 2 ^ 59
def prefixEnd_3048291 : Nat := 4983230072969 + 3 ^ 40 * 3048291 * 2
def baseEnd_3048291 : Nat := 521746152591546093714557

theorem tailTrace_3048291 : CollatzResearch.WordTrace tailWord_3048291 prefixEnd_3048291 521746152591546093714557 := by
  unfold tailWord_3048291
  simp only [CollatzResearch.WordTrace]
  refine ⟨111180306599569788500296727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74120204399713192333531151 111180306599569788500296727)
  ·
    refine ⟨166770459899354682750445091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111180306599569788500296727 166770459899354682750445091)
    ·
      refine ⟨250155689849032024125667637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166770459899354682750445091 250155689849032024125667637)
      ·
        refine ⟨23452095923346752261781341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 250155689849032024125667637 23452095923346752261781341)
        ·
          refine ⟨8794535971255032098168003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23452095923346752261781341 8794535971255032098168003)
          ·
            refine ⟨13191803956882548147252005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8794535971255032098168003 13191803956882548147252005)
            ·
              refine ⟨2473463241915477777609751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13191803956882548147252005 2473463241915477777609751)
              ·
                refine ⟨3710194862873216666414627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2473463241915477777609751 3710194862873216666414627)
                ·
                  refine ⟨5565292294309824999621941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3710194862873216666414627 5565292294309824999621941)
                  ·
                    refine ⟨521746152591546093714557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5565292294309824999621941 521746152591546093714557)
                    ·
                      rfl

theorem cell23_3048291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 4, 1, 1, 5].length) (baseStart_3048291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3048291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3048291 prefixEnd_3048291 := by exact prefixLift 3048291
  have htrace : WordTrace (prefixWord ++ tailWord_3048291) baseStart_3048291 baseEnd_3048291 := by
    simpa [prefixWord, tailWord_3048291, baseEnd_3048291] using wordTrace_append hprefix tailTrace_3048291
  have hstable : (prefixWord ++ tailWord_3048291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3048291).length < 2 ^ (prefixWord ++ tailWord_3048291).sum := by decide
  have hdescent : baseEnd_3048291 < baseStart_3048291 := by decide
  rcases family_descends (prefixWord ++ tailWord_3048291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3048307 : List Nat := [1, 1, 1, 2, 2, 1, 4, 2, 3, 2, 4]
def baseStart_3048307 : Nat := 118140960795 + 3048307 * 2 ^ 59
def prefixEnd_3048307 : Nat := 4983230072969 + 3 ^ 40 * 3048307 * 2
def baseEnd_3048307 : Nat := 1565246673465110218543597

theorem tailTrace_3048307 : CollatzResearch.WordTrace tailWord_3048307 prefixEnd_3048307 1565246673465110218543597 := by
  unfold tailWord_3048307
  simp only [CollatzResearch.WordTrace]
  refine ⟨111180890167511823232879175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74120593445007882155252783 111180890167511823232879175)
  ·
    refine ⟨166771335251267734849318763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111180890167511823232879175 166771335251267734849318763)
    ·
      refine ⟨250157002876901602273978145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166771335251267734849318763 250157002876901602273978145)
      ·
        refine ⟨187617752157676201705483609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 250157002876901602273978145 187617752157676201705483609)
        ·
          refine ⟨140713314118257151279112707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 187617752157676201705483609 140713314118257151279112707)
          ·
            refine ⟨211069971177385726918669061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140713314118257151279112707 211069971177385726918669061)
            ·
              refine ⟨39575619595759823797250449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 211069971177385726918669061 39575619595759823797250449)
              ·
                refine ⟨29681714696819867847937837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39575619595759823797250449 29681714696819867847937837)
                ·
                  refine ⟨11130643011307450442976689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29681714696819867847937837 11130643011307450442976689)
                  ·
                    refine ⟨8347982258480587832232517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11130643011307450442976689 8347982258480587832232517)
                    ·
                      refine ⟨1565246673465110218543597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8347982258480587832232517 1565246673465110218543597)
                      ·
                        rfl

theorem cell23_3048307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 2, 3, 2, 4].length) (baseStart_3048307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3048307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3048307 prefixEnd_3048307 := by exact prefixLift 3048307
  have htrace : WordTrace (prefixWord ++ tailWord_3048307) baseStart_3048307 baseEnd_3048307 := by
    simpa [prefixWord, tailWord_3048307, baseEnd_3048307] using wordTrace_append hprefix tailTrace_3048307
  have hstable : (prefixWord ++ tailWord_3048307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3048307).length < 2 ^ (prefixWord ++ tailWord_3048307).sum := by decide
  have hdescent : baseEnd_3048307 < baseStart_3048307 := by decide
  rcases family_descends (prefixWord ++ tailWord_3048307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3048328 : List Nat := [2, 1, 3, 3, 2, 1, 2, 2, 3, 2, 2]
def baseStart_3048328 : Nat := 118140960795 + 3048328 * 2 ^ 59
def prefixEnd_3048328 : Nat := 4983230072969 + 3 ^ 40 * 3048328 * 2
def baseEnd_3048328 : Nat := 1565257456558854636381001

theorem tailTrace_3048328 : CollatzResearch.WordTrace tailWord_3048328 prefixEnd_3048328 1565257456558854636381001 := by
  unfold tailWord_3048328
  simp only [CollatzResearch.WordTrace]
  refine ⟨55590828050217871909696819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74121104066957162546262425 55590828050217871909696819)
  ·
    refine ⟨83386242075326807864545229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55590828050217871909696819 83386242075326807864545229)
    ·
      refine ⟨31269840778247552949204461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83386242075326807864545229 31269840778247552949204461)
      ·
        refine ⟨11726190291842832355951673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31269840778247552949204461 11726190291842832355951673)
        ·
          refine ⟨8794642718882124266963755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11726190291842832355951673 8794642718882124266963755)
          ·
            refine ⟨13191964078323186400445633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8794642718882124266963755 13191964078323186400445633)
            ·
              refine ⟨9893973058742389800334225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13191964078323186400445633 9893973058742389800334225)
              ·
                refine ⟨7420479794056792350250669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9893973058742389800334225 7420479794056792350250669)
                ·
                  refine ⟨2782679922771297131344001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7420479794056792350250669 2782679922771297131344001)
                  ·
                    refine ⟨2087009942078472848508001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2782679922771297131344001 2087009942078472848508001)
                    ·
                      refine ⟨1565257456558854636381001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2087009942078472848508001 1565257456558854636381001)
                      ·
                        rfl

theorem cell23_3048328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 2, 2, 3, 2, 2].length) (baseStart_3048328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3048328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3048328 prefixEnd_3048328 := by exact prefixLift 3048328
  have htrace : WordTrace (prefixWord ++ tailWord_3048328) baseStart_3048328 baseEnd_3048328 := by
    simpa [prefixWord, tailWord_3048328, baseEnd_3048328] using wordTrace_append hprefix tailTrace_3048328
  have hstable : (prefixWord ++ tailWord_3048328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3048328).length < 2 ^ (prefixWord ++ tailWord_3048328).sum := by decide
  have hdescent : baseEnd_3048328 < baseStart_3048328 := by decide
  rcases family_descends (prefixWord ++ tailWord_3048328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3048361 : List Nat := [1, 2, 1, 1, 1, 1, 6, 4, 2, 1, 3]
def baseStart_3048361 : Nat := 118140960795 + 3048361 * 2 ^ 59
def prefixEnd_3048361 : Nat := 4983230072969 + 3 ^ 40 * 3048361 * 2
def baseEnd_3048361 : Nat := 1565274401420453007268349

theorem tailTrace_3048361 : CollatzResearch.WordTrace tailWord_3048361 prefixEnd_3048361 1565274401420453007268349 := by
  unfold tailWord_3048361
  simp only [CollatzResearch.WordTrace]
  refine ⟨111182859709316190455344937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74121906472877460303563291 111182859709316190455344937)
  ·
    refine ⟨83387144781987142841508703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111182859709316190455344937 83387144781987142841508703)
    ·
      refine ⟨125080717172980714262263055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83387144781987142841508703 125080717172980714262263055)
      ·
        refine ⟨187621075759471071393394583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125080717172980714262263055 187621075759471071393394583)
        ·
          refine ⟨281431613639206607090091875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 187621075759471071393394583 281431613639206607090091875)
          ·
            refine ⟨422147420458809910635137813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 281431613639206607090091875 422147420458809910635137813)
            ·
              refine ⟨19788160334006714561022085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 422147420458809910635137813 19788160334006714561022085)
              ·
                refine ⟨3710280062626258980191641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19788160334006714561022085 3710280062626258980191641)
                ·
                  refine ⟨2782710046969694235143731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3710280062626258980191641 2782710046969694235143731)
                  ·
                    refine ⟨4174065070454541352715597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2782710046969694235143731 4174065070454541352715597)
                    ·
                      refine ⟨1565274401420453007268349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4174065070454541352715597 1565274401420453007268349)
                      ·
                        rfl

theorem cell23_3048361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 4, 2, 1, 3].length) (baseStart_3048361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3048361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3048361 prefixEnd_3048361 := by exact prefixLift 3048361
  have htrace : WordTrace (prefixWord ++ tailWord_3048361) baseStart_3048361 baseEnd_3048361 := by
    simpa [prefixWord, tailWord_3048361, baseEnd_3048361] using wordTrace_append hprefix tailTrace_3048361
  have hstable : (prefixWord ++ tailWord_3048361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3048361).length < 2 ^ (prefixWord ++ tailWord_3048361).sum := by decide
  have hdescent : baseEnd_3048361 < baseStart_3048361 := by decide
  rcases family_descends (prefixWord ++ tailWord_3048361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3048372 : List Nat := [2, 5, 2, 1, 1, 3, 2, 1, 2, 4]
def baseStart_3048372 : Nat := 118140960795 + 3048372 * 2 ^ 59
def prefixEnd_3048372 : Nat := 4983230072969 + 3 ^ 40 * 3048372 * 2
def baseEnd_3048372 : Nat := 521760016569217488076933

theorem tailTrace_3048372 : CollatzResearch.WordTrace tailWord_3048372 prefixEnd_3048372 521760016569217488076933 := by
  unfold tailWord_3048372
  simp only [CollatzResearch.WordTrace]
  refine ⟨55591630456138169666997685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74122173941517559555996913 55591630456138169666997685)
  ·
    refine ⟨5211715355262953406281033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 55591630456138169666997685 5211715355262953406281033)
    ·
      refine ⟨3908786516447215054710775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5211715355262953406281033 3908786516447215054710775)
      ·
        refine ⟨5863179774670822582066163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3908786516447215054710775 5863179774670822582066163)
        ·
          refine ⟨8794769662006233873099245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5863179774670822582066163 8794769662006233873099245)
          ·
            refine ⟨3298038623252337702412217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8794769662006233873099245 3298038623252337702412217)
            ·
              refine ⟨2473528967439253276809163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3298038623252337702412217 2473528967439253276809163)
              ·
                refine ⟨3710293451158879915213745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2473528967439253276809163 3710293451158879915213745)
                ·
                  refine ⟨2782720088369159936410309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3710293451158879915213745 2782720088369159936410309)
                  ·
                    refine ⟨521760016569217488076933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2782720088369159936410309 521760016569217488076933)
                    ·
                      rfl

theorem cell23_3048372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 3, 2, 1, 2, 4].length) (baseStart_3048372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3048372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3048372 prefixEnd_3048372 := by exact prefixLift 3048372
  have htrace : WordTrace (prefixWord ++ tailWord_3048372) baseStart_3048372 baseEnd_3048372 := by
    simpa [prefixWord, tailWord_3048372, baseEnd_3048372] using wordTrace_append hprefix tailTrace_3048372
  have hstable : (prefixWord ++ tailWord_3048372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3048372).length < 2 ^ (prefixWord ++ tailWord_3048372).sum := by decide
  have hdescent : baseEnd_3048372 < baseStart_3048372 := by decide
  rcases family_descends (prefixWord ++ tailWord_3048372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3048387 : List Nat := [1, 1, 1, 3, 1, 1, 2, 2, 3, 3, 5]
def baseStart_3048387 : Nat := 118140960795 + 3048387 * 2 ^ 59
def prefixEnd_3048387 : Nat := 4983230072969 + 3 ^ 40 * 3048387 * 2
def baseEnd_3048387 : Nat := 1565287751917469905543229

theorem tailTrace_3048387 : CollatzResearch.WordTrace tailWord_3048387 prefixEnd_3048387 1565287751917469905543229 := by
  unfold tailWord_3048387
  simp only [CollatzResearch.WordTrace]
  refine ⟨111183808007221996895791415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74122538671481331263860943 111183808007221996895791415)
  ·
    refine ⟨166775712010832995343687123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111183808007221996895791415 166775712010832995343687123)
    ·
      refine ⟨250163568016249493015530685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166775712010832995343687123 250163568016249493015530685)
      ·
        refine ⟨93811338006093559880824007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 250163568016249493015530685 93811338006093559880824007)
        ·
          refine ⟨140717007009140339821236011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93811338006093559880824007 140717007009140339821236011)
          ·
            refine ⟨211075510513710509731854017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140717007009140339821236011 211075510513710509731854017)
            ·
              refine ⟨158306632885282882298890513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 211075510513710509731854017 158306632885282882298890513)
              ·
                refine ⟨118729974663962161724167885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 158306632885282882298890513 118729974663962161724167885)
                ·
                  refine ⟨44523740498985810646562957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 118729974663962161724167885 44523740498985810646562957)
                  ·
                    refine ⟨16696402687119678992461109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 44523740498985810646562957 16696402687119678992461109)
                    ·
                      refine ⟨1565287751917469905543229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16696402687119678992461109 1565287751917469905543229)
                      ·
                        rfl

theorem cell23_3048387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 2, 3, 3, 5].length) (baseStart_3048387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3048387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3048387 prefixEnd_3048387 := by exact prefixLift 3048387
  have htrace : WordTrace (prefixWord ++ tailWord_3048387) baseStart_3048387 baseEnd_3048387 := by
    simpa [prefixWord, tailWord_3048387, baseEnd_3048387] using wordTrace_append hprefix tailTrace_3048387
  have hstable : (prefixWord ++ tailWord_3048387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3048387).length < 2 ^ (prefixWord ++ tailWord_3048387).sum := by decide
  have hdescent : baseEnd_3048387 < baseStart_3048387 := by decide
  rcases family_descends (prefixWord ++ tailWord_3048387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3048401 : List Nat := [1, 2, 2, 1, 2, 1, 5, 2, 1, 4, 2]
def baseStart_3048401 : Nat := 118140960795 + 3048401 * 2 ^ 59
def prefixEnd_3048401 : Nat := 4983230072969 + 3 ^ 40 * 3048401 * 2
def baseEnd_3048401 : Nat := 1565294940646632850768165

theorem tailTrace_3048401 : CollatzResearch.WordTrace tailWord_3048401 prefixEnd_3048401 1565294940646632850768165 := by
  unfold tailWord_3048401
  simp only [CollatzResearch.WordTrace]
  refine ⟨111184318629171277286801057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74122879086114184857867371 111184318629171277286801057)
  ·
    refine ⟨83388238971878457965100793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111184318629171277286801057 83388238971878457965100793)
    ·
      refine ⟨62541179228908843473825595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83388238971878457965100793 62541179228908843473825595)
      ·
        refine ⟨93811768843363265210738393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62541179228908843473825595 93811768843363265210738393)
        ·
          refine ⟨70358826632522448908053795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93811768843363265210738393 70358826632522448908053795)
          ·
            refine ⟨105538239948783673362080693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70358826632522448908053795 105538239948783673362080693)
            ·
              refine ⟨9894209995198469377695065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 105538239948783673362080693 9894209995198469377695065)
              ·
                refine ⟨7420657496398852033271299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9894209995198469377695065 7420657496398852033271299)
                ·
                  refine ⟨11130986244598278049906949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7420657496398852033271299 11130986244598278049906949)
                  ·
                    refine ⟨2087059920862177134357553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11130986244598278049906949 2087059920862177134357553)
                    ·
                      refine ⟨1565294940646632850768165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2087059920862177134357553 1565294940646632850768165)
                      ·
                        rfl

theorem cell23_3048401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 5, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 5, 2, 1, 4, 2].length) (baseStart_3048401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3048401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3048401 prefixEnd_3048401 := by exact prefixLift 3048401
  have htrace : WordTrace (prefixWord ++ tailWord_3048401) baseStart_3048401 baseEnd_3048401 := by
    simpa [prefixWord, tailWord_3048401, baseEnd_3048401] using wordTrace_append hprefix tailTrace_3048401
  have hstable : (prefixWord ++ tailWord_3048401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3048401).length < 2 ^ (prefixWord ++ tailWord_3048401).sum := by decide
  have hdescent : baseEnd_3048401 < baseStart_3048401 := by decide
  rcases family_descends (prefixWord ++ tailWord_3048401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3048407 : List Nat := [1, 1, 3, 2, 1, 1, 2, 1, 11]
def baseStart_3048407 : Nat := 118140960795 + 3048407 * 2 ^ 59
def prefixEnd_3048407 : Nat := 4983230072969 + 3 ^ 40 * 3048407 * 2
def baseEnd_3048407 : Nat := 173922002392284425254793

theorem tailTrace_3048407 : CollatzResearch.WordTrace tailWord_3048407 prefixEnd_3048407 173922002392284425254793 := by
  unfold tailWord_3048407
  simp only [CollatzResearch.WordTrace]
  refine ⟨111184537467149540311519475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74123024978099693541012983 111184537467149540311519475)
  ·
    refine ⟨166776806200724310467279213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111184537467149540311519475 166776806200724310467279213)
    ·
      refine ⟨62541302325271616425229705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 166776806200724310467279213 62541302325271616425229705)
      ·
        refine ⟨46905976743953712318922279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62541302325271616425229705 46905976743953712318922279)
        ·
          refine ⟨70358965115930568478383419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46905976743953712318922279 70358965115930568478383419)
          ·
            refine ⟨105538447673895852717575129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70358965115930568478383419 105538447673895852717575129)
            ·
              refine ⟨79153835755421889538181347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 105538447673895852717575129 79153835755421889538181347)
              ·
                refine ⟨118730753633132834307272021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79153835755421889538181347 118730753633132834307272021)
                ·
                  refine ⟨173922002392284425254793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 118730753633132834307272021 173922002392284425254793)
                  ·
                    rfl

theorem cell23_3048407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 1, 11].length) (baseStart_3048407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3048407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3048407 prefixEnd_3048407 := by exact prefixLift 3048407
  have htrace : WordTrace (prefixWord ++ tailWord_3048407) baseStart_3048407 baseEnd_3048407 := by
    simpa [prefixWord, tailWord_3048407, baseEnd_3048407] using wordTrace_append hprefix tailTrace_3048407
  have hstable : (prefixWord ++ tailWord_3048407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3048407).length < 2 ^ (prefixWord ++ tailWord_3048407).sum := by decide
  have hdescent : baseEnd_3048407 < baseStart_3048407 := by decide
  rcases family_descends (prefixWord ++ tailWord_3048407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3048427 : List Nat := [1, 1, 1, 1, 2, 3, 1, 1, 1, 3, 8]
def baseStart_3048427 : Nat := 118140960795 + 3048427 * 2 ^ 59
def prefixEnd_3048427 : Nat := 4983230072969 + 3 ^ 40 * 3048427 * 2
def baseEnd_3048427 : Nat := 1565308291143649749043045

theorem tailTrace_3048427 : CollatzResearch.WordTrace tailWord_3048427 prefixEnd_3048427 1565308291143649749043045 := by
  unfold tailWord_3048427
  simp only [CollatzResearch.WordTrace]
  refine ⟨111185266927077083727247535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74123511284718055818165023 111185266927077083727247535)
  ·
    refine ⟨166777900390615625590871303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111185266927077083727247535 166777900390615625590871303)
    ·
      refine ⟨250166850585923438386306955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166777900390615625590871303 250166850585923438386306955)
      ·
        refine ⟨375250275878885157579460433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 250166850585923438386306955 375250275878885157579460433)
        ·
          refine ⟨281437706909163868184595325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 375250275878885157579460433 281437706909163868184595325)
          ·
            refine ⟨105539140090936450569223247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 281437706909163868184595325 105539140090936450569223247)
            ·
              refine ⟨158308710136404675853834871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105539140090936450569223247 158308710136404675853834871)
              ·
                refine ⟨237463065204607013780752307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 158308710136404675853834871 237463065204607013780752307)
                ·
                  refine ⟨356194597806910520671128461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 237463065204607013780752307 356194597806910520671128461)
                  ·
                    refine ⟨133572974177591445251673173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 356194597806910520671128461 133572974177591445251673173)
                    ·
                      refine ⟨1565308291143649749043045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 133572974177591445251673173 1565308291143649749043045)
                      ·
                        rfl

theorem cell23_3048427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 1, 1, 3, 8].length) (baseStart_3048427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3048427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3048427 prefixEnd_3048427 := by exact prefixLift 3048427
  have htrace : WordTrace (prefixWord ++ tailWord_3048427) baseStart_3048427 baseEnd_3048427 := by
    simpa [prefixWord, tailWord_3048427, baseEnd_3048427] using wordTrace_append hprefix tailTrace_3048427
  have hstable : (prefixWord ++ tailWord_3048427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3048427).length < 2 ^ (prefixWord ++ tailWord_3048427).sum := by decide
  have hdescent : baseEnd_3048427 < baseStart_3048427 := by decide
  rcases family_descends (prefixWord ++ tailWord_3048427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3048458 : List Nat := [3, 1, 2, 2, 3, 2, 2, 3, 5]
def baseStart_3048458 : Nat := 118140960795 + 3048458 * 2 ^ 59
def prefixEnd_3048458 : Nat := 4983230072969 + 3 ^ 40 * 3048458 * 2
def baseEnd_3048458 : Nat := 173924912115993236417267

theorem tailTrace_3048458 : CollatzResearch.WordTrace tailWord_3048458 prefixEnd_3048458 173924912115993236417267 := by
  unfold tailWord_3048458
  simp only [CollatzResearch.WordTrace]
  refine ⟨27796599397491194005406507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74124265059976517347750685 27796599397491194005406507)
  ·
    refine ⟨41694899096236791008109761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27796599397491194005406507 41694899096236791008109761)
    ·
      refine ⟨31271174322177593256082321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41694899096236791008109761 31271174322177593256082321)
      ·
        refine ⟨23453380741633194942061741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31271174322177593256082321 23453380741633194942061741)
        ·
          refine ⟨8795017778112448103273153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23453380741633194942061741 8795017778112448103273153)
          ·
            refine ⟨6596263333584336077454865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8795017778112448103273153 6596263333584336077454865)
            ·
              refine ⟨4947197500188252058091149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6596263333584336077454865 4947197500188252058091149)
              ·
                refine ⟨1855199062570594521784181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4947197500188252058091149 1855199062570594521784181)
                ·
                  refine ⟨173924912115993236417267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1855199062570594521784181 173924912115993236417267)
                  ·
                    rfl

theorem cell23_3048458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 2, 3, 5].length) (baseStart_3048458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3048458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3048458 prefixEnd_3048458 := by exact prefixLift 3048458
  have htrace : WordTrace (prefixWord ++ tailWord_3048458) baseStart_3048458 baseEnd_3048458 := by
    simpa [prefixWord, tailWord_3048458, baseEnd_3048458] using wordTrace_append hprefix tailTrace_3048458
  have hstable : (prefixWord ++ tailWord_3048458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3048458).length < 2 ^ (prefixWord ++ tailWord_3048458).sum := by decide
  have hdescent : baseEnd_3048458 < baseStart_3048458 := by decide
  rcases family_descends (prefixWord ++ tailWord_3048458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3048491 : List Nat := [1, 1, 1, 1, 2, 1, 5, 3, 2, 4, 2]
def baseStart_3048491 : Nat := 118140960795 + 3048491 * 2 ^ 59
def prefixEnd_3048491 : Nat := 4983230072969 + 3 ^ 40 * 3048491 * 2
def baseEnd_3048491 : Nat := 1565341153905537498642751

theorem tailTrace_3048491 : CollatzResearch.WordTrace tailWord_3048491 prefixEnd_3048491 1565341153905537498642751 := by
  unfold tailWord_3048491
  simp only [CollatzResearch.WordTrace]
  refine ⟨111187601198845222657577327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74125067465896815105051551 111187601198845222657577327)
  ·
    refine ⟨166781401798267833986365991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111187601198845222657577327 166781401798267833986365991)
    ·
      refine ⟨250172102697401750979548987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166781401798267833986365991 250172102697401750979548987)
      ·
        refine ⟨375258154046102626469323481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 250172102697401750979548987 375258154046102626469323481)
        ·
          refine ⟨281443615534576969851992611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 375258154046102626469323481 281443615534576969851992611)
          ·
            refine ⟨422165423301865454777988917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 281443615534576969851992611 422165423301865454777988917)
            ·
              refine ⟨39578008434549886385436461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 422165423301865454777988917 39578008434549886385436461)
              ·
                refine ⟨14841753162956207394538673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39578008434549886385436461 14841753162956207394538673)
                ·
                  refine ⟨11131314872217155545904005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14841753162956207394538673 11131314872217155545904005)
                  ·
                    refine ⟨2087121538540716664857001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11131314872217155545904005 2087121538540716664857001)
                    ·
                      refine ⟨1565341153905537498642751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2087121538540716664857001 1565341153905537498642751)
                      ·
                        rfl

theorem cell23_3048491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 3, 2, 4, 2].length) (baseStart_3048491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3048491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3048491 prefixEnd_3048491 := by exact prefixLift 3048491
  have htrace : WordTrace (prefixWord ++ tailWord_3048491) baseStart_3048491 baseEnd_3048491 := by
    simpa [prefixWord, tailWord_3048491, baseEnd_3048491] using wordTrace_append hprefix tailTrace_3048491
  have hstable : (prefixWord ++ tailWord_3048491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3048491).length < 2 ^ (prefixWord ++ tailWord_3048491).sum := by decide
  have hdescent : baseEnd_3048491 < baseStart_3048491 := by decide
  rcases family_descends (prefixWord ++ tailWord_3048491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3048511 : List Nat := [1, 1, 2, 2, 3, 1, 1, 5, 2, 2, 3]
def baseStart_3048511 : Nat := 118140960795 + 3048511 * 2 ^ 59
def prefixEnd_3048511 : Nat := 4983230072969 + 3 ^ 40 * 3048511 * 2
def baseEnd_3048511 : Nat := 1565351423518627420392659

theorem tailTrace_3048511 : CollatzResearch.WordTrace tailWord_3048511 prefixEnd_3048511 1565351423518627420392659 := by
  unfold tailWord_3048511
  simp only [CollatzResearch.WordTrace]
  refine ⟨111188330658772766073305387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74125553772515177382203591 111188330658772766073305387)
  ·
    refine ⟨166782495988159149109958081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111188330658772766073305387 166782495988159149109958081)
    ·
      refine ⟨125086871991119361832468561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166782495988159149109958081 125086871991119361832468561)
      ·
        refine ⟨93815153993339521374351421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125086871991119361832468561 93815153993339521374351421)
        ·
          refine ⟨35180682747502320515381783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 93815153993339521374351421 35180682747502320515381783)
          ·
            refine ⟨52771024121253480773072675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35180682747502320515381783 52771024121253480773072675)
            ·
              refine ⟨79156536181880221159609013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52771024121253480773072675 79156536181880221159609013)
              ·
                refine ⟨7420925267051270733713345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 79156536181880221159609013 7420925267051270733713345)
                ·
                  refine ⟨5565693950288453050285009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7420925267051270733713345 5565693950288453050285009)
                  ·
                    refine ⟨4174270462716339787713757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5565693950288453050285009 4174270462716339787713757)
                    ·
                      refine ⟨1565351423518627420392659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4174270462716339787713757 1565351423518627420392659)
                      ·
                        rfl

theorem cell23_3048511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 5, 2, 2, 3].length) (baseStart_3048511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3048511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3048511 prefixEnd_3048511 := by exact prefixLift 3048511
  have htrace : WordTrace (prefixWord ++ tailWord_3048511) baseStart_3048511 baseEnd_3048511 := by
    simpa [prefixWord, tailWord_3048511, baseEnd_3048511] using wordTrace_append hprefix tailTrace_3048511
  have hstable : (prefixWord ++ tailWord_3048511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3048511).length < 2 ^ (prefixWord ++ tailWord_3048511).sum := by decide
  have hdescent : baseEnd_3048511 < baseStart_3048511 := by decide
  rcases family_descends (prefixWord ++ tailWord_3048511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3048561 : List Nat := [1, 2, 2, 2, 1, 1, 2, 6, 1, 5]
def baseStart_3048561 : Nat := 118140960795 + 3048561 * 2 ^ 59
def prefixEnd_3048561 : Nat := 4983230072969 + 3 ^ 40 * 3048561 * 2
def baseEnd_3048561 : Nat := 521792365850450741589143

theorem tailTrace_3048561 : CollatzResearch.WordTrace tailWord_3048561 prefixEnd_3048561 521792365850450741589143 := by
  unfold tailWord_3048561
  simp only [CollatzResearch.WordTrace]
  refine ⟨111190154308591624612625537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74126769539061083075083691 111190154308591624612625537)
  ·
    refine ⟨83392615731443718459469153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111190154308591624612625537 83392615731443718459469153)
    ·
      refine ⟨62544461798582788844601865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83392615731443718459469153 62544461798582788844601865)
      ·
        refine ⟨46908346348937091633451399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62544461798582788844601865 46908346348937091633451399)
        ·
          refine ⟨70362519523405637450177099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46908346348937091633451399 70362519523405637450177099)
          ·
            refine ⟨105543779285108456175265649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70362519523405637450177099 105543779285108456175265649)
            ·
              refine ⟨79157834463831342131449237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 105543779285108456175265649 79157834463831342131449237)
              ·
                refine ⟨3710523490492094162411683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 79157834463831342131449237 3710523490492094162411683)
                ·
                  refine ⟨5565785235738141243617525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3710523490492094162411683 5565785235738141243617525)
                  ·
                    refine ⟨521792365850450741589143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5565785235738141243617525 521792365850450741589143)
                    ·
                      rfl

theorem cell23_3048561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 6, 1, 5].length) (baseStart_3048561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3048561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3048561 prefixEnd_3048561 := by exact prefixLift 3048561
  have htrace : WordTrace (prefixWord ++ tailWord_3048561) baseStart_3048561 baseEnd_3048561 := by
    simpa [prefixWord, tailWord_3048561, baseEnd_3048561] using wordTrace_append hprefix tailTrace_3048561
  have hstable : (prefixWord ++ tailWord_3048561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3048561).length < 2 ^ (prefixWord ++ tailWord_3048561).sum := by decide
  have hdescent : baseEnd_3048561 < baseStart_3048561 := by decide
  rcases family_descends (prefixWord ++ tailWord_3048561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3048568 : List Nat := [2, 1, 2, 1, 1, 1, 5, 3, 2, 3, 2]
def baseStart_3048568 : Nat := 118140960795 + 3048568 * 2 ^ 59
def prefixEnd_3048568 : Nat := 4983230072969 + 3 ^ 40 * 3048568 * 2
def baseEnd_3048568 : Nat := 1565380691915933697379897

theorem tailTrace_3048568 : CollatzResearch.WordTrace tailWord_3048568 prefixEnd_3048568 1565380691915933697379897 := by
  unfold tailWord_3048568
  simp only [CollatzResearch.WordTrace]
  refine ⟨55595204809783132404065179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74126939746377509872086905 55595204809783132404065179)
  ·
    refine ⟨83392807214674698606097769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55595204809783132404065179 83392807214674698606097769)
    ·
      refine ⟨62544605411006023954573327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83392807214674698606097769 62544605411006023954573327)
      ·
        refine ⟨93816908116509035931859991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62544605411006023954573327 93816908116509035931859991)
        ·
          refine ⟨140725362174763553897789987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93816908116509035931859991 140725362174763553897789987)
          ·
            refine ⟨211088043262145330846684981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140725362174763553897789987 211088043262145330846684981)
            ·
              refine ⟨19789504055826124766876717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 211088043262145330846684981 19789504055826124766876717)
              ·
                refine ⟨7421064020934796787578769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19789504055826124766876717 7421064020934796787578769)
                ·
                  refine ⟨5565798015701097590684077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7421064020934796787578769 5565798015701097590684077)
                  ·
                    refine ⟨2087174255887911596506529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5565798015701097590684077 2087174255887911596506529)
                    ·
                      refine ⟨1565380691915933697379897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2087174255887911596506529 1565380691915933697379897)
                      ·
                        rfl

theorem cell23_3048568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 3, 2, 3, 2].length) (baseStart_3048568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3048568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3048568 prefixEnd_3048568 := by exact prefixLift 3048568
  have htrace : WordTrace (prefixWord ++ tailWord_3048568) baseStart_3048568 baseEnd_3048568 := by
    simpa [prefixWord, tailWord_3048568, baseEnd_3048568] using wordTrace_append hprefix tailTrace_3048568
  have hstable : (prefixWord ++ tailWord_3048568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3048568).length < 2 ^ (prefixWord ++ tailWord_3048568).sum := by decide
  have hdescent : baseEnd_3048568 < baseStart_3048568 := by decide
  rcases family_descends (prefixWord ++ tailWord_3048568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3048608 : List Nat := [2, 1, 1, 4, 2, 1, 1, 5, 2, 4]
def baseStart_3048608 : Nat := 118140960795 + 3048608 * 2 ^ 59
def prefixEnd_3048608 : Nat := 4983230072969 + 3 ^ 40 * 3048608 * 2
def baseEnd_3048608 : Nat := 521800410380704513626571

theorem tailTrace_3048608 : CollatzResearch.WordTrace tailWord_3048608 prefixEnd_3048608 521800410380704513626571 := by
  unfold tailWord_3048608
  simp only [CollatzResearch.WordTrace]
  refine ⟨55595934269710675819793239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74127912359614234426390985 55595934269710675819793239)
  ·
    refine ⟨83393901404566013729689859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55595934269710675819793239 83393901404566013729689859)
    ·
      refine ⟨125090852106849020594534789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83393901404566013729689859 125090852106849020594534789)
      ·
        refine ⟨23454534770034191361475273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 125090852106849020594534789 23454534770034191361475273)
        ·
          refine ⟨17590901077525643521106455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23454534770034191361475273 17590901077525643521106455)
          ·
            refine ⟨26386351616288465281659683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17590901077525643521106455 26386351616288465281659683)
            ·
              refine ⟨39579527424432697922489525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26386351616288465281659683 39579527424432697922489525)
              ·
                refine ⟨3710580696040565430233393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 39579527424432697922489525 3710580696040565430233393)
                ·
                  refine ⟨2782935522030424072675045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3710580696040565430233393 2782935522030424072675045)
                  ·
                    refine ⟨521800410380704513626571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2782935522030424072675045 521800410380704513626571)
                    ·
                      rfl

theorem cell23_3048608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 5, 2, 4].length) (baseStart_3048608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3048608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3048608 prefixEnd_3048608 := by exact prefixLift 3048608
  have htrace : WordTrace (prefixWord ++ tailWord_3048608) baseStart_3048608 baseEnd_3048608 := by
    simpa [prefixWord, tailWord_3048608, baseEnd_3048608] using wordTrace_append hprefix tailTrace_3048608
  have hstable : (prefixWord ++ tailWord_3048608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3048608).length < 2 ^ (prefixWord ++ tailWord_3048608).sum := by decide
  have hdescent : baseEnd_3048608 < baseStart_3048608 := by decide
  rcases family_descends (prefixWord ++ tailWord_3048608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3048671 : List Nat := [1, 1, 2, 3, 2, 1, 2, 2, 2, 3, 4]
def baseStart_3048671 : Nat := 118140960795 + 3048671 * 2 ^ 59
def prefixEnd_3048671 : Nat := 4983230072969 + 3 ^ 40 * 3048671 * 2
def baseEnd_3048671 : Nat := 1565433580423346794391923

theorem tailTrace_3048671 : CollatzResearch.WordTrace tailWord_3048671 prefixEnd_3048671 1565433580423346794391923 := by
  unfold tailWord_3048671
  simp only [CollatzResearch.WordTrace]
  refine ⟨111194166338193113399129867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74129444225462075599419911 111194166338193113399129867)
  ·
    refine ⟨166791249507289670098694801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111194166338193113399129867 166791249507289670098694801)
    ·
      refine ⟨125093437130467252574021101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166791249507289670098694801 125093437130467252574021101)
      ·
        refine ⟨46910038923925219715257913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 125093437130467252574021101 46910038923925219715257913)
        ·
          refine ⟨35182529192943914786443435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46910038923925219715257913 35182529192943914786443435)
          ·
            refine ⟨52773793789415872179665153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35182529192943914786443435 52773793789415872179665153)
            ·
              refine ⟨39580345342061904134748865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52773793789415872179665153 39580345342061904134748865)
              ·
                refine ⟨29685259006546428101061649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39580345342061904134748865 29685259006546428101061649)
                ·
                  refine ⟨22263944254909821075796237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29685259006546428101061649 22263944254909821075796237)
                  ·
                    refine ⟨8348979095591182903423589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22263944254909821075796237 8348979095591182903423589)
                    ·
                      refine ⟨1565433580423346794391923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8348979095591182903423589 1565433580423346794391923)
                      ·
                        rfl

theorem cell23_3048671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 2, 2, 3, 4].length) (baseStart_3048671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3048671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3048671 prefixEnd_3048671 := by exact prefixLift 3048671
  have htrace : WordTrace (prefixWord ++ tailWord_3048671) baseStart_3048671 baseEnd_3048671 := by
    simpa [prefixWord, tailWord_3048671, baseEnd_3048671] using wordTrace_append hprefix tailTrace_3048671
  have hstable : (prefixWord ++ tailWord_3048671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3048671).length < 2 ^ (prefixWord ++ tailWord_3048671).sum := by decide
  have hdescent : baseEnd_3048671 < baseStart_3048671 := by decide
  rcases family_descends (prefixWord ++ tailWord_3048671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3048691 : List Nat := [1, 1, 1, 2, 2, 5, 1, 1, 1, 3, 5]
def baseStart_3048691 : Nat := 118140960795 + 3048691 * 2 ^ 59
def prefixEnd_3048691 : Nat := 4983230072969 + 3 ^ 40 * 3048691 * 2
def baseEnd_3048691 : Nat := 1565443850036436716141831

theorem tailTrace_3048691 : CollatzResearch.WordTrace tailWord_3048691 prefixEnd_3048691 1565443850036436716141831 := by
  unfold tailWord_3048691
  simp only [CollatzResearch.WordTrace]
  refine ⟨111194895798120656814857927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74129930532080437876571951 111194895798120656814857927)
  ·
    refine ⟨166792343697180985222286891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111194895798120656814857927 166792343697180985222286891)
    ·
      refine ⟨250188515545771477833430337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166792343697180985222286891 250188515545771477833430337)
      ·
        refine ⟨187641386659328608375072753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 250188515545771477833430337 187641386659328608375072753)
        ·
          refine ⟨140731039994496456281304565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 187641386659328608375072753 140731039994496456281304565)
          ·
            refine ⟨13193534999484042776372303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 140731039994496456281304565 13193534999484042776372303)
            ·
              refine ⟨19790302499226064164558455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13193534999484042776372303 19790302499226064164558455)
              ·
                refine ⟨29685453748839096246837683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19790302499226064164558455 29685453748839096246837683)
                ·
                  refine ⟨44528180623258644370256525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29685453748839096246837683 44528180623258644370256525)
                  ·
                    refine ⟨16698067733721991638846197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 44528180623258644370256525 16698067733721991638846197)
                    ·
                      refine ⟨1565443850036436716141831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16698067733721991638846197 1565443850036436716141831)
                      ·
                        rfl

theorem cell23_3048691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 1, 1, 3, 5].length) (baseStart_3048691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3048691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3048691 prefixEnd_3048691 := by exact prefixLift 3048691
  have htrace : WordTrace (prefixWord ++ tailWord_3048691) baseStart_3048691 baseEnd_3048691 := by
    simpa [prefixWord, tailWord_3048691, baseEnd_3048691] using wordTrace_append hprefix tailTrace_3048691
  have hstable : (prefixWord ++ tailWord_3048691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3048691).length < 2 ^ (prefixWord ++ tailWord_3048691).sum := by decide
  have hdescent : baseEnd_3048691 < baseStart_3048691 := by decide
  rcases family_descends (prefixWord ++ tailWord_3048691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3048771 : List Nat := [1, 1, 1, 3, 1, 3, 1, 2, 2, 8]
def baseStart_3048771 : Nat := 118140960795 + 3048771 * 2 ^ 59
def prefixEnd_3048771 : Nat := 4983230072969 + 3 ^ 40 * 3048771 * 2
def baseEnd_3048771 : Nat := 521828309496265467713821

theorem tailTrace_3048771 : CollatzResearch.WordTrace tailWord_3048771 prefixEnd_3048771 521828309496265467713821 := by
  unfold tailWord_3048771
  simp only [CollatzResearch.WordTrace]
  refine ⟨111197813637830830477770167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74131875758553886985180111 111197813637830830477770167)
  ·
    refine ⟨166796720456746245716655251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111197813637830830477770167 166796720456746245716655251)
    ·
      refine ⟨250195080685119368574982877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166796720456746245716655251 250195080685119368574982877)
      ·
        refine ⟨93823155256919763215618579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 250195080685119368574982877 93823155256919763215618579)
        ·
          refine ⟨140734732885379644823427869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93823155256919763215618579 140734732885379644823427869)
          ·
            refine ⟨52775524832017366808785451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 140734732885379644823427869 52775524832017366808785451)
            ·
              refine ⟨79163287248026050213178177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52775524832017366808785451 79163287248026050213178177)
              ·
                refine ⟨59372465436019537659883633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79163287248026050213178177 59372465436019537659883633)
                ·
                  refine ⟨44529349077014653244912725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59372465436019537659883633 44529349077014653244912725)
                  ·
                    refine ⟨521828309496265467713821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 44529349077014653244912725 521828309496265467713821)
                    ·
                      rfl

theorem cell23_3048771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 2, 2, 8].length) (baseStart_3048771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3048771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3048771 prefixEnd_3048771 := by exact prefixLift 3048771
  have htrace : WordTrace (prefixWord ++ tailWord_3048771) baseStart_3048771 baseEnd_3048771 := by
    simpa [prefixWord, tailWord_3048771, baseEnd_3048771] using wordTrace_append hprefix tailTrace_3048771
  have hstable : (prefixWord ++ tailWord_3048771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3048771).length < 2 ^ (prefixWord ++ tailWord_3048771).sum := by decide
  have hdescent : baseEnd_3048771 < baseStart_3048771 := by decide
  rcases family_descends (prefixWord ++ tailWord_3048771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3048772 : List Nat := [2, 3, 4, 1, 1, 2, 1, 1, 2, 3, 3]
def baseStart_3048772 : Nat := 118140960795 + 3048772 * 2 ^ 59
def prefixEnd_3048772 : Nat := 4983230072969 + 3 ^ 40 * 3048772 * 2
def baseEnd_3048772 : Nat := 1565485441969450899228959

theorem tailTrace_3048772 : CollatzResearch.WordTrace tailWord_3048772 prefixEnd_3048772 1565485441969450899228959 := by
  unfold tailWord_3048772
  simp only [CollatzResearch.WordTrace]
  refine ⟨55598925055413603824278285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74131900073884805099037713 55598925055413603824278285)
  ·
    refine ⟨20849596895780101434104357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55598925055413603824278285 20849596895780101434104357)
    ·
      refine ⟨3909299417958769018894567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20849596895780101434104357 3909299417958769018894567)
      ·
        refine ⟨5863949126938153528341851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3909299417958769018894567 5863949126938153528341851)
        ·
          refine ⟨8795923690407230292512777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5863949126938153528341851 8795923690407230292512777)
          ·
            refine ⟨6596942767805422719384583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8795923690407230292512777 6596942767805422719384583)
            ·
              refine ⟨9895414151708134079076875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6596942767805422719384583 9895414151708134079076875)
              ·
                refine ⟨14843121227562201118615313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9895414151708134079076875 14843121227562201118615313)
                ·
                  refine ⟨11132340920671650838961485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14843121227562201118615313 11132340920671650838961485)
                  ·
                    refine ⟨4174627845251869064610557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11132340920671650838961485 4174627845251869064610557)
                    ·
                      refine ⟨1565485441969450899228959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4174627845251869064610557 1565485441969450899228959)
                      ·
                        rfl

theorem cell23_3048772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 1, 1, 2, 3, 3].length) (baseStart_3048772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3048772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3048772 prefixEnd_3048772 := by exact prefixLift 3048772
  have htrace : WordTrace (prefixWord ++ tailWord_3048772) baseStart_3048772 baseEnd_3048772 := by
    simpa [prefixWord, tailWord_3048772, baseEnd_3048772] using wordTrace_append hprefix tailTrace_3048772
  have hstable : (prefixWord ++ tailWord_3048772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3048772).length < 2 ^ (prefixWord ++ tailWord_3048772).sum := by decide
  have hdescent : baseEnd_3048772 < baseStart_3048772 := by decide
  rcases family_descends (prefixWord ++ tailWord_3048772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3048778 : List Nat := [3, 1, 2, 1, 1, 1, 1, 4, 4, 1, 4]
def baseStart_3048778 : Nat := 118140960795 + 3048778 * 2 ^ 59
def prefixEnd_3048778 : Nat := 4983230072969 + 3 ^ 40 * 3048778 * 2
def baseEnd_3048778 : Nat := 1565488522853377875753931

theorem tailTrace_3048778 : CollatzResearch.WordTrace tailWord_3048778 prefixEnd_3048778 1565488522853377875753931 := by
  unfold tailWord_3048778
  simp only [CollatzResearch.WordTrace]
  refine ⟨27799517237201367668318747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74132045965870313782183325 27799517237201367668318747)
  ·
    refine ⟨41699275855802051502478121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27799517237201367668318747 41699275855802051502478121)
    ·
      refine ⟨31274456891851538626858591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41699275855802051502478121 31274456891851538626858591)
      ·
        refine ⟨46911685337777307940287887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31274456891851538626858591 46911685337777307940287887)
        ·
          refine ⟨70367528006665961910431831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46911685337777307940287887 70367528006665961910431831)
          ·
            refine ⟨105551292009998942865647747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70367528006665961910431831 105551292009998942865647747)
            ·
              refine ⟨158326938014998414298471621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105551292009998942865647747 158326938014998414298471621)
              ·
                refine ⟨29686300877812202680963429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 158326938014998414298471621 29686300877812202680963429)
                ·
                  refine ⟨5566181414589788002680643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29686300877812202680963429 5566181414589788002680643)
                  ·
                    refine ⟨8349272121884682004020965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5566181414589788002680643 8349272121884682004020965)
                    ·
                      refine ⟨1565488522853377875753931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8349272121884682004020965 1565488522853377875753931)
                      ·
                        rfl

theorem cell23_3048778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 4, 4, 1, 4].length) (baseStart_3048778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3048778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3048778 prefixEnd_3048778 := by exact prefixLift 3048778
  have htrace : WordTrace (prefixWord ++ tailWord_3048778) baseStart_3048778 baseEnd_3048778 := by
    simpa [prefixWord, tailWord_3048778, baseEnd_3048778] using wordTrace_append hprefix tailTrace_3048778
  have hstable : (prefixWord ++ tailWord_3048778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3048778).length < 2 ^ (prefixWord ++ tailWord_3048778).sum := by decide
  have hdescent : baseEnd_3048778 < baseStart_3048778 := by decide
  rcases family_descends (prefixWord ++ tailWord_3048778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3048818 : List Nat := [3, 2, 1, 2, 1, 2, 3, 1, 8]
def baseStart_3048818 : Nat := 118140960795 + 3048818 * 2 ^ 59
def prefixEnd_3048818 : Nat := 4983230072969 + 3 ^ 40 * 3048818 * 2
def baseEnd_3048818 : Nat := 173945451342173079917083

theorem tailTrace_3048818 : CollatzResearch.WordTrace tailWord_3048818 prefixEnd_3048818 173945451342173079917083 := by
  unfold tailWord_3048818
  simp only [CollatzResearch.WordTrace]
  refine ⟨27799881967165139376182777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74133018579107038336487405 27799881967165139376182777)
  ·
    refine ⟨20849911475373854532137083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27799881967165139376182777 20849911475373854532137083)
    ·
      refine ⟨31274867213060781798205625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20849911475373854532137083 31274867213060781798205625)
      ·
        refine ⟨23456150409795586348654219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31274867213060781798205625 23456150409795586348654219)
        ·
          refine ⟨35184225614693379522981329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23456150409795586348654219 35184225614693379522981329)
          ·
            refine ⟨26388169211020034642235997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35184225614693379522981329 26388169211020034642235997)
            ·
              refine ⟨9895563454132512990838499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26388169211020034642235997 9895563454132512990838499)
              ·
                refine ⟨14843345181198769486257749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9895563454132512990838499 14843345181198769486257749)
                ·
                  refine ⟨173945451342173079917083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 14843345181198769486257749 173945451342173079917083)
                  ·
                    rfl

theorem cell23_3048818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 3, 1, 8].length) (baseStart_3048818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3048818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3048818 prefixEnd_3048818 := by exact prefixLift 3048818
  have htrace : WordTrace (prefixWord ++ tailWord_3048818) baseStart_3048818 baseEnd_3048818 := by
    simpa [prefixWord, tailWord_3048818, baseEnd_3048818] using wordTrace_append hprefix tailTrace_3048818
  have hstable : (prefixWord ++ tailWord_3048818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3048818).length < 2 ^ (prefixWord ++ tailWord_3048818).sum := by decide
  have hdescent : baseEnd_3048818 < baseStart_3048818 := by decide
  rcases family_descends (prefixWord ++ tailWord_3048818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3048856 : List Nat := [2, 1, 2, 5, 2, 2, 1, 3, 1, 4]
def baseStart_3048856 : Nat := 118140960795 + 3048856 * 2 ^ 59
def prefixEnd_3048856 : Nat := 4983230072969 + 3 ^ 40 * 3048856 * 2
def baseEnd_3048856 : Nat := 521842858114809523526191

theorem tailTrace_3048856 : CollatzResearch.WordTrace tailWord_3048856 prefixEnd_3048856 521842858114809523526191 := by
  unfold tailWord_3048856
  simp only [CollatzResearch.WordTrace]
  refine ⟨55600456921261444997307211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74133942561681926663076281 55600456921261444997307211)
  ·
    refine ⟨83400685381892167495960817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55600456921261444997307211 83400685381892167495960817)
    ·
      refine ⟨62550514036419125621970613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83400685381892167495960817 62550514036419125621970613)
      ·
        refine ⟨5864110690914293027059745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 62550514036419125621970613 5864110690914293027059745)
        ·
          refine ⟨4398083018185719770294809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5864110690914293027059745 4398083018185719770294809)
          ·
            refine ⟨3298562263639289827721107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4398083018185719770294809 3298562263639289827721107)
            ·
              refine ⟨4947843395458934741581661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3298562263639289827721107 4947843395458934741581661)
              ·
                refine ⟨1855441273297100528093123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4947843395458934741581661 1855441273297100528093123)
                ·
                  refine ⟨2783161909945650792139685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1855441273297100528093123 2783161909945650792139685)
                  ·
                    refine ⟨521842858114809523526191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2783161909945650792139685 521842858114809523526191)
                    ·
                      rfl

theorem cell23_3048856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 2, 1, 3, 1, 4].length) (baseStart_3048856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3048856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3048856 prefixEnd_3048856 := by exact prefixLift 3048856
  have htrace : WordTrace (prefixWord ++ tailWord_3048856) baseStart_3048856 baseEnd_3048856 := by
    simpa [prefixWord, tailWord_3048856, baseEnd_3048856] using wordTrace_append hprefix tailTrace_3048856
  have hstable : (prefixWord ++ tailWord_3048856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3048856).length < 2 ^ (prefixWord ++ tailWord_3048856).sum := by decide
  have hdescent : baseEnd_3048856 < baseStart_3048856 := by decide
  rcases family_descends (prefixWord ++ tailWord_3048856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3048922 : List Nat := [3, 1, 1, 2, 3, 4, 1, 1, 1, 1, 5]
def baseStart_3048922 : Nat := 118140960795 + 3048922 * 2 ^ 59
def prefixEnd_3048922 : Nat := 4983230072969 + 3 ^ 40 * 3048922 * 2
def baseEnd_3048922 : Nat := 1565562464067625312353269

theorem tailTrace_3048922 : CollatzResearch.WordTrace tailWord_3048922 prefixEnd_3048922 1565562464067625312353269 := by
  unfold tailWord_3048922
  simp only [CollatzResearch.WordTrace]
  refine ⟨27800830265070945816629255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74135547373522522177678013 27800830265070945816629255)
  ·
    refine ⟨41701245397606418724943883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27800830265070945816629255 41701245397606418724943883)
    ·
      refine ⟨62551868096409628087415825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41701245397606418724943883 62551868096409628087415825)
      ·
        refine ⟨46913901072307221065561869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62551868096409628087415825 46913901072307221065561869)
        ·
          refine ⟨17592712902115207899585701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46913901072307221065561869 17592712902115207899585701)
          ·
            refine ⟨3298633669146601481172319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17592712902115207899585701 3298633669146601481172319)
            ·
              refine ⟨4947950503719902221758479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3298633669146601481172319 4947950503719902221758479)
              ·
                refine ⟨7421925755579853332637719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4947950503719902221758479 7421925755579853332637719)
                ·
                  refine ⟨11132888633369779998956579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7421925755579853332637719 11132888633369779998956579)
                  ·
                    refine ⟨16699332950054669998434869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11132888633369779998956579 16699332950054669998434869)
                    ·
                      refine ⟨1565562464067625312353269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16699332950054669998434869 1565562464067625312353269)
                      ·
                        rfl

theorem cell23_3048922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 4, 1, 1, 1, 1, 5].length) (baseStart_3048922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3048922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3048922 prefixEnd_3048922 := by exact prefixLift 3048922
  have htrace : WordTrace (prefixWord ++ tailWord_3048922) baseStart_3048922 baseEnd_3048922 := by
    simpa [prefixWord, tailWord_3048922, baseEnd_3048922] using wordTrace_append hprefix tailTrace_3048922
  have hstable : (prefixWord ++ tailWord_3048922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3048922).length < 2 ^ (prefixWord ++ tailWord_3048922).sum := by decide
  have hdescent : baseEnd_3048922 < baseStart_3048922 := by decide
  rcases family_descends (prefixWord ++ tailWord_3048922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3048928 : List Nat := [2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 6]
def baseStart_3048928 : Nat := 118140960795 + 3048928 * 2 ^ 59
def prefixEnd_3048928 : Nat := 4983230072969 + 3 ^ 40 * 3048928 * 2
def baseEnd_3048928 : Nat := 1565565544951552288878241

theorem tailTrace_3048928 : CollatzResearch.WordTrace tailWord_3048928 prefixEnd_3048928 1565565544951552288878241 := by
  unfold tailWord_3048928
  simp only [CollatzResearch.WordTrace]
  refine ⟨55601769949131023145617719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74135693265508030860823625 55601769949131023145617719)
  ·
    refine ⟨83402654923696534718426579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55601769949131023145617719 83402654923696534718426579)
    ·
      refine ⟨125103982385544802077639869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83402654923696534718426579 125103982385544802077639869)
      ·
        refine ⟨46913993394579300779114951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 125103982385544802077639869 46913993394579300779114951)
        ·
          refine ⟨70370990091868951168672427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46913993394579300779114951 70370990091868951168672427)
          ·
            refine ⟨105556485137803426753008641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70370990091868951168672427 105556485137803426753008641)
            ·
              refine ⟨79167363853352570064756481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 105556485137803426753008641 79167363853352570064756481)
              ·
                refine ⟨59375522890014427548567361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79167363853352570064756481 59375522890014427548567361)
                ·
                  refine ⟨44531642167510820661425521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59375522890014427548567361 44531642167510820661425521)
                  ·
                    refine ⟨33398731625633115496069141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 44531642167510820661425521 33398731625633115496069141)
                    ·
                      refine ⟨1565565544951552288878241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 33398731625633115496069141 1565565544951552288878241)
                      ·
                        rfl

theorem cell23_3048928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 6].length) (baseStart_3048928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3048928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3048928 prefixEnd_3048928 := by exact prefixLift 3048928
  have htrace : WordTrace (prefixWord ++ tailWord_3048928) baseStart_3048928 baseEnd_3048928 := by
    simpa [prefixWord, tailWord_3048928, baseEnd_3048928] using wordTrace_append hprefix tailTrace_3048928
  have hstable : (prefixWord ++ tailWord_3048928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3048928).length < 2 ^ (prefixWord ++ tailWord_3048928).sum := by decide
  have hdescent : baseEnd_3048928 < baseStart_3048928 := by decide
  rcases family_descends (prefixWord ++ tailWord_3048928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3048936 : List Nat := [2, 1, 4, 1, 1, 2, 3, 4, 1, 2, 2]
def baseStart_3048936 : Nat := 118140960795 + 3048936 * 2 ^ 59
def prefixEnd_3048936 : Nat := 4983230072969 + 3 ^ 40 * 3048936 * 2
def baseEnd_3048936 : Nat := 1565569652796788257578205

theorem tailTrace_3048936 : CollatzResearch.WordTrace tailWord_3048936 prefixEnd_3048936 1565569652796788257578205 := by
  unfold tailWord_3048936
  simp only [CollatzResearch.WordTrace]
  refine ⟨55601915841116531828763331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74135887788155375771684441 55601915841116531828763331)
  ·
    refine ⟨83402873761674797743144997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55601915841116531828763331 83402873761674797743144997)
    ·
      refine ⟨15638038830314024576839687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 83402873761674797743144997 15638038830314024576839687)
      ·
        refine ⟨23457058245471036865259531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15638038830314024576839687 23457058245471036865259531)
        ·
          refine ⟨35185587368206555297889297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23457058245471036865259531 35185587368206555297889297)
          ·
            refine ⟨26389190526154916473416973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35185587368206555297889297 26389190526154916473416973)
            ·
              refine ⟨9895946447308093677531365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26389190526154916473416973 9895946447308093677531365)
              ·
                refine ⟨1855489958870267564537131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9895946447308093677531365 1855489958870267564537131)
                ·
                  refine ⟨2783234938305401346805697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1855489958870267564537131 2783234938305401346805697)
                  ·
                    refine ⟨2087426203729051010104273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2783234938305401346805697 2087426203729051010104273)
                    ·
                      refine ⟨1565569652796788257578205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2087426203729051010104273 1565569652796788257578205)
                      ·
                        rfl

theorem cell23_3048936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 3, 4, 1, 2, 2].length) (baseStart_3048936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3048936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3048936 prefixEnd_3048936 := by exact prefixLift 3048936
  have htrace : WordTrace (prefixWord ++ tailWord_3048936) baseStart_3048936 baseEnd_3048936 := by
    simpa [prefixWord, tailWord_3048936, baseEnd_3048936] using wordTrace_append hprefix tailTrace_3048936
  have hstable : (prefixWord ++ tailWord_3048936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3048936).length < 2 ^ (prefixWord ++ tailWord_3048936).sum := by decide
  have hdescent : baseEnd_3048936 < baseStart_3048936 := by decide
  rcases family_descends (prefixWord ++ tailWord_3048936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3048949 : List Nat := [1, 3, 5, 1, 1, 2, 2, 1, 1, 2, 4]
def baseStart_3048949 : Nat := 118140960795 + 3048949 * 2 ^ 59
def prefixEnd_3048949 : Nat := 4983230072969 + 3 ^ 40 * 3048949 * 2
def baseEnd_3048949 : Nat := 1565576328045296706715645

theorem tailTrace_3048949 : CollatzResearch.WordTrace tailWord_3048949 prefixEnd_3048949 1565576328045296706715645 := by
  unfold tailWord_3048949
  simp only [CollatzResearch.WordTrace]
  refine ⟨111204305831185966877749901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74136203887457311251833267 111204305831185966877749901)
  ·
    refine ⟨41701614686694737579156213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111204305831185966877749901 41701614686694737579156213)
    ·
      refine ⟨3909526376877631648045895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 41701614686694737579156213 3909526376877631648045895)
      ·
        refine ⟨5864289565316447472068843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3909526376877631648045895 5864289565316447472068843)
        ·
          refine ⟨8796434347974671208103265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5864289565316447472068843 8796434347974671208103265)
          ·
            refine ⟨6597325760981003406077449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8796434347974671208103265 6597325760981003406077449)
            ·
              refine ⟨4947994320735752554558087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6597325760981003406077449 4947994320735752554558087)
              ·
                refine ⟨7421991481103628831837131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4947994320735752554558087 7421991481103628831837131)
                ·
                  refine ⟨11132987221655443247755697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7421991481103628831837131 11132987221655443247755697)
                  ·
                    refine ⟨8349740416241582435816773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11132987221655443247755697 8349740416241582435816773)
                    ·
                      refine ⟨1565576328045296706715645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8349740416241582435816773 1565576328045296706715645)
                      ·
                        rfl

theorem cell23_3048949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 2, 1, 1, 2, 4].length) (baseStart_3048949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3048949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3048949 prefixEnd_3048949 := by exact prefixLift 3048949
  have htrace : WordTrace (prefixWord ++ tailWord_3048949) baseStart_3048949 baseEnd_3048949 := by
    simpa [prefixWord, tailWord_3048949, baseEnd_3048949] using wordTrace_append hprefix tailTrace_3048949
  have hstable : (prefixWord ++ tailWord_3048949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3048949).length < 2 ^ (prefixWord ++ tailWord_3048949).sum := by decide
  have hdescent : baseEnd_3048949 < baseStart_3048949 := by decide
  rcases family_descends (prefixWord ++ tailWord_3048949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3048952 : List Nat := [2, 1, 2, 1, 1, 6, 2, 1, 1, 3, 3]
def baseStart_3048952 : Nat := 118140960795 + 3048952 * 2 ^ 59
def prefixEnd_3048952 : Nat := 4983230072969 + 3 ^ 40 * 3048952 * 2
def baseEnd_3048952 : Nat := 1565577868487260194978131

theorem tailTrace_3048952 : CollatzResearch.WordTrace tailWord_3048952 prefixEnd_3048952 1565577868487260194978131 := by
  unfold tailWord_3048952
  simp only [CollatzResearch.WordTrace]
  refine ⟨55602207625087549195054555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74136276833450065593406073 55602207625087549195054555)
  ·
    refine ⟨83403311437631323792581833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55602207625087549195054555 83403311437631323792581833)
    ·
      refine ⟨62552483578223492844436375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83403311437631323792581833 62552483578223492844436375)
      ·
        refine ⟨93828725367335239266654563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62552483578223492844436375 93828725367335239266654563)
        ·
          refine ⟨140743088051002858899981845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93828725367335239266654563 140743088051002858899981845)
          ·
            refine ⟨6597332252390759010936649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 140743088051002858899981845 6597332252390759010936649)
            ·
              refine ⟨4947999189293069258202487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6597332252390759010936649 4947999189293069258202487)
              ·
                refine ⟨7421998783939603887303731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4947999189293069258202487 7421998783939603887303731)
                ·
                  refine ⟨11132998175909405830955597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7421998783939603887303731 11132998175909405830955597)
                  ·
                    refine ⟨4174874315966027186608349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11132998175909405830955597 4174874315966027186608349)
                    ·
                      refine ⟨1565577868487260194978131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4174874315966027186608349 1565577868487260194978131)
                      ·
                        rfl

theorem cell23_3048952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 2, 1, 1, 3, 3].length) (baseStart_3048952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3048952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3048952 prefixEnd_3048952 := by exact prefixLift 3048952
  have htrace : WordTrace (prefixWord ++ tailWord_3048952) baseStart_3048952 baseEnd_3048952 := by
    simpa [prefixWord, tailWord_3048952, baseEnd_3048952] using wordTrace_append hprefix tailTrace_3048952
  have hstable : (prefixWord ++ tailWord_3048952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3048952).length < 2 ^ (prefixWord ++ tailWord_3048952).sum := by decide
  have hdescent : baseEnd_3048952 < baseStart_3048952 := by decide
  rcases family_descends (prefixWord ++ tailWord_3048952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3048973 : List Nat := [1, 7, 1, 1, 2, 1, 1, 3, 1, 2, 3]
def baseStart_3048973 : Nat := 118140960795 + 3048973 * 2 ^ 59
def prefixEnd_3048973 : Nat := 4983230072969 + 3 ^ 40 * 3048973 * 2
def baseEnd_3048973 : Nat := 1565588651581004612815535

theorem tailTrace_3048973 : CollatzResearch.WordTrace tailWord_3048973 prefixEnd_3048973 1565588651581004612815535 := by
  unfold tailWord_3048973
  simp only [CollatzResearch.WordTrace]
  refine ⟨111205181183099018976623573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74136787455399345984415715 111205181183099018976623573)
  ·
    refine ⟨2606371433978883257264615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 111205181183099018976623573 2606371433978883257264615)
    ·
      refine ⟨3909557150968324885896923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2606371433978883257264615 3909557150968324885896923)
      ·
        refine ⟨5864335726452487328845385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3909557150968324885896923 5864335726452487328845385)
        ·
          refine ⟨4398251794839365496634039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5864335726452487328845385 4398251794839365496634039)
          ·
            refine ⟨6597377692259048244951059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4398251794839365496634039 6597377692259048244951059)
            ·
              refine ⟨9896066538388572367426589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6597377692259048244951059 9896066538388572367426589)
              ·
                refine ⟨3711024951895714637784971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9896066538388572367426589 3711024951895714637784971)
                ·
                  refine ⟨5566537427843571956677457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3711024951895714637784971 5566537427843571956677457)
                  ·
                    refine ⟨4174903070882678967508093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5566537427843571956677457 4174903070882678967508093)
                    ·
                      refine ⟨1565588651581004612815535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4174903070882678967508093 1565588651581004612815535)
                      ·
                        rfl

theorem cell23_3048973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 1, 3, 1, 2, 3].length) (baseStart_3048973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3048973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3048973 prefixEnd_3048973 := by exact prefixLift 3048973
  have htrace : WordTrace (prefixWord ++ tailWord_3048973) baseStart_3048973 baseEnd_3048973 := by
    simpa [prefixWord, tailWord_3048973, baseEnd_3048973] using wordTrace_append hprefix tailTrace_3048973
  have hstable : (prefixWord ++ tailWord_3048973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3048973).length < 2 ^ (prefixWord ++ tailWord_3048973).sum := by decide
  have hdescent : baseEnd_3048973 < baseStart_3048973 := by decide
  rcases family_descends (prefixWord ++ tailWord_3048973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3048979 : List Nat := [1, 1, 1, 2, 1, 7, 1, 3, 1, 3, 2]
def baseStart_3048979 : Nat := 118140960795 + 3048979 * 2 ^ 59
def prefixEnd_3048979 : Nat := 4983230072969 + 3 ^ 40 * 3048979 * 2
def baseEnd_3048979 : Nat := 1565591732464931589340507

theorem tailTrace_3048979 : CollatzResearch.WordTrace tailWord_3048979 prefixEnd_3048979 1565591732464931589340507 := by
  unfold tailWord_3048979
  simp only [CollatzResearch.WordTrace]
  refine ⟨111205400021077282001341991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74136933347384854667561327 111205400021077282001341991)
  ·
    refine ⟨166808100031615923002012987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111205400021077282001341991 166808100031615923002012987)
    ·
      refine ⟨250212150047423884503019481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166808100031615923002012987 250212150047423884503019481)
      ·
        refine ⟨187659112535567913377264611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 250212150047423884503019481 187659112535567913377264611)
        ·
          refine ⟨281488668803351870065896917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 187659112535567913377264611 281488668803351870065896917)
          ·
            refine ⟨6597390675078559454669459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 281488668803351870065896917 6597390675078559454669459)
            ·
              refine ⟨9896086012617839182004189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6597390675078559454669459 9896086012617839182004189)
              ·
                refine ⟨3711032254731689693251571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9896086012617839182004189 3711032254731689693251571)
                ·
                  refine ⟨5566548382097534539877357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3711032254731689693251571 5566548382097534539877357)
                  ·
                    refine ⟨2087455643286575452454009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5566548382097534539877357 2087455643286575452454009)
                    ·
                      refine ⟨1565591732464931589340507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2087455643286575452454009 1565591732464931589340507)
                      ·
                        rfl

theorem cell23_3048979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 1, 3, 1, 3, 2].length) (baseStart_3048979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3048979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3048979 prefixEnd_3048979 := by exact prefixLift 3048979
  have htrace : WordTrace (prefixWord ++ tailWord_3048979) baseStart_3048979 baseEnd_3048979 := by
    simpa [prefixWord, tailWord_3048979, baseEnd_3048979] using wordTrace_append hprefix tailTrace_3048979
  have hstable : (prefixWord ++ tailWord_3048979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3048979).length < 2 ^ (prefixWord ++ tailWord_3048979).sum := by decide
  have hdescent : baseEnd_3048979 < baseStart_3048979 := by decide
  rcases family_descends (prefixWord ++ tailWord_3048979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3049015 : List Nat := [1, 1, 3, 1, 2, 4, 2, 2, 7]
def baseStart_3049015 : Nat := 118140960795 + 3049015 * 2 ^ 59
def prefixEnd_3049015 : Nat := 4983230072969 + 3 ^ 40 * 3049015 * 2
def baseEnd_3049015 : Nat := 173956690863165938721149

theorem tailTrace_3049015 : CollatzResearch.WordTrace tailWord_3049015 prefixEnd_3049015 173956690863165938721149 := by
  unfold tailWord_3049015
  simp only [CollatzResearch.WordTrace]
  refine ⟨111206713048946860149652499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74137808699297906766434999 111206713048946860149652499)
  ·
    refine ⟨166810069573420290224478749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111206713048946860149652499 166810069573420290224478749)
    ·
      refine ⟨62553776090032608834179531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 166810069573420290224478749 62553776090032608834179531)
      ·
        refine ⟨93830664135048913251269297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62553776090032608834179531 93830664135048913251269297)
        ·
          refine ⟨70372998101286684938451973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93830664135048913251269297 70372998101286684938451973)
          ·
            refine ⟨13194937143991253425959745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 70372998101286684938451973 13194937143991253425959745)
            ·
              refine ⟨9896202857993440069469809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13194937143991253425959745 9896202857993440069469809)
              ·
                refine ⟨7422152143495080052102357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9896202857993440069469809 7422152143495080052102357)
                ·
                  refine ⟨173956690863165938721149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7422152143495080052102357 173956690863165938721149)
                  ·
                    rfl

theorem cell23_3049015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 2, 2, 7].length) (baseStart_3049015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3049015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3049015 prefixEnd_3049015 := by exact prefixLift 3049015
  have htrace : WordTrace (prefixWord ++ tailWord_3049015) baseStart_3049015 baseEnd_3049015 := by
    simpa [prefixWord, tailWord_3049015, baseEnd_3049015] using wordTrace_append hprefix tailTrace_3049015
  have hstable : (prefixWord ++ tailWord_3049015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3049015).length < 2 ^ (prefixWord ++ tailWord_3049015).sum := by decide
  have hdescent : baseEnd_3049015 < baseStart_3049015 := by decide
  rcases family_descends (prefixWord ++ tailWord_3049015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3049065 : List Nat := [1, 2, 1, 1, 1, 4, 2, 1, 3, 3, 4]
def baseStart_3049065 : Nat := 118140960795 + 3049065 * 2 ^ 59
def prefixEnd_3049065 : Nat := 4983230072969 + 3 ^ 40 * 3049065 * 2
def baseEnd_3049065 : Nat := 1565635891801218252865111

theorem tailTrace_3049065 : CollatzResearch.WordTrace tailWord_3049065 prefixEnd_3049065 1565635891801218252865111 := by
  unfold tailWord_3049065
  simp only [CollatzResearch.WordTrace]
  refine ⟨111208536698765718688972649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74139024465843812459315099 111208536698765718688972649)
  ·
    refine ⟨83406402524074289016729487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111208536698765718688972649 83406402524074289016729487)
    ·
      refine ⟨125109603786111433525094231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83406402524074289016729487 125109603786111433525094231)
      ·
        refine ⟨187664405679167150287641347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125109603786111433525094231 187664405679167150287641347)
        ·
          refine ⟨281496608518750725431462021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 187664405679167150287641347 281496608518750725431462021)
          ·
            refine ⟨52780614097265761018399129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 281496608518750725431462021 52780614097265761018399129)
            ·
              refine ⟨39585460572949320763799347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52780614097265761018399129 39585460572949320763799347)
              ·
                refine ⟨59378190859423981145699021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39585460572949320763799347 59378190859423981145699021)
                ·
                  refine ⟨22266821572283992929637133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59378190859423981145699021 22266821572283992929637133)
                  ·
                    refine ⟨8350058089606497348613925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22266821572283992929637133 8350058089606497348613925)
                    ·
                      refine ⟨1565635891801218252865111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8350058089606497348613925 1565635891801218252865111)
                      ·
                        rfl

theorem cell23_3049065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 1, 3, 3, 4].length) (baseStart_3049065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3049065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3049065 prefixEnd_3049065 := by exact prefixLift 3049065
  have htrace : WordTrace (prefixWord ++ tailWord_3049065) baseStart_3049065 baseEnd_3049065 := by
    simpa [prefixWord, tailWord_3049065, baseEnd_3049065] using wordTrace_append hprefix tailTrace_3049065
  have hstable : (prefixWord ++ tailWord_3049065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3049065).length < 2 ^ (prefixWord ++ tailWord_3049065).sum := by decide
  have hdescent : baseEnd_3049065 < baseStart_3049065 := by decide
  rcases family_descends (prefixWord ++ tailWord_3049065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3049082 : List Nat := [3, 1, 1, 1, 1, 1, 1, 3, 3, 6, 2]
def baseStart_3049082 : Nat := 118140960795 + 3049082 * 2 ^ 59
def prefixEnd_3049082 : Nat := 4983230072969 + 3 ^ 40 * 3049082 * 2
def baseEnd_3049082 : Nat := 1565644620972344686352533

theorem tailTrace_3049082 : CollatzResearch.WordTrace tailWord_3049082 prefixEnd_3049082 1565644620972344686352533 := by
  unfold tailWord_3049082
  simp only [CollatzResearch.WordTrace]
  refine ⟨27802289184926032648085375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74139437826469420394894333 27802289184926032648085375)
  ·
    refine ⟨41703433777389048972128063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27802289184926032648085375 41703433777389048972128063)
    ·
      refine ⟨62555150666083573458192095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41703433777389048972128063 62555150666083573458192095)
      ·
        refine ⟨93832725999125360187288143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62555150666083573458192095 93832725999125360187288143)
        ·
          refine ⟨140749088998688040280932215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93832725999125360187288143 140749088998688040280932215)
          ·
            refine ⟨211123633498032060421398323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140749088998688040280932215 211123633498032060421398323)
            ·
              refine ⟨316685450247048090632097485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 211123633498032060421398323 316685450247048090632097485)
              ·
                refine ⟨118757043842643033987036557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 316685450247048090632097485 118757043842643033987036557)
                ·
                  refine ⟨44533891440991137745138709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 118757043842643033987036557 44533891440991137745138709)
                  ·
                    refine ⟨2087526161296459581803377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 44533891440991137745138709 2087526161296459581803377)
                    ·
                      refine ⟨1565644620972344686352533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2087526161296459581803377 1565644620972344686352533)
                      ·
                        rfl

theorem cell23_3049082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 3, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 3, 3, 6, 2].length) (baseStart_3049082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3049082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3049082 prefixEnd_3049082 := by exact prefixLift 3049082
  have htrace : WordTrace (prefixWord ++ tailWord_3049082) baseStart_3049082 baseEnd_3049082 := by
    simpa [prefixWord, tailWord_3049082, baseEnd_3049082] using wordTrace_append hprefix tailTrace_3049082
  have hstable : (prefixWord ++ tailWord_3049082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3049082).length < 2 ^ (prefixWord ++ tailWord_3049082).sum := by decide
  have hdescent : baseEnd_3049082 < baseStart_3049082 := by decide
  rcases family_descends (prefixWord ++ tailWord_3049082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3049116 : List Nat := [2, 2, 3, 2, 3, 1, 1, 1, 2, 4, 2]
def baseStart_3049116 : Nat := 118140960795 + 3049116 * 2 ^ 59
def prefixEnd_3049116 : Nat := 4983230072969 + 3 ^ 40 * 3049116 * 2
def baseEnd_3049116 : Nat := 1565662079314597553327377

theorem tailTrace_3049116 : CollatzResearch.WordTrace tailWord_3049116 prefixEnd_3049116 1565662079314597553327377 := by
  unfold tailWord_3049116
  simp only [CollatzResearch.WordTrace]
  refine ⟨55605198410790477199539601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74140264547720636266052801 55605198410790477199539601)
  ·
    refine ⟨41703898808092857899654701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55605198410790477199539601 41703898808092857899654701)
    ·
      refine ⟨15638962053034821712370513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41703898808092857899654701 15638962053034821712370513)
      ·
        refine ⟨11729221539776116284277885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15638962053034821712370513 11729221539776116284277885)
        ·
          refine ⟨4398458077416043606604207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11729221539776116284277885 4398458077416043606604207)
          ·
            refine ⟨6597687116124065409906311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4398458077416043606604207 6597687116124065409906311)
            ·
              refine ⟨9896530674186098114859467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6597687116124065409906311 9896530674186098114859467)
              ·
                refine ⟨14844796011279147172289201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9896530674186098114859467 14844796011279147172289201)
                ·
                  refine ⟨11133597008459360379216901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14844796011279147172289201 11133597008459360379216901)
                  ·
                    refine ⟨2087549439086130071103169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11133597008459360379216901 2087549439086130071103169)
                    ·
                      refine ⟨1565662079314597553327377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2087549439086130071103169 1565662079314597553327377)
                      ·
                        rfl

theorem cell23_3049116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 1, 1, 2, 4, 2].length) (baseStart_3049116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3049116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3049116 prefixEnd_3049116 := by exact prefixLift 3049116
  have htrace : WordTrace (prefixWord ++ tailWord_3049116) baseStart_3049116 baseEnd_3049116 := by
    simpa [prefixWord, tailWord_3049116, baseEnd_3049116] using wordTrace_append hprefix tailTrace_3049116
  have hstable : (prefixWord ++ tailWord_3049116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3049116).length < 2 ^ (prefixWord ++ tailWord_3049116).sum := by decide
  have hdescent : baseEnd_3049116 < baseStart_3049116 := by decide
  rcases family_descends (prefixWord ++ tailWord_3049116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3049149 : List Nat := [1, 4, 1, 2, 1, 2, 1, 2, 5, 1, 3]
def baseStart_3049149 : Nat := 118140960795 + 3049149 * 2 ^ 59
def prefixEnd_3049149 : Nat := 4983230072969 + 3 ^ 40 * 3049149 * 2
def baseEnd_3049149 : Nat := 1565679024176195924214725

theorem tailTrace_3049149 : CollatzResearch.WordTrace tailWord_3049149 prefixEnd_3049149 1565679024176195924214725 := by
  unfold tailWord_3049149
  simp only [CollatzResearch.WordTrace]
  refine ⟨111211600430461401035030501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74141066953640934023353667 111211600430461401035030501)
  ·
    refine ⟨20852175080711512694068219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 111211600430461401035030501 20852175080711512694068219)
    ·
      refine ⟨31278262621067269041102329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20852175080711512694068219 31278262621067269041102329)
      ·
        refine ⟨23458696965800451780826747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31278262621067269041102329 23458696965800451780826747)
        ·
          refine ⟨35188045448700677671240121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23458696965800451780826747 35188045448700677671240121)
          ·
            refine ⟨26391034086525508253430091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35188045448700677671240121 26391034086525508253430091)
            ·
              refine ⟨39586551129788262380145137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26391034086525508253430091 39586551129788262380145137)
              ·
                refine ⟨29689913347341196785108853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39586551129788262380145137 29689913347341196785108853)
                ·
                  refine ⟨2783429376313237198603955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 29689913347341196785108853 2783429376313237198603955)
                  ·
                    refine ⟨4175144064469855797905933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2783429376313237198603955 4175144064469855797905933)
                    ·
                      refine ⟨1565679024176195924214725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4175144064469855797905933 1565679024176195924214725)
                      ·
                        rfl

theorem cell23_3049149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 2, 5, 1, 3].length) (baseStart_3049149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3049149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3049149 prefixEnd_3049149 := by exact prefixLift 3049149
  have htrace : WordTrace (prefixWord ++ tailWord_3049149) baseStart_3049149 baseEnd_3049149 := by
    simpa [prefixWord, tailWord_3049149, baseEnd_3049149] using wordTrace_append hprefix tailTrace_3049149
  have hstable : (prefixWord ++ tailWord_3049149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3049149).length < 2 ^ (prefixWord ++ tailWord_3049149).sum := by decide
  have hdescent : baseEnd_3049149 < baseStart_3049149 := by decide
  rcases family_descends (prefixWord ++ tailWord_3049149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3049159 : List Nat := [1, 1, 4, 1, 1, 1, 4, 1, 4, 3, 2]
def baseStart_3049159 : Nat := 118140960795 + 3049159 * 2 ^ 59
def prefixEnd_3049159 : Nat := 4983230072969 + 3 ^ 40 * 3049159 * 2
def baseEnd_3049159 : Nat := 1565684158982740885089679

theorem tailTrace_3049159 : CollatzResearch.WordTrace tailWord_3049159 prefixEnd_3049159 1565684158982740885089679 := by
  unfold tailWord_3049159
  simp only [CollatzResearch.WordTrace]
  refine ⟨111211965160425172742894531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74141310106950115161929687 111211965160425172742894531)
  ·
    refine ⟨166817947740637759114341797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111211965160425172742894531 166817947740637759114341797)
    ·
      refine ⟨31278365201369579833939087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 166817947740637759114341797 31278365201369579833939087)
      ·
        refine ⟨46917547802054369750908631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31278365201369579833939087 46917547802054369750908631)
        ·
          refine ⟨70376321703081554626362947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46917547802054369750908631 70376321703081554626362947)
          ·
            refine ⟨105564482554622331939544421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70376321703081554626362947 105564482554622331939544421)
            ·
              refine ⟨19793340478991687238664579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 105564482554622331939544421 19793340478991687238664579)
              ·
                refine ⟨29690010718487530857996869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19793340478991687238664579 29690010718487530857996869)
                ·
                  refine ⟨5566877009716412035874413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29690010718487530857996869 5566877009716412035874413)
                  ·
                    refine ⟨2087578878643654513452905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5566877009716412035874413 2087578878643654513452905)
                    ·
                      refine ⟨1565684158982740885089679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2087578878643654513452905 1565684158982740885089679)
                      ·
                        rfl

theorem cell23_3049159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 1, 4, 3, 2].length) (baseStart_3049159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3049159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3049159 prefixEnd_3049159 := by exact prefixLift 3049159
  have htrace : WordTrace (prefixWord ++ tailWord_3049159) baseStart_3049159 baseEnd_3049159 := by
    simpa [prefixWord, tailWord_3049159, baseEnd_3049159] using wordTrace_append hprefix tailTrace_3049159
  have hstable : (prefixWord ++ tailWord_3049159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3049159).length < 2 ^ (prefixWord ++ tailWord_3049159).sum := by decide
  have hdescent : baseEnd_3049159 < baseStart_3049159 := by decide
  rcases family_descends (prefixWord ++ tailWord_3049159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3049166 : List Nat := [4, 1, 1, 1, 3, 1, 4, 1, 3, 1, 3]
def baseStart_3049166 : Nat := 118140960795 + 3049166 * 2 ^ 59
def prefixEnd_3049166 : Nat := 4983230072969 + 3 ^ 40 * 3049166 * 2
def baseEnd_3049166 : Nat := 1565687753347322357702147

theorem tailTrace_3049166 : CollatzResearch.WordTrace tailWord_3049166 prefixEnd_3049166 1565687753347322357702147 := by
  unfold tailWord_3049166
  simp only [CollatzResearch.WordTrace]
  refine ⟨13901527558924976617299919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74141480314266541958932901 13901527558924976617299919)
  ·
    refine ⟨20852291338387464925949879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13901527558924976617299919 20852291338387464925949879)
    ·
      refine ⟨31278437007581197388924819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20852291338387464925949879 31278437007581197388924819)
      ·
        refine ⟨46917655511371796083387229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31278437007581197388924819 46917655511371796083387229)
        ·
          refine ⟨17594120816764423531270211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46917655511371796083387229 17594120816764423531270211)
          ·
            refine ⟨26391181225146635296905317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17594120816764423531270211 26391181225146635296905317)
            ·
              refine ⟨4948346479714994118169747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26391181225146635296905317 4948346479714994118169747)
              ·
                refine ⟨7422519719572491177254621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4948346479714994118169747 7422519719572491177254621)
                ·
                  refine ⟨2783444894839684191470483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7422519719572491177254621 2783444894839684191470483)
                  ·
                    refine ⟨4175167342259526287205725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2783444894839684191470483 4175167342259526287205725)
                    ·
                      refine ⟨1565687753347322357702147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4175167342259526287205725 1565687753347322357702147)
                      ·
                        rfl

theorem cell23_3049166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 4, 1, 3, 1, 3].length) (baseStart_3049166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3049166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3049166 prefixEnd_3049166 := by exact prefixLift 3049166
  have htrace : WordTrace (prefixWord ++ tailWord_3049166) baseStart_3049166 baseEnd_3049166 := by
    simpa [prefixWord, tailWord_3049166, baseEnd_3049166] using wordTrace_append hprefix tailTrace_3049166
  have hstable : (prefixWord ++ tailWord_3049166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3049166).length < 2 ^ (prefixWord ++ tailWord_3049166).sum := by decide
  have hdescent : baseEnd_3049166 < baseStart_3049166 := by decide
  rcases family_descends (prefixWord ++ tailWord_3049166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3049189 : List Nat := [1, 3, 1, 4, 1, 1, 1, 1, 2, 6, 2]
def baseStart_3049189 : Nat := 118140960795 + 3049189 * 2 ^ 59
def prefixEnd_3049189 : Nat := 4983230072969 + 3 ^ 40 * 3049189 * 2
def baseEnd_3049189 : Nat := 1565699563402375767714541

theorem tailTrace_3049189 : CollatzResearch.WordTrace tailWord_3049189 prefixEnd_3049189 1565699563402375767714541 := by
  unfold tailWord_3049189
  simp only [CollatzResearch.WordTrace]
  refine ⟨111213059350316487866486621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74142039566877658577657747 111213059350316487866486621)
  ·
    refine ⟨41704897256368682949932483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111213059350316487866486621 41704897256368682949932483)
    ·
      refine ⟨62557345884553024424898725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41704897256368682949932483 62557345884553024424898725)
      ·
        refine ⟨11729502353353692079668511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 62557345884553024424898725 11729502353353692079668511)
        ·
          refine ⟨17594253530030538119502767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11729502353353692079668511 17594253530030538119502767)
          ·
            refine ⟨26391380295045807179254151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17594253530030538119502767 26391380295045807179254151)
            ·
              refine ⟨39587070442568710768881227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26391380295045807179254151 39587070442568710768881227)
              ·
                refine ⟨59380605663853066153321841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39587070442568710768881227 59380605663853066153321841)
                ·
                  refine ⟨44535454247889799614991381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59380605663853066153321841 44535454247889799614991381)
                  ·
                    refine ⟨2087599417869834356952721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 44535454247889799614991381 2087599417869834356952721)
                    ·
                      refine ⟨1565699563402375767714541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2087599417869834356952721 1565699563402375767714541)
                      ·
                        rfl

theorem cell23_3049189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 1, 2, 6, 2].length) (baseStart_3049189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3049189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3049189 prefixEnd_3049189 := by exact prefixLift 3049189
  have htrace : WordTrace (prefixWord ++ tailWord_3049189) baseStart_3049189 baseEnd_3049189 := by
    simpa [prefixWord, tailWord_3049189, baseEnd_3049189] using wordTrace_append hprefix tailTrace_3049189
  have hstable : (prefixWord ++ tailWord_3049189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3049189).length < 2 ^ (prefixWord ++ tailWord_3049189).sum := by decide
  have hdescent : baseEnd_3049189 < baseStart_3049189 := by decide
  rcases family_descends (prefixWord ++ tailWord_3049189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3049206 : List Nat := [5, 1, 1, 1, 1, 3, 2, 3, 1, 1, 4]
def baseStart_3049206 : Nat := 118140960795 + 3049206 * 2 ^ 59
def prefixEnd_3049206 : Nat := 4983230072969 + 3 ^ 40 * 3049206 * 2
def baseEnd_3049206 : Nat := 1565708292573502201201963

theorem tailTrace_3049206 : CollatzResearch.WordTrace tailWord_3049206 prefixEnd_3049206 1565708292573502201201963 := by
  unfold tailWord_3049206
  simp only [CollatzResearch.WordTrace]
  refine ⟨6950854961953431235615967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 74142452927503266513236981 6950854961953431235615967)
  ·
    refine ⟨10426282442930146853423951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6950854961953431235615967 10426282442930146853423951)
    ·
      refine ⟨15639423664395220280135927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10426282442930146853423951 15639423664395220280135927)
      ·
        refine ⟨23459135496592830420203891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15639423664395220280135927 23459135496592830420203891)
        ·
          refine ⟨35188703244889245630305837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23459135496592830420203891 35188703244889245630305837)
          ·
            refine ⟨13195763716833467111364689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35188703244889245630305837 13195763716833467111364689)
            ·
              refine ⟨9896822787625100333523517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13195763716833467111364689 9896822787625100333523517)
              ·
                refine ⟨3711308545359412625071319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9896822787625100333523517 3711308545359412625071319)
                ·
                  refine ⟨5566962818039118937606979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3711308545359412625071319 5566962818039118937606979)
                  ·
                    refine ⟨8350444227058678406410469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5566962818039118937606979 8350444227058678406410469)
                    ·
                      refine ⟨1565708292573502201201963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8350444227058678406410469 1565708292573502201201963)
                      ·
                        rfl

theorem cell23_3049206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 2, 3, 1, 1, 4].length) (baseStart_3049206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3049206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3049206 prefixEnd_3049206 := by exact prefixLift 3049206
  have htrace : WordTrace (prefixWord ++ tailWord_3049206) baseStart_3049206 baseEnd_3049206 := by
    simpa [prefixWord, tailWord_3049206, baseEnd_3049206] using wordTrace_append hprefix tailTrace_3049206
  have hstable : (prefixWord ++ tailWord_3049206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3049206).length < 2 ^ (prefixWord ++ tailWord_3049206).sum := by decide
  have hdescent : baseEnd_3049206 < baseStart_3049206 := by decide
  rcases family_descends (prefixWord ++ tailWord_3049206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3049256 : List Nat := [2, 1, 5, 1, 1, 3, 1, 2, 1, 3, 3]
def baseStart_3049256 : Nat := 118140960795 + 3049256 * 2 ^ 59
def prefixEnd_3049256 : Nat := 4983230072969 + 3 ^ 40 * 3049256 * 2
def baseEnd_3049256 : Nat := 1565733966606227005576733

theorem tailTrace_3049256 : CollatzResearch.WordTrace tailWord_3049256 prefixEnd_3049256 1565733966606227005576733 := by
  unfold tailWord_3049256
  simp only [CollatzResearch.WordTrace]
  refine ⟨55607751520536879154587811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74143668694049172206117081 55607751520536879154587811)
  ·
    refine ⟨83411627280805318731881717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55607751520536879154587811 83411627280805318731881717)
    ·
      refine ⟨7819840057575498631113911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 83411627280805318731881717 7819840057575498631113911)
      ·
        refine ⟨11729760086363247946670867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7819840057575498631113911 11729760086363247946670867)
        ·
          refine ⟨17594640129544871920006301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11729760086363247946670867 17594640129544871920006301)
          ·
            refine ⟨6597990048579326970002363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17594640129544871920006301 6597990048579326970002363)
            ·
              refine ⟨9896985072868990455003545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6597990048579326970002363 9896985072868990455003545)
              ·
                refine ⟨7422738804651742841252659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9896985072868990455003545 7422738804651742841252659)
                ·
                  refine ⟨11134108206977614261878989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7422738804651742841252659 11134108206977614261878989)
                  ·
                    refine ⟨4175290577616605348204621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11134108206977614261878989 4175290577616605348204621)
                    ·
                      refine ⟨1565733966606227005576733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4175290577616605348204621 1565733966606227005576733)
                      ·
                        rfl

theorem cell23_3049256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 1, 2, 1, 3, 3].length) (baseStart_3049256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3049256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3049256 prefixEnd_3049256 := by exact prefixLift 3049256
  have htrace : WordTrace (prefixWord ++ tailWord_3049256) baseStart_3049256 baseEnd_3049256 := by
    simpa [prefixWord, tailWord_3049256, baseEnd_3049256] using wordTrace_append hprefix tailTrace_3049256
  have hstable : (prefixWord ++ tailWord_3049256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3049256).length < 2 ^ (prefixWord ++ tailWord_3049256).sum := by decide
  have hdescent : baseEnd_3049256 < baseStart_3049256 := by decide
  rcases family_descends (prefixWord ++ tailWord_3049256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3049296 : List Nat := [2, 1, 1, 1, 1, 4, 1, 2, 6, 2, 2]
def baseStart_3049296 : Nat := 118140960795 + 3049296 * 2 ^ 59
def prefixEnd_3049296 : Nat := 4983230072969 + 3 ^ 40 * 3049296 * 2
def baseEnd_3049296 : Nat := 1565754505832406849076549

theorem tailTrace_3049296 : CollatzResearch.WordTrace tailWord_3049296 prefixEnd_3049296 1565754505832406849076549 := by
  unfold tailWord_3049296
  simp only [CollatzResearch.WordTrace]
  refine ⟨55608480980464422570315871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74144641307285896760421161 55608480980464422570315871)
  ·
    refine ⟨83412721470696633855473807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55608480980464422570315871 83412721470696633855473807)
    ·
      refine ⟨125119082206044950783210711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83412721470696633855473807 125119082206044950783210711)
      ·
        refine ⟨187678623309067426174816067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125119082206044950783210711 187678623309067426174816067)
        ·
          refine ⟨281517934963601139262224101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 187678623309067426174816067 281517934963601139262224101)
          ·
            refine ⟨52784612805675213611667019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 281517934963601139262224101 52784612805675213611667019)
            ·
              refine ⟨79176919208512820417500529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52784612805675213611667019 79176919208512820417500529)
              ·
                refine ⟨59382689406384615313125397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79176919208512820417500529 59382689406384615313125397)
                ·
                  refine ⟨2783563565924278842802753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 59382689406384615313125397 2783563565924278842802753)
                  ·
                    refine ⟨2087672674443209132102065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2783563565924278842802753 2087672674443209132102065)
                    ·
                      refine ⟨1565754505832406849076549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2087672674443209132102065 1565754505832406849076549)
                      ·
                        rfl

theorem cell23_3049296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 2, 6, 2, 2].length) (baseStart_3049296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3049296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3049296 prefixEnd_3049296 := by exact prefixLift 3049296
  have htrace : WordTrace (prefixWord ++ tailWord_3049296) baseStart_3049296 baseEnd_3049296 := by
    simpa [prefixWord, tailWord_3049296, baseEnd_3049296] using wordTrace_append hprefix tailTrace_3049296
  have hstable : (prefixWord ++ tailWord_3049296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3049296).length < 2 ^ (prefixWord ++ tailWord_3049296).sum := by decide
  have hdescent : baseEnd_3049296 < baseStart_3049296 := by decide
  rcases family_descends (prefixWord ++ tailWord_3049296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3049326 : List Nat := [4, 1, 2, 3, 1, 1, 1, 2, 2, 2, 4]
def baseStart_3049326 : Nat := 118140960795 + 3049326 * 2 ^ 59
def prefixEnd_3049326 : Nat := 4983230072969 + 3 ^ 40 * 3049326 * 2
def baseEnd_3049326 : Nat := 1565769910252041731701411

theorem tailTrace_3049326 : CollatzResearch.WordTrace tailWord_3049326 prefixEnd_3049326 1565769910252041731701411 := by
  unfold tailWord_3049326
  simp only [CollatzResearch.WordTrace]
  refine ⟨13902257018852520033027979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74145370767213440176149221 13902257018852520033027979)
  ·
    refine ⟨20853385528278780049541969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13902257018852520033027979 20853385528278780049541969)
    ·
      refine ⟨15640039146209085037156477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20853385528278780049541969 15640039146209085037156477)
      ·
        refine ⟨5865014679828406888933679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15640039146209085037156477 5865014679828406888933679)
        ·
          refine ⟨8797522019742610333400519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5865014679828406888933679 8797522019742610333400519)
          ·
            refine ⟨13196283029613915500100779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8797522019742610333400519 13196283029613915500100779)
            ·
              refine ⟨19794424544420873250151169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13196283029613915500100779 19794424544420873250151169)
              ·
                refine ⟨14845818408315654937613377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19794424544420873250151169 14845818408315654937613377)
                ·
                  refine ⟨11134363806236741203210033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14845818408315654937613377 11134363806236741203210033)
                  ·
                    refine ⟨8350772854677555902407525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11134363806236741203210033 8350772854677555902407525)
                    ·
                      refine ⟨1565769910252041731701411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8350772854677555902407525 1565769910252041731701411)
                      ·
                        rfl

theorem cell23_3049326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 2, 2, 2, 4].length) (baseStart_3049326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3049326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3049326 prefixEnd_3049326 := by exact prefixLift 3049326
  have htrace : WordTrace (prefixWord ++ tailWord_3049326) baseStart_3049326 baseEnd_3049326 := by
    simpa [prefixWord, tailWord_3049326, baseEnd_3049326] using wordTrace_append hprefix tailTrace_3049326
  have hstable : (prefixWord ++ tailWord_3049326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3049326).length < 2 ^ (prefixWord ++ tailWord_3049326).sum := by decide
  have hdescent : baseEnd_3049326 < baseStart_3049326 := by decide
  rcases family_descends (prefixWord ++ tailWord_3049326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3049329 : List Nat := [1, 2, 2, 2, 1, 3, 1, 1, 4, 3, 3]
def baseStart_3049329 : Nat := 118140960795 + 3049329 * 2 ^ 59
def prefixEnd_3049329 : Nat := 4983230072969 + 3 ^ 40 * 3049329 * 2
def baseEnd_3049329 : Nat := 1565771450694005219963897

theorem tailTrace_3049329 : CollatzResearch.WordTrace tailWord_3049329 prefixEnd_3049329 1565771450694005219963897 := by
  unfold tailWord_3049329
  simp only [CollatzResearch.WordTrace]
  refine ⟨111218165569809291776583041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74145443713206194517722027 111218165569809291776583041)
  ·
    refine ⟨83413624177356968832437281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111218165569809291776583041 83413624177356968832437281)
    ·
      refine ⟨62560218133017726624327961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83413624177356968832437281 62560218133017726624327961)
      ·
        refine ⟨46920163599763294968245971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62560218133017726624327961 46920163599763294968245971)
        ·
          refine ⟨70380245399644942452368957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46920163599763294968245971 70380245399644942452368957)
          ·
            refine ⟨26392592024866853419638359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70380245399644942452368957 26392592024866853419638359)
            ·
              refine ⟨39588888037300280129457539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26392592024866853419638359 39588888037300280129457539)
              ·
                refine ⟨59383332055950420194186309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39588888037300280129457539 59383332055950420194186309)
                ·
                  refine ⟨11134374760490703786409933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 59383332055950420194186309 11134374760490703786409933)
                  ·
                    refine ⟨4175390535184013919903725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11134374760490703786409933 4175390535184013919903725)
                    ·
                      refine ⟨1565771450694005219963897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4175390535184013919903725 1565771450694005219963897)
                      ·
                        rfl

theorem cell23_3049329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 1, 4, 3, 3].length) (baseStart_3049329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3049329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3049329 prefixEnd_3049329 := by exact prefixLift 3049329
  have htrace : WordTrace (prefixWord ++ tailWord_3049329) baseStart_3049329 baseEnd_3049329 := by
    simpa [prefixWord, tailWord_3049329, baseEnd_3049329] using wordTrace_append hprefix tailTrace_3049329
  have hstable : (prefixWord ++ tailWord_3049329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3049329).length < 2 ^ (prefixWord ++ tailWord_3049329).sum := by decide
  have hdescent : baseEnd_3049329 < baseStart_3049329 := by decide
  rcases family_descends (prefixWord ++ tailWord_3049329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3049369 : List Nat := [1, 2, 1, 2, 1, 3, 4, 1, 1, 3, 4]
def baseStart_3049369 : Nat := 118140960795 + 3049369 * 2 ^ 59
def prefixEnd_3049369 : Nat := 4983230072969 + 3 ^ 40 * 3049369 * 2
def baseEnd_3049369 : Nat := 1565791989920185063463713

theorem tailTrace_3049369 : CollatzResearch.WordTrace tailWord_3049369 prefixEnd_3049369 1565791989920185063463713 := by
  unfold tailWord_3049369
  simp only [CollatzResearch.WordTrace]
  refine ⟨111219624489664378608039161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74146416326442919072026107 111219624489664378608039161)
  ·
    refine ⟨83414718367248283956029371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111219624489664378608039161 83414718367248283956029371)
    ·
      refine ⟨125122077550872425934044057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83414718367248283956029371 125122077550872425934044057)
      ·
        refine ⟨93841558163154319450533043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125122077550872425934044057 93841558163154319450533043)
        ·
          refine ⟨140762337244731479175799565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93841558163154319450533043 140762337244731479175799565)
          ·
            refine ⟨52785876466774304690924837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 140762337244731479175799565 52785876466774304690924837)
            ·
              refine ⟨9897351837520182129548407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52785876466774304690924837 9897351837520182129548407)
              ·
                refine ⟨14846027756280273194322611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9897351837520182129548407 14846027756280273194322611)
                ·
                  refine ⟨22269041634420409791483917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14846027756280273194322611 22269041634420409791483917)
                  ·
                    refine ⟨8350890612907653671806469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22269041634420409791483917 8350890612907653671806469)
                    ·
                      refine ⟨1565791989920185063463713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8350890612907653671806469 1565791989920185063463713)
                      ·
                        rfl

theorem cell23_3049369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 4, 1, 1, 3, 4].length) (baseStart_3049369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3049369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3049369 prefixEnd_3049369 := by exact prefixLift 3049369
  have htrace : WordTrace (prefixWord ++ tailWord_3049369) baseStart_3049369 baseEnd_3049369 := by
    simpa [prefixWord, tailWord_3049369, baseEnd_3049369] using wordTrace_append hprefix tailTrace_3049369
  have hstable : (prefixWord ++ tailWord_3049369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3049369).length < 2 ^ (prefixWord ++ tailWord_3049369).sum := by decide
  have hdescent : baseEnd_3049369 < baseStart_3049369 := by decide
  rcases family_descends (prefixWord ++ tailWord_3049369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3049470 : List Nat := [4, 2, 2, 2, 1, 1, 1, 1, 5, 1, 3]
def baseStart_3049470 : Nat := 118140960795 + 3049470 * 2 ^ 59
def prefixEnd_3049470 : Nat := 4983230072969 + 3 ^ 40 * 3049470 * 2
def baseEnd_3049470 : Nat := 1565843851466289168300749

theorem tailTrace_3049470 : CollatzResearch.WordTrace tailWord_3049470 prefixEnd_3049470 1565843851466289168300749 := by
  unfold tailWord_3049470
  simp only [CollatzResearch.WordTrace]
  refine ⟨13902913532787309107183233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74148872174865648571643909 13902913532787309107183233)
  ·
    refine ⟨10427185149590481830387425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13902913532787309107183233 10427185149590481830387425)
    ·
      refine ⟨7820388862192861372790569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10427185149590481830387425 7820388862192861372790569)
      ·
        refine ⟨5865291646644646029592927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7820388862192861372790569 5865291646644646029592927)
        ·
          refine ⟨8797937469966969044389391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5865291646644646029592927 8797937469966969044389391)
          ·
            refine ⟨13196906204950453566584087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8797937469966969044389391 13196906204950453566584087)
            ·
              refine ⟨19795359307425680349876131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13196906204950453566584087 19795359307425680349876131)
              ·
                refine ⟨29693038961138520524814197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19795359307425680349876131 29693038961138520524814197)
                ·
                  refine ⟨2783722402606736299201331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 29693038961138520524814197 2783722402606736299201331)
                  ·
                    refine ⟨4175583603910104448801997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2783722402606736299201331 4175583603910104448801997)
                    ·
                      refine ⟨1565843851466289168300749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4175583603910104448801997 1565843851466289168300749)
                      ·
                        rfl

theorem cell23_3049470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 1, 5, 1, 3].length) (baseStart_3049470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3049470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3049470 prefixEnd_3049470 := by exact prefixLift 3049470
  have htrace : WordTrace (prefixWord ++ tailWord_3049470) baseStart_3049470 baseEnd_3049470 := by
    simpa [prefixWord, tailWord_3049470, baseEnd_3049470] using wordTrace_append hprefix tailTrace_3049470
  have hstable : (prefixWord ++ tailWord_3049470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3049470).length < 2 ^ (prefixWord ++ tailWord_3049470).sum := by decide
  have hdescent : baseEnd_3049470 < baseStart_3049470 := by decide
  rcases family_descends (prefixWord ++ tailWord_3049470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3049486 : List Nat := [4, 1, 1, 2, 2, 1, 1, 4, 1, 6]
def baseStart_3049486 : Nat := 118140960795 + 3049486 * 2 ^ 59
def prefixEnd_3049486 : Nat := 4983230072969 + 3 ^ 40 * 3049486 * 2
def baseEnd_3049486 : Nat := 521950689052253701900225

theorem tailTrace_3049486 : CollatzResearch.WordTrace tailWord_3049486 prefixEnd_3049486 521950689052253701900225 := by
  unfold tailWord_3049486
  simp only [CollatzResearch.WordTrace]
  refine ⟨13902986478780063448756039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74149261220160338393365541 13902986478780063448756039)
  ·
    refine ⟨20854479718170095173134059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13902986478780063448756039 20854479718170095173134059)
    ·
      refine ⟨31281719577255142759701089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20854479718170095173134059 31281719577255142759701089)
      ·
        refine ⟨23461289682941357069775817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31281719577255142759701089 23461289682941357069775817)
        ·
          refine ⟨17595967262206017802331863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23461289682941357069775817 17595967262206017802331863)
          ·
            refine ⟨26393950893309026703497795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17595967262206017802331863 26393950893309026703497795)
            ·
              refine ⟨39590926339963540055246693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26393950893309026703497795 39590926339963540055246693)
              ·
                refine ⟨7423298688743163760358755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39590926339963540055246693 7423298688743163760358755)
                ·
                  refine ⟨11134948033114745640538133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7423298688743163760358755 11134948033114745640538133)
                  ·
                    refine ⟨521950689052253701900225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11134948033114745640538133 521950689052253701900225)
                    ·
                      rfl

theorem cell23_3049486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 4, 1, 6].length) (baseStart_3049486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3049486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3049486 prefixEnd_3049486 := by exact prefixLift 3049486
  have htrace : WordTrace (prefixWord ++ tailWord_3049486) baseStart_3049486 baseEnd_3049486 := by
    simpa [prefixWord, tailWord_3049486, baseEnd_3049486] using wordTrace_append hprefix tailTrace_3049486
  have hstable : (prefixWord ++ tailWord_3049486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3049486).length < 2 ^ (prefixWord ++ tailWord_3049486).sum := by decide
  have hdescent : baseEnd_3049486 < baseStart_3049486 := by decide
  rcases family_descends (prefixWord ++ tailWord_3049486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3049489 : List Nat := [1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 6]
def baseStart_3049489 : Nat := 118140960795 + 3049489 * 2 ^ 59
def prefixEnd_3049489 : Nat := 4983230072969 + 3 ^ 40 * 3049489 * 2
def baseEnd_3049489 : Nat := 1565853607598724593963161

theorem tailTrace_3049489 : CollatzResearch.WordTrace tailWord_3049489 prefixEnd_3049489 1565853607598724593963161 := by
  unfold tailWord_3049489
  simp only [CollatzResearch.WordTrace]
  refine ⟨111224001249229639102407521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74149334166153092734938347 111224001249229639102407521)
  ·
    refine ⟨83418000936922229326805641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111224001249229639102407521 83418000936922229326805641)
    ·
      refine ⟨62563500702691671995104231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83418000936922229326805641 62563500702691671995104231)
      ·
        refine ⟨93845251054037507992656347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62563500702691671995104231 93845251054037507992656347)
        ·
          refine ⟨140767876581056261988984521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93845251054037507992656347 140767876581056261988984521)
          ·
            refine ⟨105575907435792196491738391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 140767876581056261988984521 105575907435792196491738391)
            ·
              refine ⟨158363861153688294737607587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105575907435792196491738391 158363861153688294737607587)
              ·
                refine ⟨237545791730532442106411381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 158363861153688294737607587 237545791730532442106411381)
                ·
                  refine ⟨22269917974737416447476067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 237545791730532442106411381 22269917974737416447476067)
                  ·
                    refine ⟨33404876962106124671214101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22269917974737416447476067 33404876962106124671214101)
                    ·
                      refine ⟨1565853607598724593963161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 33404876962106124671214101 1565853607598724593963161)
                      ·
                        rfl

theorem cell23_3049489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 6].length) (baseStart_3049489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3049489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3049489 prefixEnd_3049489 := by exact prefixLift 3049489
  have htrace : WordTrace (prefixWord ++ tailWord_3049489) baseStart_3049489 baseEnd_3049489 := by
    simpa [prefixWord, tailWord_3049489, baseEnd_3049489] using wordTrace_append hprefix tailTrace_3049489
  have hstable : (prefixWord ++ tailWord_3049489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3049489).length < 2 ^ (prefixWord ++ tailWord_3049489).sum := by decide
  have hdescent : baseEnd_3049489 < baseStart_3049489 := by decide
  rcases family_descends (prefixWord ++ tailWord_3049489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3049496 : List Nat := [2, 1, 2, 3, 2, 1, 2, 3, 1, 1, 5]
def baseStart_3049496 : Nat := 118140960795 + 3049496 * 2 ^ 59
def prefixEnd_3049496 : Nat := 4983230072969 + 3 ^ 40 * 3049496 * 2
def baseEnd_3049496 : Nat := 1565857201963306066575629

theorem tailTrace_3049496 : CollatzResearch.WordTrace tailWord_3049496 prefixEnd_3049496 1565857201963306066575629 := by
  unfold tailWord_3049496
  simp only [CollatzResearch.WordTrace]
  refine ⟨55612128280102139648956171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74149504373469519531941561 55612128280102139648956171)
  ·
    refine ⟨83418192420153209473434257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55612128280102139648956171 83418192420153209473434257)
    ·
      refine ⟨62563644315114907105075693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83418192420153209473434257 62563644315114907105075693)
      ·
        refine ⟨23461366618168090164403385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62563644315114907105075693 23461366618168090164403385)
        ·
          refine ⟨17596024963626067623302539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23461366618168090164403385 17596024963626067623302539)
          ·
            refine ⟨26394037445439101434953809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17596024963626067623302539 26394037445439101434953809)
            ·
              refine ⟨19795528084079326076215357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26394037445439101434953809 19795528084079326076215357)
              ·
                refine ⟨7423323031529747278580759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19795528084079326076215357 7423323031529747278580759)
                ·
                  refine ⟨11134984547294620917871139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7423323031529747278580759 11134984547294620917871139)
                  ·
                    refine ⟨16702476820941931376806709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11134984547294620917871139 16702476820941931376806709)
                    ·
                      refine ⟨1565857201963306066575629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16702476820941931376806709 1565857201963306066575629)
                      ·
                        rfl

theorem cell23_3049496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 3, 1, 1, 5].length) (baseStart_3049496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3049496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3049496 prefixEnd_3049496 := by exact prefixLift 3049496
  have htrace : WordTrace (prefixWord ++ tailWord_3049496) baseStart_3049496 baseEnd_3049496 := by
    simpa [prefixWord, tailWord_3049496, baseEnd_3049496] using wordTrace_append hprefix tailTrace_3049496
  have hstable : (prefixWord ++ tailWord_3049496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3049496).length < 2 ^ (prefixWord ++ tailWord_3049496).sum := by decide
  have hdescent : baseEnd_3049496 < baseStart_3049496 := by decide
  rcases family_descends (prefixWord ++ tailWord_3049496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3049506 : List Nat := [3, 3, 1, 1, 1, 2, 2, 2, 1, 1, 6]
def baseStart_3049506 : Nat := 118140960795 + 3049506 * 2 ^ 59
def prefixEnd_3049506 : Nat := 4983230072969 + 3 ^ 40 * 3049506 * 2
def baseEnd_3049506 : Nat := 1565862336769851027450583

theorem tailTrace_3049506 : CollatzResearch.WordTrace tailWord_3049506 prefixEnd_3049506 1565862336769851027450583 := by
  unfold tailWord_3049506
  simp only [CollatzResearch.WordTrace]
  refine ⟨27806155322542012751444093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74149747526778700670517581 27806155322542012751444093)
  ·
    refine ⟨10427308245953254781791535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27806155322542012751444093 10427308245953254781791535)
    ·
      refine ⟨15640962368929882172687303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10427308245953254781791535 15640962368929882172687303)
      ·
        refine ⟨23461443553394823259030955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15640962368929882172687303 23461443553394823259030955)
        ·
          refine ⟨35192165330092234888546433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23461443553394823259030955 35192165330092234888546433)
          ·
            refine ⟨26394123997569176166409825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35192165330092234888546433 26394123997569176166409825)
            ·
              refine ⟨19795592998176882124807369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26394123997569176166409825 19795592998176882124807369)
              ·
                refine ⟨14846694748632661593605527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19795592998176882124807369 14846694748632661593605527)
                ·
                  refine ⟨22270042122948992390408291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14846694748632661593605527 22270042122948992390408291)
                  ·
                    refine ⟨33405063184423488585612437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22270042122948992390408291 33405063184423488585612437)
                    ·
                      refine ⟨1565862336769851027450583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 33405063184423488585612437 1565862336769851027450583)
                      ·
                        rfl

theorem cell23_3049506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 2, 1, 1, 6].length) (baseStart_3049506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3049506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3049506 prefixEnd_3049506 := by exact prefixLift 3049506
  have htrace : WordTrace (prefixWord ++ tailWord_3049506) baseStart_3049506 baseEnd_3049506 := by
    simpa [prefixWord, tailWord_3049506, baseEnd_3049506] using wordTrace_append hprefix tailTrace_3049506
  have hstable : (prefixWord ++ tailWord_3049506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3049506).length < 2 ^ (prefixWord ++ tailWord_3049506).sum := by decide
  have hdescent : baseEnd_3049506 < baseStart_3049506 := by decide
  rcases family_descends (prefixWord ++ tailWord_3049506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3049519 : List Nat := [1, 1, 2, 1, 2, 1, 1, 3, 1, 4, 6]
def baseStart_3049519 : Nat := 118140960795 + 3049519 * 2 ^ 59
def prefixEnd_3049519 : Nat := 4983230072969 + 3 ^ 40 * 3049519 * 2
def baseEnd_3049519 : Nat := 1565869012018359476588023

theorem tailTrace_3049519 : CollatzResearch.WordTrace tailWord_3049519 prefixEnd_3049519 1565869012018359476588023 := by
  unfold tailWord_3049519
  simp only [CollatzResearch.WordTrace]
  refine ⟨111225095439120954225999611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74150063626080636150666407 111225095439120954225999611)
  ·
    refine ⟨166837643158681431338999417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111225095439120954225999611 166837643158681431338999417)
    ·
      refine ⟨125128232369011073504249563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166837643158681431338999417 125128232369011073504249563)
      ·
        refine ⟨187692348553516610256374345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125128232369011073504249563 187692348553516610256374345)
        ·
          refine ⟨140769261415137457692280759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 187692348553516610256374345 140769261415137457692280759)
          ·
            refine ⟨211153892122706186538421139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140769261415137457692280759 211153892122706186538421139)
            ·
              refine ⟨316730838184059279807631709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 211153892122706186538421139 316730838184059279807631709)
              ·
                refine ⟨118774064319022229927861891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 316730838184059279807631709 118774064319022229927861891)
                ·
                  refine ⟨178161096478533344891792837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 118774064319022229927861891 178161096478533344891792837)
                  ·
                    refine ⟨33405205589725002167211157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 178161096478533344891792837 33405205589725002167211157)
                    ·
                      refine ⟨1565869012018359476588023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 33405205589725002167211157 1565869012018359476588023)
                      ·
                        rfl

theorem cell23_3049519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 3, 1, 4, 6].length) (baseStart_3049519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3049519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3049519 prefixEnd_3049519 := by exact prefixLift 3049519
  have htrace : WordTrace (prefixWord ++ tailWord_3049519) baseStart_3049519 baseEnd_3049519 := by
    simpa [prefixWord, tailWord_3049519, baseEnd_3049519] using wordTrace_append hprefix tailTrace_3049519
  have hstable : (prefixWord ++ tailWord_3049519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3049519).length < 2 ^ (prefixWord ++ tailWord_3049519).sum := by decide
  have hdescent : baseEnd_3049519 < baseStart_3049519 := by decide
  rcases family_descends (prefixWord ++ tailWord_3049519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3049520 : List Nat := [2, 1, 1, 1, 2, 6, 3, 1, 2, 4]
def baseStart_3049520 : Nat := 118140960795 + 3049520 * 2 ^ 59
def prefixEnd_3049520 : Nat := 4983230072969 + 3 ^ 40 * 3049520 * 2
def baseEnd_3049520 : Nat := 521956508499671324225173

theorem tailTrace_3049520 : CollatzResearch.WordTrace tailWord_3049520 prefixEnd_3049520 521956508499671324225173 := by
  unfold tailWord_3049520
  simp only [CollatzResearch.WordTrace]
  refine ⟨55612565956058665698393007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74150087941411554264524009 55612565956058665698393007)
  ·
    refine ⟨83418848934087998547589511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55612565956058665698393007 83418848934087998547589511)
    ·
      refine ⟨125128273401131997821384267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83418848934087998547589511 125128273401131997821384267)
      ·
        refine ⟨187692410101697996732076401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125128273401131997821384267 187692410101697996732076401)
        ·
          refine ⟨140769307576273497549057301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 187692410101697996732076401 140769307576273497549057301)
          ·
            refine ⟨6598561292637820197612061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 140769307576273497549057301 6598561292637820197612061)
            ·
              refine ⟨2474460484739182574104523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6598561292637820197612061 2474460484739182574104523)
              ·
                refine ⟨3711690727108773861156785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2474460484739182574104523 3711690727108773861156785)
                ·
                  refine ⟨2783768045331580395867589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3711690727108773861156785 2783768045331580395867589)
                  ·
                    refine ⟨521956508499671324225173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2783768045331580395867589 521956508499671324225173)
                    ·
                      rfl

theorem cell23_3049520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 3, 1, 2, 4].length) (baseStart_3049520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3049520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3049520 prefixEnd_3049520 := by exact prefixLift 3049520
  have htrace : WordTrace (prefixWord ++ tailWord_3049520) baseStart_3049520 baseEnd_3049520 := by
    simpa [prefixWord, tailWord_3049520, baseEnd_3049520] using wordTrace_append hprefix tailTrace_3049520
  have hstable : (prefixWord ++ tailWord_3049520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3049520).length < 2 ^ (prefixWord ++ tailWord_3049520).sum := by decide
  have hdescent : baseEnd_3049520 < baseStart_3049520 := by decide
  rcases family_descends (prefixWord ++ tailWord_3049520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3049543 : List Nat := [1, 1, 4, 1, 3, 1, 1, 1, 6, 1, 3]
def baseStart_3049543 : Nat := 118140960795 + 3049543 * 2 ^ 59
def prefixEnd_3049543 : Nat := 4983230072969 + 3 ^ 40 * 3049543 * 2
def baseEnd_3049543 : Nat := 1565881335554067382687913

theorem tailTrace_3049543 : CollatzResearch.WordTrace tailWord_3049543 prefixEnd_3049543 1565881335554067382687913 := by
  unfold tailWord_3049543
  simp only [CollatzResearch.WordTrace]
  refine ⟨111225970791034006324873283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74150647194022670883248855 111225970791034006324873283)
  ·
    refine ⟨166838956186551009487309925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111225970791034006324873283 166838956186551009487309925)
    ·
      refine ⟨31282304284978314278870611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 166838956186551009487309925 31282304284978314278870611)
      ·
        refine ⟨46923456427467471418305917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31282304284978314278870611 46923456427467471418305917)
        ·
          refine ⟨17596296160300301781864719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46923456427467471418305917 17596296160300301781864719)
          ·
            refine ⟨26394444240450452672797079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17596296160300301781864719 26394444240450452672797079)
            ·
              refine ⟨39591666360675679009195619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26394444240450452672797079 39591666360675679009195619)
              ·
                refine ⟨59387499541013518513793429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39591666360675679009195619 59387499541013518513793429)
                ·
                  refine ⟨2783789040985008680334067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 59387499541013518513793429 2783789040985008680334067)
                  ·
                    refine ⟨4175683561477513020501101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2783789040985008680334067 4175683561477513020501101)
                    ·
                      refine ⟨1565881335554067382687913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4175683561477513020501101 1565881335554067382687913)
                      ·
                        rfl

theorem cell23_3049543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 1, 6, 1, 3].length) (baseStart_3049543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3049543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3049543 prefixEnd_3049543 := by exact prefixLift 3049543
  have htrace : WordTrace (prefixWord ++ tailWord_3049543) baseStart_3049543 baseEnd_3049543 := by
    simpa [prefixWord, tailWord_3049543, baseEnd_3049543] using wordTrace_append hprefix tailTrace_3049543
  have hstable : (prefixWord ++ tailWord_3049543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3049543).length < 2 ^ (prefixWord ++ tailWord_3049543).sum := by decide
  have hdescent : baseEnd_3049543 < baseStart_3049543 := by decide
  rcases family_descends (prefixWord ++ tailWord_3049543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3049553 : List Nat := [1, 2, 2, 1, 3, 1, 1, 2, 5, 3, 2]
def baseStart_3049553 : Nat := 118140960795 + 3049553 * 2 ^ 59
def prefixEnd_3049553 : Nat := 4983230072969 + 3 ^ 40 * 3049553 * 2
def baseEnd_3049553 : Nat := 1565886470360612343562867

theorem tailTrace_3049553 : CollatzResearch.WordTrace tailWord_3049553 prefixEnd_3049553 1565886470360612343562867 := by
  unfold tailWord_3049553
  simp only [CollatzResearch.WordTrace]
  refine ⟨111226335520997778032737313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74150890347331852021824875 111226335520997778032737313)
  ·
    refine ⟨83419751640748333524552985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111226335520997778032737313 83419751640748333524552985)
    ·
      refine ⟨62564813730561250143414739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83419751640748333524552985 62564813730561250143414739)
      ·
        refine ⟨93847220595841875215122109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62564813730561250143414739 93847220595841875215122109)
        ·
          refine ⟨35192707723440703205670791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 93847220595841875215122109 35192707723440703205670791)
          ·
            refine ⟨52789061585161054808506187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35192707723440703205670791 52789061585161054808506187)
            ·
              refine ⟨79183592377741582212759281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52789061585161054808506187 79183592377741582212759281)
              ·
                refine ⟨59387694283306186659569461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79183592377741582212759281 59387694283306186659569461)
                ·
                  refine ⟨5567596339059954999334637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 59387694283306186659569461 5567596339059954999334637)
                  ·
                    refine ⟨2087848627147483124750489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5567596339059954999334637 2087848627147483124750489)
                    ·
                      refine ⟨1565886470360612343562867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2087848627147483124750489 1565886470360612343562867)
                      ·
                        rfl

theorem cell23_3049553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 2, 5, 3, 2].length) (baseStart_3049553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3049553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3049553 prefixEnd_3049553 := by exact prefixLift 3049553
  have htrace : WordTrace (prefixWord ++ tailWord_3049553) baseStart_3049553 baseEnd_3049553 := by
    simpa [prefixWord, tailWord_3049553, baseEnd_3049553] using wordTrace_append hprefix tailTrace_3049553
  have hstable : (prefixWord ++ tailWord_3049553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3049553).length < 2 ^ (prefixWord ++ tailWord_3049553).sum := by decide
  have hdescent : baseEnd_3049553 < baseStart_3049553 := by decide
  rcases family_descends (prefixWord ++ tailWord_3049553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3049556 : List Nat := [2, 4, 1, 1, 1, 1, 1, 1, 4, 2, 5]
def baseStart_3049556 : Nat := 118140960795 + 3049556 * 2 ^ 59
def prefixEnd_3049556 : Nat := 4983230072969 + 3 ^ 40 * 3049556 * 2
def baseEnd_3049556 : Nat := 1565888010802575831825353

theorem tailTrace_3049556 : CollatzResearch.WordTrace tailWord_3049556 prefixEnd_3049556 1565888010802575831825353 := by
  unfold tailWord_3049556
  simp only [CollatzResearch.WordTrace]
  refine ⟨55613222469993454772548261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74150963293324606363397681 55613222469993454772548261)
  ·
    refine ⟨10427479213123772769852799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55613222469993454772548261 10427479213123772769852799)
    ·
      refine ⟨15641218819685659154779199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10427479213123772769852799 15641218819685659154779199)
      ·
        refine ⟨23461828229528488732168799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15641218819685659154779199 23461828229528488732168799)
        ·
          refine ⟨35192742344292733098253199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23461828229528488732168799 35192742344292733098253199)
          ·
            refine ⟨52789113516439099647379799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35192742344292733098253199 52789113516439099647379799)
            ·
              refine ⟨79183670274658649471069699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52789113516439099647379799 79183670274658649471069699)
              ·
                refine ⟨118775505411987974206604549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79183670274658649471069699 118775505411987974206604549)
                ·
                  refine ⟨22270407264747745163738353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 118775505411987974206604549 22270407264747745163738353)
                  ·
                    refine ⟨16702805448560808872803765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22270407264747745163738353 16702805448560808872803765)
                    ·
                      refine ⟨1565888010802575831825353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16702805448560808872803765 1565888010802575831825353)
                      ·
                        rfl

theorem cell23_3049556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 1, 4, 2, 5].length) (baseStart_3049556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3049556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3049556 prefixEnd_3049556 := by exact prefixLift 3049556
  have htrace : WordTrace (prefixWord ++ tailWord_3049556) baseStart_3049556 baseEnd_3049556 := by
    simpa [prefixWord, tailWord_3049556, baseEnd_3049556] using wordTrace_append hprefix tailTrace_3049556
  have hstable : (prefixWord ++ tailWord_3049556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3049556).length < 2 ^ (prefixWord ++ tailWord_3049556).sum := by decide
  have hdescent : baseEnd_3049556 < baseStart_3049556 := by decide
  rcases family_descends (prefixWord ++ tailWord_3049556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3049633 : List Nat := [1, 2, 3, 3, 1, 2, 1, 1, 1, 5, 3]
def baseStart_3049633 : Nat := 118140960795 + 3049633 * 2 ^ 59
def prefixEnd_3049633 : Nat := 4983230072969 + 3 ^ 40 * 3049633 * 2
def baseEnd_3049633 : Nat := 1565927548812972030562499

theorem tailTrace_3049633 : CollatzResearch.WordTrace tailWord_3049633 prefixEnd_3049633 1565927548812972030562499 := by
  unfold tailWord_3049633
  simp only [CollatzResearch.WordTrace]
  refine ⟨111229253360707951695649553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74152835573805301130433035 111229253360707951695649553)
  ·
    refine ⟨83421940020530963771737165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111229253360707951695649553 83421940020530963771737165)
    ·
      refine ⟨31283227507699111414401437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83421940020530963771737165 31283227507699111414401437)
      ·
        refine ⟨11731210315387166780400539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31283227507699111414401437 11731210315387166780400539)
        ·
          refine ⟨17596815473080750170600809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11731210315387166780400539 17596815473080750170600809)
          ·
            refine ⟨13197611604810562627950607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17596815473080750170600809 13197611604810562627950607)
            ·
              refine ⟨19796417407215843941925911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13197611604810562627950607 19796417407215843941925911)
              ·
                refine ⟨29694626110823765912888867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19796417407215843941925911 29694626110823765912888867)
                ·
                  refine ⟨44541939166235648869333301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29694626110823765912888867 44541939166235648869333301)
                  ·
                    refine ⟨4175806796834592081499997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 44541939166235648869333301 4175806796834592081499997)
                    ·
                      refine ⟨1565927548812972030562499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4175806796834592081499997 1565927548812972030562499)
                      ·
                        rfl

theorem cell23_3049633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 1, 1, 5, 3].length) (baseStart_3049633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3049633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3049633 prefixEnd_3049633 := by exact prefixLift 3049633
  have htrace : WordTrace (prefixWord ++ tailWord_3049633) baseStart_3049633 baseEnd_3049633 := by
    simpa [prefixWord, tailWord_3049633, baseEnd_3049633] using wordTrace_append hprefix tailTrace_3049633
  have hstable : (prefixWord ++ tailWord_3049633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3049633).length < 2 ^ (prefixWord ++ tailWord_3049633).sum := by decide
  have hdescent : baseEnd_3049633 < baseStart_3049633 := by decide
  rcases family_descends (prefixWord ++ tailWord_3049633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3049634 : List Nat := [3, 3, 1, 3, 1, 1, 2, 3, 2, 2, 2]
def baseStart_3049634 : Nat := 118140960795 + 3049634 * 2 ^ 59
def prefixEnd_3049634 : Nat := 4983230072969 + 3 ^ 40 * 3049634 * 2
def baseEnd_3049634 : Nat := 1565928062293626526649995

theorem tailTrace_3049634 : CollatzResearch.WordTrace tailWord_3049634 prefixEnd_3049634 1565928062293626526649995 := by
  unfold tailWord_3049634
  simp only [CollatzResearch.WordTrace]
  refine ⟨27807322458426082216608989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74152859889136219244290637 27807322458426082216608989)
  ·
    refine ⟨10427745921909780831228371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27807322458426082216608989 10427745921909780831228371)
    ·
      refine ⟨15641618882864671246842557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10427745921909780831228371 15641618882864671246842557)
      ·
        refine ⟨5865607081074251717565959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15641618882864671246842557 5865607081074251717565959)
        ·
          refine ⟨8798410621611377576348939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5865607081074251717565959 8798410621611377576348939)
          ·
            refine ⟨13197615932417066364523409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8798410621611377576348939 13197615932417066364523409)
            ·
              refine ⟨9898211949312799773392557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13197615932417066364523409 9898211949312799773392557)
              ·
                refine ⟨3711829480992299915022209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9898211949312799773392557 3711829480992299915022209)
                ·
                  refine ⟨2783872110744224936266657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3711829480992299915022209 2783872110744224936266657)
                  ·
                    refine ⟨2087904083058168702199993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2783872110744224936266657 2087904083058168702199993)
                    ·
                      refine ⟨1565928062293626526649995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2087904083058168702199993 1565928062293626526649995)
                      ·
                        rfl

theorem cell23_3049634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 2, 3, 2, 2, 2].length) (baseStart_3049634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3049634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3049634 prefixEnd_3049634 := by exact prefixLift 3049634
  have htrace : WordTrace (prefixWord ++ tailWord_3049634) baseStart_3049634 baseEnd_3049634 := by
    simpa [prefixWord, tailWord_3049634, baseEnd_3049634] using wordTrace_append hprefix tailTrace_3049634
  have hstable : (prefixWord ++ tailWord_3049634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3049634).length < 2 ^ (prefixWord ++ tailWord_3049634).sum := by decide
  have hdescent : baseEnd_3049634 < baseStart_3049634 := by decide
  rcases family_descends (prefixWord ++ tailWord_3049634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3049690 : List Nat := [3, 1, 1, 2, 2, 1, 4, 1, 2, 4, 2]
def baseStart_3049690 : Nat := 118140960795 + 3049690 * 2 ^ 59
def prefixEnd_3049690 : Nat := 4983230072969 + 3 ^ 40 * 3049690 * 2
def baseEnd_3049690 : Nat := 1565956817210278307549737

theorem tailTrace_3049690 : CollatzResearch.WordTrace tailWord_3049690 prefixEnd_3049690 1565956817210278307549737 := by
  unfold tailWord_3049690
  simp only [CollatzResearch.WordTrace]
  refine ⟨27807833080375362607618631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74154221547667633620316349 27807833080375362607618631)
  ·
    refine ⟨41711749620563043911427947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27807833080375362607618631 41711749620563043911427947)
    ·
      refine ⟨62567624430844565867141921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41711749620563043911427947 62567624430844565867141921)
      ·
        refine ⟨46925718323133424400356441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62567624430844565867141921 46925718323133424400356441)
        ·
          refine ⟨35194288742350068300267331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46925718323133424400356441 35194288742350068300267331)
          ·
            refine ⟨52791433113525102450400997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35194288742350068300267331 52791433113525102450400997)
            ·
              refine ⟨9898393708785956709450187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52791433113525102450400997 9898393708785956709450187)
              ·
                refine ⟨14847590563178935064175281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9898393708785956709450187 14847590563178935064175281)
                ·
                  refine ⟨11135692922384201298131461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14847590563178935064175281 11135692922384201298131461)
                  ·
                    refine ⟨2087942422947037743399649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11135692922384201298131461 2087942422947037743399649)
                    ·
                      refine ⟨1565956817210278307549737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2087942422947037743399649 1565956817210278307549737)
                      ·
                        rfl

theorem cell23_3049690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 4, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 4, 1, 2, 4, 2].length) (baseStart_3049690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3049690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3049690 prefixEnd_3049690 := by exact prefixLift 3049690
  have htrace : WordTrace (prefixWord ++ tailWord_3049690) baseStart_3049690 baseEnd_3049690 := by
    simpa [prefixWord, tailWord_3049690, baseEnd_3049690] using wordTrace_append hprefix tailTrace_3049690
  have hstable : (prefixWord ++ tailWord_3049690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3049690).length < 2 ^ (prefixWord ++ tailWord_3049690).sum := by decide
  have hdescent : baseEnd_3049690 < baseStart_3049690 := by decide
  rcases family_descends (prefixWord ++ tailWord_3049690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3049710 : List Nat := [4, 1, 2, 1, 1, 1, 1, 5, 2, 2, 3]
def baseStart_3049710 : Nat := 118140960795 + 3049710 * 2 ^ 59
def prefixEnd_3049710 : Nat := 4983230072969 + 3 ^ 40 * 3049710 * 2
def baseEnd_3049710 : Nat := 1565967086823368229299645

theorem tailTrace_3049710 : CollatzResearch.WordTrace tailWord_3049710 prefixEnd_3049710 1565967086823368229299645 := by
  unfold tailWord_3049710
  simp only [CollatzResearch.WordTrace]
  refine ⟨13904007722678624230775323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74154707854285995897468389 13904007722678624230775323)
  ·
    refine ⟨20856011584017936346162985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13904007722678624230775323 20856011584017936346162985)
    ·
      refine ⟨15642008688013452259622239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20856011584017936346162985 15642008688013452259622239)
      ·
        refine ⟨23463013032020178389433359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15642008688013452259622239 23463013032020178389433359)
        ·
          refine ⟨35194519548030267584150039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23463013032020178389433359 35194519548030267584150039)
          ·
            refine ⟨52791779322045401376225059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35194519548030267584150039 52791779322045401376225059)
            ·
              refine ⟨79187668983068102064337589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52791779322045401376225059 79187668983068102064337589)
              ·
                refine ⟨7423843967162634568531649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 79187668983068102064337589 7423843967162634568531649)
                ·
                  refine ⟨5567882975371975926398737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7423843967162634568531649 5567882975371975926398737)
                  ·
                    refine ⟨4175912231528981944799053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5567882975371975926398737 4175912231528981944799053)
                    ·
                      refine ⟨1565967086823368229299645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4175912231528981944799053 1565967086823368229299645)
                      ·
                        rfl

theorem cell23_3049710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 5, 2, 2, 3].length) (baseStart_3049710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3049710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3049710 prefixEnd_3049710 := by exact prefixLift 3049710
  have htrace : WordTrace (prefixWord ++ tailWord_3049710) baseStart_3049710 baseEnd_3049710 := by
    simpa [prefixWord, tailWord_3049710, baseEnd_3049710] using wordTrace_append hprefix tailTrace_3049710
  have hstable : (prefixWord ++ tailWord_3049710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3049710).length < 2 ^ (prefixWord ++ tailWord_3049710).sum := by decide
  have hdescent : baseEnd_3049710 < baseStart_3049710 := by decide
  rcases family_descends (prefixWord ++ tailWord_3049710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3049730 : List Nat := [3, 4, 1, 1, 2, 1, 2, 1, 8]
def baseStart_3049730 : Nat := 118140960795 + 3049730 * 2 ^ 59
def prefixEnd_3049730 : Nat := 4983230072969 + 3 ^ 40 * 3049730 * 2
def baseEnd_3049730 : Nat := 173997484048495350116617

theorem tailTrace_3049730 : CollatzResearch.WordTrace tailWord_3049730 prefixEnd_3049730 173997484048495350116617 := by
  unfold tailWord_3049730
  simp only [CollatzResearch.WordTrace]
  refine ⟨27808197810339134315482661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74155194160904358174620429 27808197810339134315482661)
  ·
    refine ⟨5214037089438587684152999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27808197810339134315482661 5214037089438587684152999)
    ·
      refine ⟨7821055634157881526229499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5214037089438587684152999 7821055634157881526229499)
      ·
        refine ⟨11731583451236822289344249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7821055634157881526229499 11731583451236822289344249)
        ·
          refine ⟨8798687588427616717008187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11731583451236822289344249 8798687588427616717008187)
          ·
            refine ⟨13198031382641425075512281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8798687588427616717008187 13198031382641425075512281)
            ·
              refine ⟨9898523536981068806634211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13198031382641425075512281 9898523536981068806634211)
              ·
                refine ⟨14847785305471603209951317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9898523536981068806634211 14847785305471603209951317)
                ·
                  refine ⟨173997484048495350116617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 14847785305471603209951317 173997484048495350116617)
                  ·
                    rfl

theorem cell23_3049730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 2, 1, 8].length) (baseStart_3049730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3049730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3049730 prefixEnd_3049730 := by exact prefixLift 3049730
  have htrace : WordTrace (prefixWord ++ tailWord_3049730) baseStart_3049730 baseEnd_3049730 := by
    simpa [prefixWord, tailWord_3049730, baseEnd_3049730] using wordTrace_append hprefix tailTrace_3049730
  have hstable : (prefixWord ++ tailWord_3049730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3049730).length < 2 ^ (prefixWord ++ tailWord_3049730).sum := by decide
  have hdescent : baseEnd_3049730 < baseStart_3049730 := by decide
  rcases family_descends (prefixWord ++ tailWord_3049730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3049760 : List Nat := [2, 1, 1, 5, 2, 2, 1, 1, 3, 5]
def baseStart_3049760 : Nat := 118140960795 + 3049760 * 2 ^ 59
def prefixEnd_3049760 : Nat := 4983230072969 + 3 ^ 40 * 3049760 * 2
def baseEnd_3049760 : Nat := 521997586952031011224805

theorem tailTrace_3049760 : CollatzResearch.WordTrace tailWord_3049760 prefixEnd_3049760 521997586952031011224805 := by
  unfold tailWord_3049760
  simp only [CollatzResearch.WordTrace]
  refine ⟨55616942715623926192761367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74155923620831901590348489 55616942715623926192761367)
  ·
    refine ⟨83425414073435889289142051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55616942715623926192761367 83425414073435889289142051)
    ·
      refine ⟨125138121110153833933713077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83425414073435889289142051 125138121110153833933713077)
      ·
        refine ⟨11731698854076921931285601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 125138121110153833933713077 11731698854076921931285601)
        ·
          refine ⟨8798774140557691448464201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11731698854076921931285601 8798774140557691448464201)
          ·
            refine ⟨6599080605418268586348151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8798774140557691448464201 6599080605418268586348151)
            ·
              refine ⟨9898620908127402879522227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6599080605418268586348151 9898620908127402879522227)
              ·
                refine ⟨14847931362191104319283341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9898620908127402879522227 14847931362191104319283341)
                ·
                  refine ⟨5567974260821664119731253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14847931362191104319283341 5567974260821664119731253)
                  ·
                    refine ⟨521997586952031011224805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5567974260821664119731253 521997586952031011224805)
                    ·
                      rfl

theorem cell23_3049760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 1, 1, 3, 5].length) (baseStart_3049760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3049760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3049760 prefixEnd_3049760 := by exact prefixLift 3049760
  have htrace : WordTrace (prefixWord ++ tailWord_3049760) baseStart_3049760 baseEnd_3049760 := by
    simpa [prefixWord, tailWord_3049760, baseEnd_3049760] using wordTrace_append hprefix tailTrace_3049760
  have hstable : (prefixWord ++ tailWord_3049760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3049760).length < 2 ^ (prefixWord ++ tailWord_3049760).sum := by decide
  have hdescent : baseEnd_3049760 < baseStart_3049760 := by decide
  rcases family_descends (prefixWord ++ tailWord_3049760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3049800 : List Nat := [2, 1, 3, 1, 1, 2, 3, 2, 3, 2, 3]
def baseStart_3049800 : Nat := 118140960795 + 3049800 * 2 ^ 59
def prefixEnd_3049800 : Nat := 4983230072969 + 3 ^ 40 * 3049800 * 2
def baseEnd_3049800 : Nat := 1566013300082272877174231

theorem tailTrace_3049800 : CollatzResearch.WordTrace tailWord_3049800 prefixEnd_3049800 1566013300082272877174231 := by
  unfold tailWord_3049800
  simp only [CollatzResearch.WordTrace]
  refine ⟨55617672175551469608489427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74156896234068626144652569 55617672175551469608489427)
  ·
    refine ⟨83426508263327204412734141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55617672175551469608489427 83426508263327204412734141)
    ·
      refine ⟨31284940598747701654775303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83426508263327204412734141 31284940598747701654775303)
      ·
        refine ⟨46927410898121552482162955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31284940598747701654775303 46927410898121552482162955)
        ·
          refine ⟨70391116347182328723244433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46927410898121552482162955 70391116347182328723244433)
          ·
            refine ⟨52793337260386746542433325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70391116347182328723244433 52793337260386746542433325)
            ·
              refine ⟨19797501472645029953412497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52793337260386746542433325 19797501472645029953412497)
              ·
                refine ⟨14848126104483772465059373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19797501472645029953412497 14848126104483772465059373)
                ·
                  refine ⟨5568047289181414674397265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14848126104483772465059373 5568047289181414674397265)
                  ·
                    refine ⟨4176035466886061005797949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5568047289181414674397265 4176035466886061005797949)
                    ·
                      refine ⟨1566013300082272877174231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4176035466886061005797949 1566013300082272877174231)
                      ·
                        rfl

theorem cell23_3049800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 2, 3, 2, 3].length) (baseStart_3049800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3049800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3049800 prefixEnd_3049800 := by exact prefixLift 3049800
  have htrace : WordTrace (prefixWord ++ tailWord_3049800) baseStart_3049800 baseEnd_3049800 := by
    simpa [prefixWord, tailWord_3049800, baseEnd_3049800] using wordTrace_append hprefix tailTrace_3049800
  have hstable : (prefixWord ++ tailWord_3049800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3049800).length < 2 ^ (prefixWord ++ tailWord_3049800).sum := by decide
  have hdescent : baseEnd_3049800 < baseStart_3049800 := by decide
  rcases family_descends (prefixWord ++ tailWord_3049800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3049810 : List Nat := [3, 2, 2, 1, 1, 1, 3, 3, 1, 2, 4]
def baseStart_3049810 : Nat := 118140960795 + 3049810 * 2 ^ 59
def prefixEnd_3049810 : Nat := 4983230072969 + 3 ^ 40 * 3049810 * 2
def baseEnd_3049810 : Nat := 1566018434888817838049185

theorem tailTrace_3049810 : CollatzResearch.WordTrace tailWord_3049810 prefixEnd_3049810 1566018434888817838049185 := by
  unfold tailWord_3049810
  simp only [CollatzResearch.WordTrace]
  refine ⟨27808927270266677731210721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74157139387377807283228589 27808927270266677731210721)
  ·
    refine ⟨20856695452700008298408041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27808927270266677731210721 20856695452700008298408041)
    ·
      refine ⟨15642521589525006223806031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20856695452700008298408041 15642521589525006223806031)
      ·
        refine ⟨23463782384287509335709047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15642521589525006223806031 23463782384287509335709047)
        ·
          refine ⟨35195673576431264003563571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23463782384287509335709047 35195673576431264003563571)
          ·
            refine ⟨52793510364646896005345357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35195673576431264003563571 52793510364646896005345357)
            ·
              refine ⟨19797566386742586002004509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52793510364646896005345357 19797566386742586002004509)
              ·
                refine ⟨7424087395028469750751691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19797566386742586002004509 7424087395028469750751691)
                ·
                  refine ⟨11136131092542704626127537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7424087395028469750751691 11136131092542704626127537)
                  ·
                    refine ⟨8352098319407028469595653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11136131092542704626127537 8352098319407028469595653)
                    ·
                      refine ⟨1566018434888817838049185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8352098319407028469595653 1566018434888817838049185)
                      ·
                        rfl

theorem cell23_3049810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 3, 1, 2, 4].length) (baseStart_3049810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3049810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3049810 prefixEnd_3049810 := by exact prefixLift 3049810
  have htrace : WordTrace (prefixWord ++ tailWord_3049810) baseStart_3049810 baseEnd_3049810 := by
    simpa [prefixWord, tailWord_3049810, baseEnd_3049810] using wordTrace_append hprefix tailTrace_3049810
  have hstable : (prefixWord ++ tailWord_3049810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3049810).length < 2 ^ (prefixWord ++ tailWord_3049810).sum := by decide
  have hdescent : baseEnd_3049810 < baseStart_3049810 := by decide
  rcases family_descends (prefixWord ++ tailWord_3049810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3049831 : List Nat := [1, 1, 5, 1, 3, 1, 1, 5, 1, 2, 2]
def baseStart_3049831 : Nat := 118140960795 + 3049831 * 2 ^ 59
def prefixEnd_3049831 : Nat := 4983230072969 + 3 ^ 40 * 3049831 * 2
def baseEnd_3049831 : Nat := 1566029217982562255886589

theorem tailTrace_3049831 : CollatzResearch.WordTrace tailWord_3049831 prefixEnd_3049831 1566029217982562255886589 := by
  unfold tailWord_3049831
  simp only [CollatzResearch.WordTrace]
  refine ⟨111236475013990631511357347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74157650009327087674238231 111236475013990631511357347)
  ·
    refine ⟨166854712520985947267036021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111236475013990631511357347 166854712520985947267036021)
    ·
      refine ⟨15642629298842432556284627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 166854712520985947267036021 15642629298842432556284627)
      ·
        refine ⟨23463943948263648834426941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15642629298842432556284627 23463943948263648834426941)
        ·
          refine ⟨8798978980598868312910103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23463943948263648834426941 8798978980598868312910103)
          ·
            refine ⟨13198468470898302469365155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8798978980598868312910103 13198468470898302469365155)
            ·
              refine ⟨19797702706347453704047733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13198468470898302469365155 19797702706347453704047733)
              ·
                refine ⟨1856034628720073784754475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19797702706347453704047733 1856034628720073784754475)
                ·
                  refine ⟨2784051943080110677131713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1856034628720073784754475 2784051943080110677131713)
                  ·
                    refine ⟨2088038957310083007848785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2784051943080110677131713 2088038957310083007848785)
                    ·
                      refine ⟨1566029217982562255886589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2088038957310083007848785 1566029217982562255886589)
                      ·
                        rfl

theorem cell23_3049831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 5, 1, 2, 2].length) (baseStart_3049831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3049831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3049831 prefixEnd_3049831 := by exact prefixLift 3049831
  have htrace : WordTrace (prefixWord ++ tailWord_3049831) baseStart_3049831 baseEnd_3049831 := by
    simpa [prefixWord, tailWord_3049831, baseEnd_3049831] using wordTrace_append hprefix tailTrace_3049831
  have hstable : (prefixWord ++ tailWord_3049831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3049831).length < 2 ^ (prefixWord ++ tailWord_3049831).sum := by decide
  have hdescent : baseEnd_3049831 < baseStart_3049831 := by decide
  rcases family_descends (prefixWord ++ tailWord_3049831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3049834 : List Nat := [3, 1, 3, 3, 1, 2, 1, 3, 1, 2, 3]
def baseStart_3049834 : Nat := 118140960795 + 3049834 * 2 ^ 59
def prefixEnd_3049834 : Nat := 4983230072969 + 3 ^ 40 * 3049834 * 2
def baseEnd_3049834 : Nat := 1566030758424525744149075

theorem tailTrace_3049834 : CollatzResearch.WordTrace tailWord_3049834 prefixEnd_3049834 1566030758424525744149075 := by
  unfold tailWord_3049834
  simp only [CollatzResearch.WordTrace]
  refine ⟨27809146108244940755929139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74157722955319842015811037 27809146108244940755929139)
  ·
    refine ⟨41713719162367411133893709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27809146108244940755929139 41713719162367411133893709)
    ·
      refine ⟨15642644685887779175210141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41713719162367411133893709 15642644685887779175210141)
      ·
        refine ⟨5865991757207917190703803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15642644685887779175210141 5865991757207917190703803)
        ·
          refine ⟨8798987635811875786055705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5865991757207917190703803 8798987635811875786055705)
          ·
            refine ⟨6599240726858906839541779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8798987635811875786055705 6599240726858906839541779)
            ·
              refine ⟨9898861090288360259312669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6599240726858906839541779 9898861090288360259312669)
              ·
                refine ⟨3712072908858135097242251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9898861090288360259312669 3712072908858135097242251)
                ·
                  refine ⟨5568109363287202645863377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3712072908858135097242251 5568109363287202645863377)
                  ·
                    refine ⟨4176082022465401984397533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5568109363287202645863377 4176082022465401984397533)
                    ·
                      refine ⟨1566030758424525744149075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4176082022465401984397533 1566030758424525744149075)
                      ·
                        rfl

theorem cell23_3049834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 1, 3, 1, 2, 3].length) (baseStart_3049834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3049834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3049834 prefixEnd_3049834 := by exact prefixLift 3049834
  have htrace : WordTrace (prefixWord ++ tailWord_3049834) baseStart_3049834 baseEnd_3049834 := by
    simpa [prefixWord, tailWord_3049834, baseEnd_3049834] using wordTrace_append hprefix tailTrace_3049834
  have hstable : (prefixWord ++ tailWord_3049834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3049834).length < 2 ^ (prefixWord ++ tailWord_3049834).sum := by decide
  have hdescent : baseEnd_3049834 < baseStart_3049834 := by decide
  rcases family_descends (prefixWord ++ tailWord_3049834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3049843 : List Nat := [1, 1, 1, 2, 2, 1, 2, 4, 2, 2, 5]
def baseStart_3049843 : Nat := 118140960795 + 3049843 * 2 ^ 59
def prefixEnd_3049843 : Nat := 4983230072969 + 3 ^ 40 * 3049843 * 2
def baseEnd_3049843 : Nat := 1566035379750416208936533

theorem tailTrace_3049843 : CollatzResearch.WordTrace tailWord_3049843 prefixEnd_3049843 1566035379750416208936533 := by
  unfold tailWord_3049843
  simp only [CollatzResearch.WordTrace]
  refine ⟨111236912689947157560794183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74157941793298105040529455 111236912689947157560794183)
  ·
    refine ⟨166855369034920736341191275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111236912689947157560794183 166855369034920736341191275)
    ·
      refine ⟨250283053552381104511786913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166855369034920736341191275 250283053552381104511786913)
      ·
        refine ⟨187712290164285828383840185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 250283053552381104511786913 187712290164285828383840185)
        ·
          refine ⟨140784217623214371287880139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 187712290164285828383840185 140784217623214371287880139)
          ·
            refine ⟨211176326434821556931820209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140784217623214371287880139 211176326434821556931820209)
            ·
              refine ⟨158382244826116167698865157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 211176326434821556931820209 158382244826116167698865157)
              ·
                refine ⟨29696670904896781443537217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 158382244826116167698865157 29696670904896781443537217)
                ·
                  refine ⟨22272503178672586082652913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29696670904896781443537217 22272503178672586082652913)
                  ·
                    refine ⟨16704377384004439561989685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22272503178672586082652913 16704377384004439561989685)
                    ·
                      refine ⟨1566035379750416208936533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16704377384004439561989685 1566035379750416208936533)
                      ·
                        rfl

theorem cell23_3049843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 4, 2, 2, 5].length) (baseStart_3049843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3049843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3049843 prefixEnd_3049843 := by exact prefixLift 3049843
  have htrace : WordTrace (prefixWord ++ tailWord_3049843) baseStart_3049843 baseEnd_3049843 := by
    simpa [prefixWord, tailWord_3049843, baseEnd_3049843] using wordTrace_append hprefix tailTrace_3049843
  have hstable : (prefixWord ++ tailWord_3049843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3049843).length < 2 ^ (prefixWord ++ tailWord_3049843).sum := by decide
  have hdescent : baseEnd_3049843 < baseStart_3049843 := by decide
  rcases family_descends (prefixWord ++ tailWord_3049843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3049847 : List Nat := [1, 1, 3, 1, 1, 2, 2, 6, 2, 1, 3]
def baseStart_3049847 : Nat := 118140960795 + 3049847 * 2 ^ 59
def prefixEnd_3049847 : Nat := 4983230072969 + 3 ^ 40 * 3049847 * 2
def baseEnd_3049847 : Nat := 1566037433673034193286515

theorem tailTrace_3049847 : CollatzResearch.WordTrace tailWord_3049847 prefixEnd_3049847 1566037433673034193286515 := by
  unfold tailWord_3049847
  simp only [CollatzResearch.WordTrace]
  refine ⟨111237058581932666243939795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74158039054621777495959863 111237058581932666243939795)
  ·
    refine ⟨166855587872898999365909693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111237058581932666243939795 166855587872898999365909693)
    ·
      refine ⟨62570845452337124762216135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 166855587872898999365909693 62570845452337124762216135)
      ·
        refine ⟨93856268178505687143324203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62570845452337124762216135 93856268178505687143324203)
        ·
          refine ⟨140784402267758530714986305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93856268178505687143324203 140784402267758530714986305)
          ·
            refine ⟨105588301700818898036239729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 140784402267758530714986305 105588301700818898036239729)
            ·
              refine ⟨79191226275614173527179797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 105588301700818898036239729 79191226275614173527179797)
              ·
                refine ⟨3712088731669414384086553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 79191226275614173527179797 3712088731669414384086553)
                ·
                  refine ⟨2784066548752060788064915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3712088731669414384086553 2784066548752060788064915)
                  ·
                    refine ⟨4176099823128091182097373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2784066548752060788064915 4176099823128091182097373)
                    ·
                      refine ⟨1566037433673034193286515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4176099823128091182097373 1566037433673034193286515)
                      ·
                        rfl

theorem cell23_3049847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 6, 2, 1, 3].length) (baseStart_3049847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3049847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3049847 prefixEnd_3049847 := by exact prefixLift 3049847
  have htrace : WordTrace (prefixWord ++ tailWord_3049847) baseStart_3049847 baseEnd_3049847 := by
    simpa [prefixWord, tailWord_3049847, baseEnd_3049847] using wordTrace_append hprefix tailTrace_3049847
  have hstable : (prefixWord ++ tailWord_3049847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3049847).length < 2 ^ (prefixWord ++ tailWord_3049847).sum := by decide
  have hdescent : baseEnd_3049847 < baseStart_3049847 := by decide
  rcases family_descends (prefixWord ++ tailWord_3049847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3049858 : List Nat := [3, 4, 2, 1, 2, 1, 3, 1, 2, 4]
def baseStart_3049858 : Nat := 118140960795 + 3049858 * 2 ^ 59
def prefixEnd_3049858 : Nat := 4983230072969 + 3 ^ 40 * 3049858 * 2
def baseEnd_3049858 : Nat := 522014360653411216749655

theorem tailTrace_3049858 : CollatzResearch.WordTrace tailWord_3049858 prefixEnd_3049858 522014360653411216749655 := by
  unfold tailWord_3049858
  simp only [CollatzResearch.WordTrace]
  refine ⟨27809364946223203780647557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74158306523261876748393485 27809364946223203780647557)
  ·
    refine ⟨5214255927416850708871417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27809364946223203780647557 5214255927416850708871417)
    ·
      refine ⟨3910691945562638031653563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5214255927416850708871417 3910691945562638031653563)
      ·
        refine ⟨5866037918343957047480345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3910691945562638031653563 5866037918343957047480345)
        ·
          refine ⟨4399528438757967785610259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5866037918343957047480345 4399528438757967785610259)
          ·
            refine ⟨6599292658136951678415389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4399528438757967785610259 6599292658136951678415389)
            ·
              refine ⟨2474734746801356879405771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6599292658136951678415389 2474734746801356879405771)
              ·
                refine ⟨3712102120202035319108657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2474734746801356879405771 3712102120202035319108657)
                ·
                  refine ⟨2784076590151526489331493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3712102120202035319108657 2784076590151526489331493)
                  ·
                    refine ⟨522014360653411216749655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2784076590151526489331493 522014360653411216749655)
                    ·
                      rfl

theorem cell23_3049858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 3, 1, 2, 4].length) (baseStart_3049858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3049858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3049858 prefixEnd_3049858 := by exact prefixLift 3049858
  have htrace : WordTrace (prefixWord ++ tailWord_3049858) baseStart_3049858 baseEnd_3049858 := by
    simpa [prefixWord, tailWord_3049858, baseEnd_3049858] using wordTrace_append hprefix tailTrace_3049858
  have hstable : (prefixWord ++ tailWord_3049858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3049858).length < 2 ^ (prefixWord ++ tailWord_3049858).sum := by decide
  have hdescent : baseEnd_3049858 < baseStart_3049858 := by decide
  rcases family_descends (prefixWord ++ tailWord_3049858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3049887 : List Nat := [1, 1, 2, 5, 1, 1, 2, 1, 3, 4, 2]
def baseStart_3049887 : Nat := 118140960795 + 3049887 * 2 ^ 59
def prefixEnd_3049887 : Nat := 4983230072969 + 3 ^ 40 * 3049887 * 2
def baseEnd_3049887 : Nat := 1566057972899214036786331

theorem tailTrace_3049887 : CollatzResearch.WordTrace tailWord_3049887 prefixEnd_3049887 1566057972899214036786331 := by
  unfold tailWord_3049887
  simp only [CollatzResearch.WordTrace]
  refine ⟨111238517501787753075395915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74159011667858502050263943 111238517501787753075395915)
  ·
    refine ⟨166857776252681629613093873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111238517501787753075395915 166857776252681629613093873)
    ·
      refine ⟨125143332189511222209820405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166857776252681629613093873 125143332189511222209820405)
      ·
        refine ⟨11732187392766677082170663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 125143332189511222209820405 11732187392766677082170663)
        ·
          refine ⟨17598281089150015623255995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11732187392766677082170663 17598281089150015623255995)
          ·
            refine ⟨26397421633725023434883993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17598281089150015623255995 26397421633725023434883993)
            ·
              refine ⟨19798066225293767576162995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26397421633725023434883993 19798066225293767576162995)
              ·
                refine ⟨29697099337940651364244493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19798066225293767576162995 29697099337940651364244493)
                ·
                  refine ⟨11136412251727744261591685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29697099337940651364244493 11136412251727744261591685)
                  ·
                    refine ⟨2088077297198952049048441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11136412251727744261591685 2088077297198952049048441)
                    ·
                      refine ⟨1566057972899214036786331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2088077297198952049048441 1566057972899214036786331)
                      ·
                        rfl

theorem cell23_3049887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 1, 3, 4, 2].length) (baseStart_3049887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3049887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3049887 prefixEnd_3049887 := by exact prefixLift 3049887
  have htrace : WordTrace (prefixWord ++ tailWord_3049887) baseStart_3049887 baseEnd_3049887 := by
    simpa [prefixWord, tailWord_3049887, baseEnd_3049887] using wordTrace_append hprefix tailTrace_3049887
  have hstable : (prefixWord ++ tailWord_3049887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3049887).length < 2 ^ (prefixWord ++ tailWord_3049887).sum := by decide
  have hdescent : baseEnd_3049887 < baseStart_3049887 := by decide
  rcases family_descends (prefixWord ++ tailWord_3049887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3049920 : List Nat := [2, 1, 1, 2, 3, 1, 1, 3, 1, 5, 3]
def baseStart_3049920 : Nat := 118140960795 + 3049920 * 2 ^ 59
def prefixEnd_3049920 : Nat := 4983230072969 + 3 ^ 40 * 3049920 * 2
def baseEnd_3049920 : Nat := 1566074917760812407673679

theorem tailTrace_3049920 : CollatzResearch.WordTrace tailWord_3049920 prefixEnd_3049920 1566074917760812407673679 := by
  unfold tailWord_3049920
  simp only [CollatzResearch.WordTrace]
  refine ⟨55619860555334099855673607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74159814073778799807564809 55619860555334099855673607)
  ·
    refine ⟨83429790833001149783510411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55619860555334099855673607 83429790833001149783510411)
    ·
      refine ⟨125144686249501724675265617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83429790833001149783510411 125144686249501724675265617)
      ·
        refine ⟨93858514687126293506449213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125144686249501724675265617 93858514687126293506449213)
        ·
          refine ⟨35196943007672360064918455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 93858514687126293506449213 35196943007672360064918455)
          ·
            refine ⟨52795414511508540097377683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35196943007672360064918455 52795414511508540097377683)
            ·
              refine ⟨79193121767262810146066525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52795414511508540097377683 79193121767262810146066525)
              ·
                refine ⟨29697420662723553804774947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 79193121767262810146066525 29697420662723553804774947)
                ·
                  refine ⟨44546130994085330707162421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29697420662723553804774947 44546130994085330707162421)
                  ·
                    refine ⟨4176199780695499753796477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 44546130994085330707162421 4176199780695499753796477)
                    ·
                      refine ⟨1566074917760812407673679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4176199780695499753796477 1566074917760812407673679)
                      ·
                        rfl

theorem cell23_3049920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 3, 1, 5, 3].length) (baseStart_3049920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3049920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3049920 prefixEnd_3049920 := by exact prefixLift 3049920
  have htrace : WordTrace (prefixWord ++ tailWord_3049920) baseStart_3049920 baseEnd_3049920 := by
    simpa [prefixWord, tailWord_3049920, baseEnd_3049920] using wordTrace_append hprefix tailTrace_3049920
  have hstable : (prefixWord ++ tailWord_3049920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3049920).length < 2 ^ (prefixWord ++ tailWord_3049920).sum := by decide
  have hdescent : baseEnd_3049920 < baseStart_3049920 := by decide
  rcases family_descends (prefixWord ++ tailWord_3049920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3049977 : List Nat := [1, 2, 1, 3, 1, 2, 3, 1, 1, 6, 2]
def baseStart_3049977 : Nat := 118140960795 + 3049977 * 2 ^ 59
def prefixEnd_3049977 : Nat := 4983230072969 + 3 ^ 40 * 3049977 * 2
def baseEnd_3049977 : Nat := 1566104186158118684660917

theorem tailTrace_3049977 : CollatzResearch.WordTrace tailWord_3049977 prefixEnd_3049977 1566104186158118684660917 := by
  unfold tailWord_3049977
  simp only [CollatzResearch.WordTrace]
  refine ⟨111241800071461698446172185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74161200047641132297448123 111241800071461698446172185)
  ·
    refine ⟨83431350053596273834629139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111241800071461698446172185 83431350053596273834629139)
    ·
      refine ⟨125147025080394410751943709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83431350053596273834629139 125147025080394410751943709)
      ·
        refine ⟨46930134405147904031978891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 125147025080394410751943709 46930134405147904031978891)
        ·
          refine ⟨70395201607721856047968337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46930134405147904031978891 70395201607721856047968337)
          ·
            refine ⟨52796401205791392035976253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70395201607721856047968337 52796401205791392035976253)
            ·
              refine ⟨19798650452171772013491095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52796401205791392035976253 19798650452171772013491095)
              ·
                refine ⟨29697975678257658020236643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19798650452171772013491095 29697975678257658020236643)
                ·
                  refine ⟨44546963517386487030354965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29697975678257658020236643 44546963517386487030354965)
                  ·
                    refine ⟨2088138914877491579547889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 44546963517386487030354965 2088138914877491579547889)
                    ·
                      refine ⟨1566104186158118684660917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2088138914877491579547889 1566104186158118684660917)
                      ·
                        rfl

theorem cell23_3049977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 1, 1, 6, 2].length) (baseStart_3049977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3049977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3049977 prefixEnd_3049977 := by exact prefixLift 3049977
  have htrace : WordTrace (prefixWord ++ tailWord_3049977) baseStart_3049977 baseEnd_3049977 := by
    simpa [prefixWord, tailWord_3049977, baseEnd_3049977] using wordTrace_append hprefix tailTrace_3049977
  have hstable : (prefixWord ++ tailWord_3049977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3049977).length < 2 ^ (prefixWord ++ tailWord_3049977).sum := by decide
  have hdescent : baseEnd_3049977 < baseStart_3049977 := by decide
  rcases family_descends (prefixWord ++ tailWord_3049977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3049987 : List Nat := [1, 1, 1, 3, 2, 1, 5, 2, 3, 4]
def baseStart_3049987 : Nat := 118140960795 + 3049987 * 2 ^ 59
def prefixEnd_3049987 : Nat := 4983230072969 + 3 ^ 40 * 3049987 * 2
def baseEnd_3049987 : Nat := 522036440321554548511957

theorem tailTrace_3049987 : CollatzResearch.WordTrace tailWord_3049987 prefixEnd_3049987 522036440321554548511957 := by
  unfold tailWord_3049987
  simp only [CollatzResearch.WordTrace]
  refine ⟨111242164801425470154036215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74161443200950313436024143 111242164801425470154036215)
  ·
    refine ⟨166863247202138205231054323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111242164801425470154036215 166863247202138205231054323)
    ·
      refine ⟨250294870803207307846581485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166863247202138205231054323 250294870803207307846581485)
      ·
        refine ⟨93860576551202740442468057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 250294870803207307846581485 93860576551202740442468057)
        ·
          refine ⟨70395432413402055331851043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93860576551202740442468057 70395432413402055331851043)
          ·
            refine ⟨105593148620103082997776565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70395432413402055331851043 105593148620103082997776565)
            ·
              refine ⟨9899357683134664031041553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 105593148620103082997776565 9899357683134664031041553)
              ·
                refine ⟨7424518262350998023281165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9899357683134664031041553 7424518262350998023281165)
                ·
                  refine ⟨2784194348381624258730437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7424518262350998023281165 2784194348381624258730437)
                  ·
                    refine ⟨522036440321554548511957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2784194348381624258730437 522036440321554548511957)
                    ·
                      rfl

theorem cell23_3049987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 5, 2, 3, 4].length) (baseStart_3049987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3049987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3049987 prefixEnd_3049987 := by exact prefixLift 3049987
  have htrace : WordTrace (prefixWord ++ tailWord_3049987) baseStart_3049987 baseEnd_3049987 := by
    simpa [prefixWord, tailWord_3049987, baseEnd_3049987] using wordTrace_append hprefix tailTrace_3049987
  have hstable : (prefixWord ++ tailWord_3049987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3049987).length < 2 ^ (prefixWord ++ tailWord_3049987).sum := by decide
  have hdescent : baseEnd_3049987 < baseStart_3049987 := by decide
  rcases family_descends (prefixWord ++ tailWord_3049987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3049991 : List Nat := [1, 1, 4, 3, 4, 1, 1, 1, 2, 5]
def baseStart_3049991 : Nat := 118140960795 + 3049991 * 2 ^ 59
def prefixEnd_3049991 : Nat := 4983230072969 + 3 ^ 40 * 3049991 * 2
def baseEnd_3049991 : Nat := 522037124962427209961951

theorem tailTrace_3049991 : CollatzResearch.WordTrace tailWord_3049991 prefixEnd_3049991 522037124962427209961951 := by
  unfold tailWord_3049991
  simp only [CollatzResearch.WordTrace]
  refine ⟨111242310693410978837181827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74161540462273985891454551 111242310693410978837181827)
  ·
    refine ⟨166863466040116468255772741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111242310693410978837181827 166863466040116468255772741)
    ·
      refine ⟨31286899882521837797957389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 166863466040116468255772741 31286899882521837797957389)
      ·
        refine ⟨11732587455945689174234021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31286899882521837797957389 11732587455945689174234021)
        ·
          refine ⟨2199860147989816720168879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11732587455945689174234021 2199860147989816720168879)
          ·
            refine ⟨3299790221984725080253319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2199860147989816720168879 3299790221984725080253319)
            ·
              refine ⟨4949685332977087620379979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3299790221984725080253319 4949685332977087620379979)
              ·
                refine ⟨7424527999465631430569969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4949685332977087620379979 7424527999465631430569969)
                ·
                  refine ⟨5568395999599223572927477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7424527999465631430569969 5568395999599223572927477)
                  ·
                    refine ⟨522037124962427209961951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5568395999599223572927477 522037124962427209961951)
                    ·
                      rfl

theorem cell23_3049991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 1, 1, 1, 2, 5].length) (baseStart_3049991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3049991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3049991 prefixEnd_3049991 := by exact prefixLift 3049991
  have htrace : WordTrace (prefixWord ++ tailWord_3049991) baseStart_3049991 baseEnd_3049991 := by
    simpa [prefixWord, tailWord_3049991, baseEnd_3049991] using wordTrace_append hprefix tailTrace_3049991
  have hstable : (prefixWord ++ tailWord_3049991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3049991).length < 2 ^ (prefixWord ++ tailWord_3049991).sum := by decide
  have hdescent : baseEnd_3049991 < baseStart_3049991 := by decide
  rcases family_descends (prefixWord ++ tailWord_3049991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3050087 : List Nat := [1, 1, 5, 1, 1, 1, 1, 1, 2, 6, 3]
def baseStart_3050087 : Nat := 118140960795 + 3050087 * 2 ^ 59
def prefixEnd_3050087 : Nat := 4983230072969 + 3 ^ 40 * 3050087 * 2
def baseEnd_3050087 : Nat := 1566160669030113254285411

theorem tailTrace_3050087 : CollatzResearch.WordTrace tailWord_3050087 prefixEnd_3050087 1566160669030113254285411 := by
  unfold tailWord_3050087
  simp only [CollatzResearch.WordTrace]
  refine ⟨111245812101063187232676515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74163874734042124821784343 111245812101063187232676515)
  ·
    refine ⟨166868718151594780849014773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111245812101063187232676515 166868718151594780849014773)
    ·
      refine ⟨15643942326712010704595135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 166868718151594780849014773 15643942326712010704595135)
      ·
        refine ⟨23465913490068016056892703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15643942326712010704595135 23465913490068016056892703)
        ·
          refine ⟨35198870235102024085339055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23465913490068016056892703 35198870235102024085339055)
          ·
            refine ⟨52798305352653036128008583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35198870235102024085339055 52798305352653036128008583)
            ·
              refine ⟨79197458028979554192012875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52798305352653036128008583 79197458028979554192012875)
              ·
                refine ⟨118796187043469331288019313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79197458028979554192012875 118796187043469331288019313)
                ·
                  refine ⟨89097140282601998466014485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 118796187043469331288019313 89097140282601998466014485)
                  ·
                    refine ⟨4176428450746968678094429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 89097140282601998466014485 4176428450746968678094429)
                    ·
                      refine ⟨1566160669030113254285411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4176428450746968678094429 1566160669030113254285411)
                      ·
                        rfl

theorem cell23_3050087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 1, 2, 6, 3].length) (baseStart_3050087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3050087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3050087 prefixEnd_3050087 := by exact prefixLift 3050087
  have htrace : WordTrace (prefixWord ++ tailWord_3050087) baseStart_3050087 baseEnd_3050087 := by
    simpa [prefixWord, tailWord_3050087, baseEnd_3050087] using wordTrace_append hprefix tailTrace_3050087
  have hstable : (prefixWord ++ tailWord_3050087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3050087).length < 2 ^ (prefixWord ++ tailWord_3050087).sum := by decide
  have hdescent : baseEnd_3050087 < baseStart_3050087 := by decide
  rcases family_descends (prefixWord ++ tailWord_3050087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3050098 : List Nat := [3, 2, 1, 2, 5, 1, 1, 2, 1, 5]
def baseStart_3050098 : Nat := 118140960795 + 3050098 * 2 ^ 59
def prefixEnd_3050098 : Nat := 4983230072969 + 3 ^ 40 * 3050098 * 2
def baseEnd_3050098 : Nat := 522055439105770903749287

theorem tailTrace_3050098 : CollatzResearch.WordTrace tailWord_3050098 prefixEnd_3050098 522055439105770903749287 := by
  unfold tailWord_3050098
  simp only [CollatzResearch.WordTrace]
  refine ⟨27811553326005834027831737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74164142202682224074217965 27811553326005834027831737)
  ·
    refine ⟨20858664994504375520873803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27811553326005834027831737 20858664994504375520873803)
    ·
      refine ⟨31287997491756563281310705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20858664994504375520873803 31287997491756563281310705)
      ·
        refine ⟨23465998118817422460983029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31287997491756563281310705 23465998118817422460983029)
        ·
          refine ⟨2199937323639133355717159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 23465998118817422460983029 2199937323639133355717159)
          ·
            refine ⟨3299905985458700033575739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2199937323639133355717159 3299905985458700033575739)
            ·
              refine ⟨4949858978188050050363609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3299905985458700033575739 4949858978188050050363609)
              ·
                refine ⟨3712394233641037537772707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4949858978188050050363609 3712394233641037537772707)
                ·
                  refine ⟨5568591350461556306659061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3712394233641037537772707 5568591350461556306659061)
                  ·
                    refine ⟨522055439105770903749287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5568591350461556306659061 522055439105770903749287)
                    ·
                      rfl

theorem cell23_3050098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 1, 1, 2, 1, 5].length) (baseStart_3050098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3050098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3050098 prefixEnd_3050098 := by exact prefixLift 3050098
  have htrace : WordTrace (prefixWord ++ tailWord_3050098) baseStart_3050098 baseEnd_3050098 := by
    simpa [prefixWord, tailWord_3050098, baseEnd_3050098] using wordTrace_append hprefix tailTrace_3050098
  have hstable : (prefixWord ++ tailWord_3050098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3050098).length < 2 ^ (prefixWord ++ tailWord_3050098).sum := by decide
  have hdescent : baseEnd_3050098 < baseStart_3050098 := by decide
  rcases family_descends (prefixWord ++ tailWord_3050098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3050101 : List Nat := [1, 3, 4, 2, 2, 1, 1, 1, 3, 1, 4]
def baseStart_3050101 : Nat := 118140960795 + 3050101 * 2 ^ 59
def prefixEnd_3050101 : Nat := 4983230072969 + 3 ^ 40 * 3050101 * 2
def baseEnd_3050101 : Nat := 1566167857759276199510347

theorem tailTrace_3050101 : CollatzResearch.WordTrace tailWord_3050101 prefixEnd_3050101 1566167857759276199510347 := by
  unfold tailWord_3050101
  simp only [CollatzResearch.WordTrace]
  refine ⟨111246322723012467623686157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74164215148674978415790771 111246322723012467623686157)
  ·
    refine ⟨41717371021129675358882309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111246322723012467623686157 41717371021129675358882309)
    ·
      refine ⟨7822007066461814129790433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41717371021129675358882309 7822007066461814129790433)
      ·
        refine ⟨5866505299846360597342825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7822007066461814129790433 5866505299846360597342825)
        ·
          refine ⟨4399878974884770448007119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5866505299846360597342825 4399878974884770448007119)
          ·
            refine ⟨6599818462327155672010679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4399878974884770448007119 6599818462327155672010679)
            ·
              refine ⟨9899727693490733508016019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6599818462327155672010679 9899727693490733508016019)
              ·
                refine ⟨14849591540236100262024029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9899727693490733508016019 14849591540236100262024029)
                ·
                  refine ⟨5568596827588537598259011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14849591540236100262024029 5568596827588537598259011)
                  ·
                    refine ⟨8352895241382806397388517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5568596827588537598259011 8352895241382806397388517)
                    ·
                      refine ⟨1566167857759276199510347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8352895241382806397388517 1566167857759276199510347)
                      ·
                        rfl

theorem cell23_3050101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 1, 1, 3, 1, 4].length) (baseStart_3050101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3050101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3050101 prefixEnd_3050101 := by exact prefixLift 3050101
  have htrace : WordTrace (prefixWord ++ tailWord_3050101) baseStart_3050101 baseEnd_3050101 := by
    simpa [prefixWord, tailWord_3050101, baseEnd_3050101] using wordTrace_append hprefix tailTrace_3050101
  have hstable : (prefixWord ++ tailWord_3050101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3050101).length < 2 ^ (prefixWord ++ tailWord_3050101).sum := by decide
  have hdescent : baseEnd_3050101 < baseStart_3050101 := by decide
  rcases family_descends (prefixWord ++ tailWord_3050101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3050248 : List Nat := [2, 1, 3, 2, 2, 3, 3, 2, 5]
def baseStart_3050248 : Nat := 118140960795 + 3050248 * 2 ^ 59
def prefixEnd_3050248 : Nat := 4983230072969 + 3 ^ 40 * 3050248 * 2
def baseEnd_3050248 : Nat := 174027037712831902708019

theorem tailTrace_3050248 : CollatzResearch.WordTrace tailWord_3050248 prefixEnd_3050248 174027037712831902708019 := by
  unfold tailWord_3050248
  simp only [CollatzResearch.WordTrace]
  refine ⟨55625842126739955864643699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74167789502319941152858265 55625842126739955864643699)
  ·
    refine ⟨83438763190109933796965549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55625842126739955864643699 83438763190109933796965549)
    ·
      refine ⟨31289536196291225173862081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83438763190109933796965549 31289536196291225173862081)
      ·
        refine ⟨23467152147218418880396561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31289536196291225173862081 23467152147218418880396561)
        ·
          refine ⟨17600364110413814160297421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23467152147218418880396561 17600364110413814160297421)
          ·
            refine ⟨6600136541405180310111533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17600364110413814160297421 6600136541405180310111533)
            ·
              refine ⟨2475051203026942616291825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6600136541405180310111533 2475051203026942616291825)
              ·
                refine ⟨1856288402270206962218869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2475051203026942616291825 1856288402270206962218869)
                ·
                  refine ⟨174027037712831902708019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1856288402270206962218869 174027037712831902708019)
                  ·
                    rfl

theorem cell23_3050248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 3, 2, 5].length) (baseStart_3050248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3050248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3050248 prefixEnd_3050248 := by exact prefixLift 3050248
  have htrace : WordTrace (prefixWord ++ tailWord_3050248) baseStart_3050248 baseEnd_3050248 := by
    simpa [prefixWord, tailWord_3050248, baseEnd_3050248] using wordTrace_append hprefix tailTrace_3050248
  have hstable : (prefixWord ++ tailWord_3050248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3050248).length < 2 ^ (prefixWord ++ tailWord_3050248).sum := by decide
  have hdescent : baseEnd_3050248 < baseStart_3050248 := by decide
  rcases family_descends (prefixWord ++ tailWord_3050248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3050264 : List Nat := [2, 1, 2, 3, 1, 1, 1, 1, 6, 1, 4]
def baseStart_3050264 : Nat := 118140960795 + 3050264 * 2 ^ 59
def prefixEnd_3050264 : Nat := 4983230072969 + 3 ^ 40 * 3050264 * 2
def baseEnd_3050264 : Nat := 1566251555105959061772097

theorem tailTrace_3050264 : CollatzResearch.WordTrace tailWord_3050264 prefixEnd_3050264 1566251555105959061772097 := by
  unfold tailWord_3050264
  simp only [CollatzResearch.WordTrace]
  refine ⟨55626133910710973230934923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74168178547614630974579897 55626133910710973230934923)
  ·
    refine ⟨83439200866066459846402385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55626133910710973230934923 83439200866066459846402385)
    ·
      refine ⟨62579400649549844884801789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83439200866066459846402385 62579400649549844884801789)
      ·
        refine ⟨23467275243581191831800671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62579400649549844884801789 23467275243581191831800671)
        ·
          refine ⟨35200912865371787747701007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23467275243581191831800671 35200912865371787747701007)
          ·
            refine ⟨52801369298057681621551511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35200912865371787747701007 52801369298057681621551511)
            ·
              refine ⟨79202053947086522432327267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52801369298057681621551511 79202053947086522432327267)
              ·
                refine ⟨118803080920629783648490901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79202053947086522432327267 118803080920629783648490901)
                ·
                  refine ⟨5568894418154521108523011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 118803080920629783648490901 5568894418154521108523011)
                  ·
                    refine ⟨8353341627231781662784517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5568894418154521108523011 8353341627231781662784517)
                    ·
                      refine ⟨1566251555105959061772097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8353341627231781662784517 1566251555105959061772097)
                      ·
                        rfl

theorem cell23_3050264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 1, 6, 1, 4].length) (baseStart_3050264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3050264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3050264 prefixEnd_3050264 := by exact prefixLift 3050264
  have htrace : WordTrace (prefixWord ++ tailWord_3050264) baseStart_3050264 baseEnd_3050264 := by
    simpa [prefixWord, tailWord_3050264, baseEnd_3050264] using wordTrace_append hprefix tailTrace_3050264
  have hstable : (prefixWord ++ tailWord_3050264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3050264).length < 2 ^ (prefixWord ++ tailWord_3050264).sum := by decide
  have hdescent : baseEnd_3050264 < baseStart_3050264 := by decide
  rcases family_descends (prefixWord ++ tailWord_3050264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3050364 : List Nat := [2, 2, 2, 1, 1, 1, 1, 4, 3, 6]
def baseStart_3050364 : Nat := 118140960795 + 3050364 * 2 ^ 59
def prefixEnd_3050364 : Nat := 4983230072969 + 3 ^ 40 * 3050364 * 2
def baseEnd_3050364 : Nat := 522100967723802890173879

theorem tailTrace_3050364 : CollatzResearch.WordTrace tailWord_3050364 prefixEnd_3050364 522100967723802890173879 := by
  unfold tailWord_3050364
  simp only [CollatzResearch.WordTrace]
  refine ⟨55627957560529831770255073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74170610080706442360340097 55627957560529831770255073)
  ·
    refine ⟨41720968170397373827691305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55627957560529831770255073 41720968170397373827691305)
    ·
      refine ⟨31290726127798030370768479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41720968170397373827691305 31290726127798030370768479)
      ·
        refine ⟨46936089191697045556152719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31290726127798030370768479 46936089191697045556152719)
        ·
          refine ⟨70404133787545568334229079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46936089191697045556152719 70404133787545568334229079)
          ·
            refine ⟨105606200681318352501343619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70404133787545568334229079 105606200681318352501343619)
            ·
              refine ⟨158409301021977528752015429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105606200681318352501343619 158409301021977528752015429)
              ·
                refine ⟨29701743941620786641002893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 158409301021977528752015429 29701743941620786641002893)
                ·
                  refine ⟨11138153978107794990376085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29701743941620786641002893 11138153978107794990376085)
                  ·
                    refine ⟨522100967723802890173879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11138153978107794990376085 522100967723802890173879)
                    ·
                      rfl

theorem cell23_3050364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 4, 3, 6].length) (baseStart_3050364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3050364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3050364 prefixEnd_3050364 := by exact prefixLift 3050364
  have htrace : WordTrace (prefixWord ++ tailWord_3050364) baseStart_3050364 baseEnd_3050364 := by
    simpa [prefixWord, tailWord_3050364, baseEnd_3050364] using wordTrace_append hprefix tailTrace_3050364
  have hstable : (prefixWord ++ tailWord_3050364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3050364).length < 2 ^ (prefixWord ++ tailWord_3050364).sum := by decide
  have hdescent : baseEnd_3050364 < baseStart_3050364 := by decide
  rcases family_descends (prefixWord ++ tailWord_3050364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3050365 : List Nat := [1, 4, 1, 1, 2, 1, 4, 4, 1, 1, 3]
def baseStart_3050365 : Nat := 118140960795 + 3050365 * 2 ^ 59
def prefixEnd_3050365 : Nat := 4983230072969 + 3 ^ 40 * 3050365 * 2
def baseEnd_3050365 : Nat := 1566303416652063166609133

theorem tailTrace_3050365 : CollatzResearch.WordTrace tailWord_3050365 prefixEnd_3050365 1566303416652063166609133 := by
  unfold tailWord_3050365
  simp only [CollatzResearch.WordTrace]
  refine ⟨111255951594056040711296549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74170634396037360474197699 111255951594056040711296549)
  ·
    refine ⟨20860490923885507633368103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 111255951594056040711296549 20860490923885507633368103)
    ·
      refine ⟨31290736385828261450052155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20860490923885507633368103 31290736385828261450052155)
      ·
        refine ⟨46936104578742392175078233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31290736385828261450052155 46936104578742392175078233)
        ·
          refine ⟨35202078434056794131308675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46936104578742392175078233 35202078434056794131308675)
          ·
            refine ⟨52803117651085191196963013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35202078434056794131308675 52803117651085191196963013)
            ·
              refine ⟨9900584559578473349430565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52803117651085191196963013 9900584559578473349430565)
              ·
                refine ⟨1856359604920963753018231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9900584559578473349430565 1856359604920963753018231)
                ·
                  refine ⟨2784539407381445629527347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1856359604920963753018231 2784539407381445629527347)
                  ·
                    refine ⟨4176809111072168444291021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2784539407381445629527347 4176809111072168444291021)
                    ·
                      refine ⟨1566303416652063166609133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4176809111072168444291021 1566303416652063166609133)
                      ·
                        rfl

theorem cell23_3050365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 4, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 4, 4, 1, 1, 3].length) (baseStart_3050365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3050365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3050365 prefixEnd_3050365 := by exact prefixLift 3050365
  have htrace : WordTrace (prefixWord ++ tailWord_3050365) baseStart_3050365 baseEnd_3050365 := by
    simpa [prefixWord, tailWord_3050365, baseEnd_3050365] using wordTrace_append hprefix tailTrace_3050365
  have hstable : (prefixWord ++ tailWord_3050365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3050365).length < 2 ^ (prefixWord ++ tailWord_3050365).sum := by decide
  have hdescent : baseEnd_3050365 < baseStart_3050365 := by decide
  rcases family_descends (prefixWord ++ tailWord_3050365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3050388 : List Nat := [2, 4, 2, 1, 1, 1, 1, 1, 2, 6, 2]
def baseStart_3050388 : Nat := 118140960795 + 3050388 * 2 ^ 59
def prefixEnd_3050388 : Nat := 4983230072969 + 3 ^ 40 * 3050388 * 2
def baseEnd_3050388 : Nat := 1566315226707116576621527

theorem tailTrace_3050388 : CollatzResearch.WordTrace tailWord_3050388 prefixEnd_3050388 1566315226707116576621527 := by
  unfold tailWord_3050388
  simp only [CollatzResearch.WordTrace]
  refine ⟨55628395236486357819691909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74171193648648477092922545 55628395236486357819691909)
  ·
    refine ⟨10430324106841192091192233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55628395236486357819691909 10430324106841192091192233)
    ·
      refine ⟨7822743080130894068394175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10430324106841192091192233 7822743080130894068394175)
      ·
        refine ⟨11734114620196341102591263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7822743080130894068394175 11734114620196341102591263)
        ·
          refine ⟨17601171930294511653886895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11734114620196341102591263 17601171930294511653886895)
          ·
            refine ⟨26401757895441767480830343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17601171930294511653886895 26401757895441767480830343)
            ·
              refine ⟨39602636843162651221245515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26401757895441767480830343 39602636843162651221245515)
              ·
                refine ⟨59403955264743976831868273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39602636843162651221245515 59403955264743976831868273)
                ·
                  refine ⟨44552966448557982623901205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59403955264743976831868273 44552966448557982623901205)
                  ·
                    refine ⟨2088420302276155435495369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 44552966448557982623901205 2088420302276155435495369)
                    ·
                      refine ⟨1566315226707116576621527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2088420302276155435495369 1566315226707116576621527)
                      ·
                        rfl

theorem cell23_3050388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 1, 2, 6, 2].length) (baseStart_3050388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3050388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3050388 prefixEnd_3050388 := by exact prefixLift 3050388
  have htrace : WordTrace (prefixWord ++ tailWord_3050388) baseStart_3050388 baseEnd_3050388 := by
    simpa [prefixWord, tailWord_3050388, baseEnd_3050388] using wordTrace_append hprefix tailTrace_3050388
  have hstable : (prefixWord ++ tailWord_3050388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3050388).length < 2 ^ (prefixWord ++ tailWord_3050388).sum := by decide
  have hdescent : baseEnd_3050388 < baseStart_3050388 := by decide
  rcases family_descends (prefixWord ++ tailWord_3050388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3050501 : List Nat := [1, 3, 1, 1, 2, 3, 3, 2, 7]
def baseStart_3050501 : Nat := 118140960795 + 3050501 * 2 ^ 59
def prefixEnd_3050501 : Nat := 4983230072969 + 3 ^ 40 * 3050501 * 2
def baseEnd_3050501 : Nat := 174041472224563848278723

theorem tailTrace_3050501 : CollatzResearch.WordTrace tailWord_3050501 prefixEnd_3050501 174041472224563848278723 := by
  unfold tailWord_3050501
  simp only [CollatzResearch.WordTrace]
  refine ⟨111260911921563335938247357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74173941281042223958831571 111260911921563335938247357)
  ·
    refine ⟨41722841970586250976842759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111260911921563335938247357 41722841970586250976842759)
    ·
      refine ⟨62584262955879376465264139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41722841970586250976842759 62584262955879376465264139)
      ·
        refine ⟨93876394433819064697896209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62584262955879376465264139 93876394433819064697896209)
        ·
          refine ⟨70407295825364298523422157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93876394433819064697896209 70407295825364298523422157)
          ·
            refine ⟨26402735934511611946283309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70407295825364298523422157 26402735934511611946283309)
            ·
              refine ⟨9901025975441854479856241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26402735934511611946283309 9901025975441854479856241)
              ·
                refine ⟨7425769481581390859892181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9901025975441854479856241 7425769481581390859892181)
                ·
                  refine ⟨174041472224563848278723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7425769481581390859892181 174041472224563848278723)
                  ·
                    rfl

theorem cell23_3050501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 3, 2, 7].length) (baseStart_3050501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3050501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3050501 prefixEnd_3050501 := by exact prefixLift 3050501
  have htrace : WordTrace (prefixWord ++ tailWord_3050501) baseStart_3050501 baseEnd_3050501 := by
    simpa [prefixWord, tailWord_3050501, baseEnd_3050501] using wordTrace_append hprefix tailTrace_3050501
  have hstable : (prefixWord ++ tailWord_3050501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3050501).length < 2 ^ (prefixWord ++ tailWord_3050501).sum := by decide
  have hdescent : baseEnd_3050501 < baseStart_3050501 := by decide
  rcases family_descends (prefixWord ++ tailWord_3050501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3050529 : List Nat := [1, 2, 3, 2, 3, 3, 1, 2, 2, 2, 2]
def baseStart_3050529 : Nat := 118140960795 + 3050529 * 2 ^ 59
def prefixEnd_3050529 : Nat := 4983230072969 + 3 ^ 40 * 3050529 * 2
def baseEnd_3050529 : Nat := 1566387627479400524958379

theorem tailTrace_3050529 : CollatzResearch.WordTrace tailWord_3050529 prefixEnd_3050529 1566387627479400524958379 := by
  unfold tailWord_3050529
  simp only [CollatzResearch.WordTrace]
  refine ⟨111261933165461896720266641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74174622110307931146844427 111261933165461896720266641)
  ·
    refine ⟨83446449874096422540199981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111261933165461896720266641 83446449874096422540199981)
    ·
      refine ⟨31292418702786158452574993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83446449874096422540199981 31292418702786158452574993)
      ·
        refine ⟨23469314027089618839431245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31292418702786158452574993 23469314027089618839431245)
        ·
          refine ⟨8800992760158607064786717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23469314027089618839431245 8800992760158607064786717)
          ·
            refine ⟨3300372285059477649295019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8800992760158607064786717 3300372285059477649295019)
            ·
              refine ⟨4950558427589216473942529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3300372285059477649295019 4950558427589216473942529)
              ·
                refine ⟨3712918820691912355456897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4950558427589216473942529 3712918820691912355456897)
                ·
                  refine ⟨2784689115518934266592673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3712918820691912355456897 2784689115518934266592673)
                  ·
                    refine ⟨2088516836639200699944505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2784689115518934266592673 2088516836639200699944505)
                    ·
                      refine ⟨1566387627479400524958379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2088516836639200699944505 1566387627479400524958379)
                      ·
                        rfl

theorem cell23_3050529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 3, 1, 2, 2, 2, 2].length) (baseStart_3050529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3050529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3050529 prefixEnd_3050529 := by exact prefixLift 3050529
  have htrace : WordTrace (prefixWord ++ tailWord_3050529) baseStart_3050529 baseEnd_3050529 := by
    simpa [prefixWord, tailWord_3050529, baseEnd_3050529] using wordTrace_append hprefix tailTrace_3050529
  have hstable : (prefixWord ++ tailWord_3050529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3050529).length < 2 ^ (prefixWord ++ tailWord_3050529).sum := by decide
  have hdescent : baseEnd_3050529 < baseStart_3050529 := by decide
  rcases family_descends (prefixWord ++ tailWord_3050529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3050535 : List Nat := [1, 1, 7, 1, 1, 2, 2, 1, 7]
def baseStart_3050535 : Nat := 118140960795 + 3050535 * 2 ^ 59
def prefixEnd_3050535 : Nat := 4983230072969 + 3 ^ 40 * 3050535 * 2
def baseEnd_3050535 : Nat := 174043412040369722387039

theorem tailTrace_3050535 : CollatzResearch.WordTrace tailWord_3050535 prefixEnd_3050535 174043412040369722387039 := by
  unfold tailWord_3050535
  simp only [CollatzResearch.WordTrace]
  refine ⟨111262152003440159744985059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74174768002293439829990039 111262152003440159744985059)
  ·
    refine ⟨166893228005160239617477589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111262152003440159744985059 166893228005160239617477589)
    ·
      refine ⟨3911560031370943116034631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 166893228005160239617477589 3911560031370943116034631)
      ·
        refine ⟨5867340047056414674051947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3911560031370943116034631 5867340047056414674051947)
        ·
          refine ⟨8801010070584622011077921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5867340047056414674051947 8801010070584622011077921)
          ·
            refine ⟨6600757552938466508308441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8801010070584622011077921 6600757552938466508308441)
            ·
              refine ⟨4950568164703849881231331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6600757552938466508308441 4950568164703849881231331)
              ·
                refine ⟨7425852247055774821846997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4950568164703849881231331 7425852247055774821846997)
                ·
                  refine ⟨174043412040369722387039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7425852247055774821846997 174043412040369722387039)
                  ·
                    rfl

theorem cell23_3050535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 2, 1, 7].length) (baseStart_3050535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3050535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3050535 prefixEnd_3050535 := by exact prefixLift 3050535
  have htrace : WordTrace (prefixWord ++ tailWord_3050535) baseStart_3050535 baseEnd_3050535 := by
    simpa [prefixWord, tailWord_3050535, baseEnd_3050535] using wordTrace_append hprefix tailTrace_3050535
  have hstable : (prefixWord ++ tailWord_3050535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3050535).length < 2 ^ (prefixWord ++ tailWord_3050535).sum := by decide
  have hdescent : baseEnd_3050535 < baseStart_3050535 := by decide
  rcases family_descends (prefixWord ++ tailWord_3050535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3050568 : List Nat := [2, 1, 3, 1, 1, 1, 4, 3, 2, 1, 4]
def baseStart_3050568 : Nat := 118140960795 + 3050568 * 2 ^ 59
def prefixEnd_3050568 : Nat := 4983230072969 + 3 ^ 40 * 3050568 * 2
def baseEnd_3050568 : Nat := 1566407653224925872370699

theorem tailTrace_3050568 : CollatzResearch.WordTrace tailWord_3050568 prefixEnd_3050568 1566407653224925872370699 := by
  unfold tailWord_3050568
  simp only [CollatzResearch.WordTrace]
  refine ⟨55631677806160303190468179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74175570408213737587290905 55631677806160303190468179)
  ·
    refine ⟨83447516709240454785702269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55631677806160303190468179 83447516709240454785702269)
    ·
      refine ⟨31292818765965170544638351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83447516709240454785702269 31292818765965170544638351)
      ·
        refine ⟨46939228148947755816957527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31292818765965170544638351 46939228148947755816957527)
        ·
          refine ⟨70408842223421633725436291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46939228148947755816957527 70408842223421633725436291)
          ·
            refine ⟨105613263335132450588154437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70408842223421633725436291 105613263335132450588154437)
            ·
              refine ⟨19802486875337334485278957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 105613263335132450588154437 19802486875337334485278957)
              ·
                refine ⟨7425932578251500431979609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19802486875337334485278957 7425932578251500431979609)
                ·
                  refine ⟨5569449433688625323984707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7425932578251500431979609 5569449433688625323984707)
                  ·
                    refine ⟨8354174150532937985977061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5569449433688625323984707 8354174150532937985977061)
                    ·
                      refine ⟨1566407653224925872370699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8354174150532937985977061 1566407653224925872370699)
                      ·
                        rfl

theorem cell23_3050568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 3, 2, 1, 4].length) (baseStart_3050568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3050568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3050568 prefixEnd_3050568 := by exact prefixLift 3050568
  have htrace : WordTrace (prefixWord ++ tailWord_3050568) baseStart_3050568 baseEnd_3050568 := by
    simpa [prefixWord, tailWord_3050568, baseEnd_3050568] using wordTrace_append hprefix tailTrace_3050568
  have hstable : (prefixWord ++ tailWord_3050568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3050568).length < 2 ^ (prefixWord ++ tailWord_3050568).sum := by decide
  have hdescent : baseEnd_3050568 < baseStart_3050568 := by decide
  rcases family_descends (prefixWord ++ tailWord_3050568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3050591 : List Nat := [1, 1, 2, 3, 1, 1, 3, 3, 8]
def baseStart_3050591 : Nat := 118140960795 + 3050591 * 2 ^ 59
def prefixEnd_3050591 : Nat := 4983230072969 + 3 ^ 40 * 3050591 * 2
def baseEnd_3050591 : Nat := 174046607031108809153677

theorem tailTrace_3050591 : CollatzResearch.WordTrace tailWord_3050591 prefixEnd_3050591 174046607031108809153677 := by
  unfold tailWord_3050591
  simp only [CollatzResearch.WordTrace]
  refine ⟨111264194491237281309023627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74176129660824854206015751 111264194491237281309023627)
  ·
    refine ⟨166896291736855921963535441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111264194491237281309023627 166896291736855921963535441)
    ·
      refine ⟨125172218802641941472651581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166896291736855921963535441 125172218802641941472651581)
      ·
        refine ⟨46939582050990728052244343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 125172218802641941472651581 46939582050990728052244343)
        ·
          refine ⟨70409373076486092078366515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46939582050990728052244343 70409373076486092078366515)
          ·
            refine ⟨105614059614729138117549773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70409373076486092078366515 105614059614729138117549773)
            ·
              refine ⟨39605272355523426794081165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 105614059614729138117549773 39605272355523426794081165)
              ·
                refine ⟨14851977133321285047780437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39605272355523426794081165 14851977133321285047780437)
                ·
                  refine ⟨174046607031108809153677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 14851977133321285047780437 174046607031108809153677)
                  ·
                    rfl

theorem cell23_3050591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 3, 8].length) (baseStart_3050591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3050591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3050591 prefixEnd_3050591 := by exact prefixLift 3050591
  have htrace : WordTrace (prefixWord ++ tailWord_3050591) baseStart_3050591 baseEnd_3050591 := by
    simpa [prefixWord, tailWord_3050591, baseEnd_3050591] using wordTrace_append hprefix tailTrace_3050591
  have hstable : (prefixWord ++ tailWord_3050591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3050591).length < 2 ^ (prefixWord ++ tailWord_3050591).sum := by decide
  have hdescent : baseEnd_3050591 < baseStart_3050591 := by decide
  rcases family_descends (prefixWord ++ tailWord_3050591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3050608 : List Nat := [2, 1, 1, 1, 5, 1, 3, 3, 6]
def baseStart_3050608 : Nat := 118140960795 + 3050608 * 2 ^ 59
def prefixEnd_3050608 : Nat := 4983230072969 + 3 ^ 40 * 3050608 * 2
def baseEnd_3050608 : Nat := 174047576939011746207835

theorem tailTrace_3050608 : CollatzResearch.WordTrace tailWord_3050608 prefixEnd_3050608 174047576939011746207835 := by
  unfold tailWord_3050608
  simp only [CollatzResearch.WordTrace]
  refine ⟨55632407266087846606196239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74176543021450462141594985 55632407266087846606196239)
  ·
    refine ⟨83448610899131769909294359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55632407266087846606196239 83448610899131769909294359)
    ·
      refine ⟨125172916348697654863941539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83448610899131769909294359 125172916348697654863941539)
      ·
        refine ⟨187759374523046482295912309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125172916348697654863941539 187759374523046482295912309)
        ·
          refine ⟨17602441361535607715241779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 187759374523046482295912309 17602441361535607715241779)
          ·
            refine ⟨26403662042303411572862669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17602441361535607715241779 26403662042303411572862669)
            ·
              refine ⟨9901373265863779339823501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26403662042303411572862669 9901373265863779339823501)
              ·
                refine ⟨3713014974698917252433813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9901373265863779339823501 3713014974698917252433813)
                ·
                  refine ⟨174047576939011746207835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3713014974698917252433813 174047576939011746207835)
                  ·
                    rfl

theorem cell23_3050608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 3, 3, 6].length) (baseStart_3050608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3050608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3050608 prefixEnd_3050608 := by exact prefixLift 3050608
  have htrace : WordTrace (prefixWord ++ tailWord_3050608) baseStart_3050608 baseEnd_3050608 := by
    simpa [prefixWord, tailWord_3050608, baseEnd_3050608] using wordTrace_append hprefix tailTrace_3050608
  have hstable : (prefixWord ++ tailWord_3050608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3050608).length < 2 ^ (prefixWord ++ tailWord_3050608).sum := by decide
  have hdescent : baseEnd_3050608 < baseStart_3050608 := by decide
  rcases family_descends (prefixWord ++ tailWord_3050608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3050645 : List Nat := [1, 3, 2, 1, 1, 1, 2, 3, 4, 3, 2]
def baseStart_3050645 : Nat := 118140960795 + 3050645 * 2 ^ 59
def prefixEnd_3050645 : Nat := 4983230072969 + 3 ^ 40 * 3050645 * 2
def baseEnd_3050645 : Nat := 1566447191235322071107845

theorem tailTrace_3050645 : CollatzResearch.WordTrace tailWord_3050645 prefixEnd_3050645 1566447191235322071107845 := by
  unfold tailWord_3050645
  simp only [CollatzResearch.WordTrace]
  refine ⟨111266164033041648531489389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74177442688694432354326259 111266164033041648531489389)
  ·
    refine ⟨41724811512390618199308521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111266164033041648531489389 41724811512390618199308521)
    ·
      refine ⟨31293608634292963649481391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41724811512390618199308521 31293608634292963649481391)
      ·
        refine ⟨46940412951439445474222087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31293608634292963649481391 46940412951439445474222087)
        ·
          refine ⟨70410619427159168211333131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46940412951439445474222087 70410619427159168211333131)
          ·
            refine ⟨105615929140738752316999697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70410619427159168211333131 105615929140738752316999697)
            ·
              refine ⟨79211946855554064237749773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 105615929140738752316999697 79211946855554064237749773)
              ·
                refine ⟨29704480070832774089156165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 79211946855554064237749773 29704480070832774089156165)
                ·
                  refine ⟨5569590013281145141716781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29704480070832774089156165 5569590013281145141716781)
                  ·
                    refine ⟨2088596254980429428143793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5569590013281145141716781 2088596254980429428143793)
                    ·
                      refine ⟨1566447191235322071107845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2088596254980429428143793 1566447191235322071107845)
                      ·
                        rfl

theorem cell23_3050645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 3, 4, 3, 2].length) (baseStart_3050645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3050645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3050645 prefixEnd_3050645 := by exact prefixLift 3050645
  have htrace : WordTrace (prefixWord ++ tailWord_3050645) baseStart_3050645 baseEnd_3050645 := by
    simpa [prefixWord, tailWord_3050645, baseEnd_3050645] using wordTrace_append hprefix tailTrace_3050645
  have hstable : (prefixWord ++ tailWord_3050645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3050645).length < 2 ^ (prefixWord ++ tailWord_3050645).sum := by decide
  have hdescent : baseEnd_3050645 < baseStart_3050645 := by decide
  rcases family_descends (prefixWord ++ tailWord_3050645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3050651 : List Nat := [1, 1, 1, 1, 1, 1, 2, 3, 2, 10]
def baseStart_3050651 : Nat := 118140960795 + 3050651 * 2 ^ 59
def prefixEnd_3050651 : Nat := 4983230072969 + 3 ^ 40 * 3050651 * 2
def baseEnd_3050651 : Nat := 522150090706416349210939

theorem tailTrace_3050651 : CollatzResearch.WordTrace tailWord_3050651 prefixEnd_3050651 522150090706416349210939 := by
  unfold tailWord_3050651
  simp only [CollatzResearch.WordTrace]
  refine ⟨111266382871019911556207807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74177588580679941037471871 111266382871019911556207807)
  ·
    refine ⟨166899574306529867334311711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111266382871019911556207807 166899574306529867334311711)
    ·
      refine ⟨250349361459794801001467567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166899574306529867334311711 250349361459794801001467567)
      ·
        refine ⟨375524042189692201502201351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 250349361459794801001467567 375524042189692201502201351)
        ·
          refine ⟨563286063284538302253302027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 375524042189692201502201351 563286063284538302253302027)
          ·
            refine ⟨844929094926807453379953041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 563286063284538302253302027 844929094926807453379953041)
            ·
              refine ⟨633696821195105590034964781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 844929094926807453379953041 633696821195105590034964781)
              ·
                refine ⟨237636307948164596263111793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 633696821195105590034964781 237636307948164596263111793)
                ·
                  refine ⟨178227230961123447197333845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 237636307948164596263111793 178227230961123447197333845)
                  ·
                    refine ⟨522150090706416349210939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 178227230961123447197333845 522150090706416349210939)
                    ·
                      rfl

theorem cell23_3050651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 2, 10].length) (baseStart_3050651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3050651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3050651 prefixEnd_3050651 := by exact prefixLift 3050651
  have htrace : WordTrace (prefixWord ++ tailWord_3050651) baseStart_3050651 baseEnd_3050651 := by
    simpa [prefixWord, tailWord_3050651, baseEnd_3050651] using wordTrace_append hprefix tailTrace_3050651
  have hstable : (prefixWord ++ tailWord_3050651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3050651).length < 2 ^ (prefixWord ++ tailWord_3050651).sum := by decide
  have hdescent : baseEnd_3050651 < baseStart_3050651 := by decide
  rcases family_descends (prefixWord ++ tailWord_3050651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3050669 : List Nat := [1, 5, 2, 1, 3, 1, 1, 2, 3, 1, 3]
def baseStart_3050669 : Nat := 118140960795 + 3050669 * 2 ^ 59
def prefixEnd_3050669 : Nat := 4983230072969 + 3 ^ 40 * 3050669 * 2
def baseEnd_3050669 : Nat := 1566459514771029977207735

theorem tailTrace_3050669 : CollatzResearch.WordTrace tailWord_3050669 prefixEnd_3050669 1566459514771029977207735 := by
  unfold tailWord_3050669
  simp only [CollatzResearch.WordTrace]
  refine ⟨111267039384954700630363061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74178026256636467086908707 111267039384954700630363061)
  ·
    refine ⟨10431284942339503184096537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 111267039384954700630363061 10431284942339503184096537)
    ·
      refine ⟨7823463706754627388072403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10431284942339503184096537 7823463706754627388072403)
      ·
        refine ⟨11735195560131941082108605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7823463706754627388072403 11735195560131941082108605)
        ·
          refine ⟨4400698335049477905790727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11735195560131941082108605 4400698335049477905790727)
          ·
            refine ⟨6601047502574216858686091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4400698335049477905790727 6601047502574216858686091)
            ·
              refine ⟨9901571253861325288029137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6601047502574216858686091 9901571253861325288029137)
              ·
                refine ⟨7426178440395993966021853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9901571253861325288029137 7426178440395993966021853)
                ·
                  refine ⟨2784816915148497737258195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7426178440395993966021853 2784816915148497737258195)
                  ·
                    refine ⟨4177225372722746605887293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2784816915148497737258195 4177225372722746605887293)
                    ·
                      refine ⟨1566459514771029977207735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4177225372722746605887293 1566459514771029977207735)
                      ·
                        rfl

theorem cell23_3050669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 1, 2, 3, 1, 3].length) (baseStart_3050669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3050669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3050669 prefixEnd_3050669 := by exact prefixLift 3050669
  have htrace : WordTrace (prefixWord ++ tailWord_3050669) baseStart_3050669 baseEnd_3050669 := by
    simpa [prefixWord, tailWord_3050669, baseEnd_3050669] using wordTrace_append hprefix tailTrace_3050669
  have hstable : (prefixWord ++ tailWord_3050669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3050669).length < 2 ^ (prefixWord ++ tailWord_3050669).sum := by decide
  have hdescent : baseEnd_3050669 < baseStart_3050669 := by decide
  rcases family_descends (prefixWord ++ tailWord_3050669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3050686 : List Nat := [4, 2, 1, 1, 3, 2, 2, 3, 1, 1, 3]
def baseStart_3050686 : Nat := 118140960795 + 3050686 * 2 ^ 59
def prefixEnd_3050686 : Nat := 4983230072969 + 3 ^ 40 * 3050686 * 2
def baseEnd_3050686 : Nat := 1566468243942156410695157

theorem tailTrace_3050686 : CollatzResearch.WordTrace tailWord_3050686 prefixEnd_3050686 1566468243942156410695157 := by
  unfold tailWord_3050686
  simp only [CollatzResearch.WordTrace]
  refine ⟨13908457428236639066716489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74178439617262075022487941 13908457428236639066716489)
  ·
    refine ⟨10431343071177479300037367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13908457428236639066716489 10431343071177479300037367)
    ·
      refine ⟨15647014606766218950056051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10431343071177479300037367 15647014606766218950056051)
      ·
        refine ⟨23470521910149328425084077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15647014606766218950056051 23470521910149328425084077)
        ·
          refine ⟨8801445716305998159406529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23470521910149328425084077 8801445716305998159406529)
          ·
            refine ⟨6601084287229498619554897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8801445716305998159406529 6601084287229498619554897)
            ·
              refine ⟨4950813215422123964666173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6601084287229498619554897 4950813215422123964666173)
              ·
                refine ⟨1856554955783296486749815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4950813215422123964666173 1856554955783296486749815)
                ·
                  refine ⟨2784832433674944730124723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1856554955783296486749815 2784832433674944730124723)
                  ·
                    refine ⟨4177248650512417095187085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2784832433674944730124723 4177248650512417095187085)
                    ·
                      refine ⟨1566468243942156410695157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4177248650512417095187085 1566468243942156410695157)
                      ·
                        rfl

theorem cell23_3050686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 2, 3, 1, 1, 3].length) (baseStart_3050686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3050686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3050686 prefixEnd_3050686 := by exact prefixLift 3050686
  have htrace : WordTrace (prefixWord ++ tailWord_3050686) baseStart_3050686 baseEnd_3050686 := by
    simpa [prefixWord, tailWord_3050686, baseEnd_3050686] using wordTrace_append hprefix tailTrace_3050686
  have hstable : (prefixWord ++ tailWord_3050686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3050686).length < 2 ^ (prefixWord ++ tailWord_3050686).sum := by decide
  have hdescent : baseEnd_3050686 < baseStart_3050686 := by decide
  rcases family_descends (prefixWord ++ tailWord_3050686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3050689 : List Nat := [1, 2, 6, 1, 1, 1, 4, 1, 1, 5]
def baseStart_3050689 : Nat := 118140960795 + 3050689 * 2 ^ 59
def prefixEnd_3050689 : Nat := 4983230072969 + 3 ^ 40 * 3050689 * 2
def baseEnd_3050689 : Nat := 522156594794706632985881

theorem tailTrace_3050689 : CollatzResearch.WordTrace tailWord_3050689 prefixEnd_3050689 522156594794706632985881 := by
  unfold tailWord_3050689
  simp only [CollatzResearch.WordTrace]
  refine ⟨111267768844882244046091121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74178512563254829364060747 111267768844882244046091121)
  ·
    refine ⟨83450826633661683034568341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111267768844882244046091121 83450826633661683034568341)
    ·
      refine ⟨3911757498452891392245391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 83450826633661683034568341 3911757498452891392245391)
      ·
        refine ⟨5867636247679337088368087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3911757498452891392245391 5867636247679337088368087)
        ·
          refine ⟨8801454371519005632552131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5867636247679337088368087 8801454371519005632552131)
          ·
            refine ⟨13202181557278508448828197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8801454371519005632552131 13202181557278508448828197)
            ·
              refine ⟨2475409041989720334155287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13202181557278508448828197 2475409041989720334155287)
              ·
                refine ⟨3713113562984580501232931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2475409041989720334155287 3713113562984580501232931)
                ·
                  refine ⟨5569670344476870751849397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3713113562984580501232931 5569670344476870751849397)
                  ·
                    refine ⟨522156594794706632985881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5569670344476870751849397 522156594794706632985881)
                    ·
                      rfl

theorem cell23_3050689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 4, 1, 1, 5].length) (baseStart_3050689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3050689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3050689 prefixEnd_3050689 := by exact prefixLift 3050689
  have htrace : WordTrace (prefixWord ++ tailWord_3050689) baseStart_3050689 baseEnd_3050689 := by
    simpa [prefixWord, tailWord_3050689, baseEnd_3050689] using wordTrace_append hprefix tailTrace_3050689
  have hstable : (prefixWord ++ tailWord_3050689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3050689).length < 2 ^ (prefixWord ++ tailWord_3050689).sum := by decide
  have hdescent : baseEnd_3050689 < baseStart_3050689 := by decide
  rcases family_descends (prefixWord ++ tailWord_3050689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3050698 : List Nat := [3, 1, 2, 1, 3, 3, 10]
def baseStart_3050698 : Nat := 118140960795 + 3050698 * 2 ^ 59
def prefixEnd_3050698 : Nat := 4983230072969 + 3 ^ 40 * 3050698 * 2
def baseEnd_3050698 : Nat := 19339190193950745231421

theorem tailTrace_3050698 : CollatzResearch.WordTrace tailWord_3050698 prefixEnd_3050698 19339190193950745231421 := by
  unfold tailWord_3050698
  simp only [CollatzResearch.WordTrace]
  refine ⟨27817024275462409645792187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74178731401233092388779165 27817024275462409645792187)
  ·
    refine ⟨41725536413193614468688281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27817024275462409645792187 41725536413193614468688281)
    ·
      refine ⟨31294152309895210851516211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41725536413193614468688281 31294152309895210851516211)
      ·
        refine ⟨46941228464842816277274317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31294152309895210851516211 46941228464842816277274317)
        ·
          refine ⟨17602960674316056103977869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46941228464842816277274317 17602960674316056103977869)
          ·
            refine ⟨6601110252868521038991701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17602960674316056103977869 6601110252868521038991701)
            ·
              refine ⟨19339190193950745231421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 6601110252868521038991701 19339190193950745231421)
              ·
                rfl

theorem cell23_3050698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 10].length) (baseStart_3050698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3050698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3050698 prefixEnd_3050698 := by exact prefixLift 3050698
  have htrace : WordTrace (prefixWord ++ tailWord_3050698) baseStart_3050698 baseEnd_3050698 := by
    simpa [prefixWord, tailWord_3050698, baseEnd_3050698] using wordTrace_append hprefix tailTrace_3050698
  have hstable : (prefixWord ++ tailWord_3050698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3050698).length < 2 ^ (prefixWord ++ tailWord_3050698).sum := by decide
  have hdescent : baseEnd_3050698 < baseStart_3050698 := by decide
  rcases family_descends (prefixWord ++ tailWord_3050698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3050702 : List Nat := [4, 1, 1, 1, 5, 1, 1, 1, 4, 4]
def baseStart_3050702 : Nat := 118140960795 + 3050702 * 2 ^ 59
def prefixEnd_3050702 : Nat := 4983230072969 + 3 ^ 40 * 3050702 * 2
def baseEnd_3050702 : Nat := 522158819877542782698361

theorem tailTrace_3050702 : CollatzResearch.WordTrace tailWord_3050702 prefixEnd_3050702 522158819877542782698361 := by
  unfold tailWord_3050702
  simp only [CollatzResearch.WordTrace]
  refine ⟨13908530374229393408289295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74178828662556764844209573 13908530374229393408289295)
  ·
    refine ⟨20862795561344090112433943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13908530374229393408289295 20862795561344090112433943)
    ·
      refine ⟨31294193342016135168650915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20862795561344090112433943 31294193342016135168650915)
      ·
        refine ⟨46941290013024202752976373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31294193342016135168650915 46941290013024202752976373)
        ·
          refine ⟨4400745938721019008091535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 46941290013024202752976373 4400745938721019008091535)
          ·
            refine ⟨6601118908081528512137303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4400745938721019008091535 6601118908081528512137303)
            ·
              refine ⟨9901678362122292768205955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6601118908081528512137303 9901678362122292768205955)
              ·
                refine ⟨14852517543183439152308933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9901678362122292768205955 14852517543183439152308933)
                ·
                  refine ⟨2784847039346894841057925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14852517543183439152308933 2784847039346894841057925)
                  ·
                    refine ⟨522158819877542782698361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2784847039346894841057925 522158819877542782698361)
                    ·
                      rfl

theorem cell23_3050702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 1, 1, 4, 4].length) (baseStart_3050702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3050702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3050702 prefixEnd_3050702 := by exact prefixLift 3050702
  have htrace : WordTrace (prefixWord ++ tailWord_3050702) baseStart_3050702 baseEnd_3050702 := by
    simpa [prefixWord, tailWord_3050702, baseEnd_3050702] using wordTrace_append hprefix tailTrace_3050702
  have hstable : (prefixWord ++ tailWord_3050702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3050702).length < 2 ^ (prefixWord ++ tailWord_3050702).sum := by decide
  have hdescent : baseEnd_3050702 < baseStart_3050702 := by decide
  rcases family_descends (prefixWord ++ tailWord_3050702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3050709 : List Nat := [1, 3, 2, 4, 1, 1, 1, 3, 3, 2, 2]
def baseStart_3050709 : Nat := 118140960795 + 3050709 * 2 ^ 59
def prefixEnd_3050709 : Nat := 4983230072969 + 3 ^ 40 * 3050709 * 2
def baseEnd_3050709 : Nat := 1566480053997209820707551

theorem tailTrace_3050709 : CollatzResearch.WordTrace tailWord_3050709 prefixEnd_3050709 1566480053997209820707551 := by
  unfold tailWord_3050709
  simp only [CollatzResearch.WordTrace]
  refine ⟨111268498304809787461819181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74178998869873191641212787 111268498304809787461819181)
  ·
    refine ⟨41725686864303670298182193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111268498304809787461819181 41725686864303670298182193)
    ·
      refine ⟨31294265148227752723636645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41725686864303670298182193 31294265148227752723636645)
      ·
        refine ⟨5867674715292703635681871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31294265148227752723636645 5867674715292703635681871)
        ·
          refine ⟨8801512072939055453522807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5867674715292703635681871 8801512072939055453522807)
          ·
            refine ⟨13202268109408583180284211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8801512072939055453522807 13202268109408583180284211)
            ·
              refine ⟨19803402164112874770426317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13202268109408583180284211 19803402164112874770426317)
              ·
                refine ⟨7426275811542328038909869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19803402164112874770426317 7426275811542328038909869)
                ·
                  refine ⟨2784853429328373014591201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7426275811542328038909869 2784853429328373014591201)
                  ·
                    refine ⟨2088640071996279760943401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2784853429328373014591201 2088640071996279760943401)
                    ·
                      refine ⟨1566480053997209820707551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2088640071996279760943401 1566480053997209820707551)
                      ·
                        rfl

theorem cell23_3050709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 3, 3, 2, 2].length) (baseStart_3050709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3050709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3050709 prefixEnd_3050709 := by exact prefixLift 3050709
  have htrace : WordTrace (prefixWord ++ tailWord_3050709) baseStart_3050709 baseEnd_3050709 := by
    simpa [prefixWord, tailWord_3050709, baseEnd_3050709] using wordTrace_append hprefix tailTrace_3050709
  have hstable : (prefixWord ++ tailWord_3050709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3050709).length < 2 ^ (prefixWord ++ tailWord_3050709).sum := by decide
  have hdescent : baseEnd_3050709 < baseStart_3050709 := by decide
  rcases family_descends (prefixWord ++ tailWord_3050709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3050770 : List Nat := [3, 2, 4, 2, 2, 1, 2, 1, 2, 4]
def baseStart_3050770 : Nat := 118140960795 + 3050770 * 2 ^ 59
def prefixEnd_3050770 : Nat := 4983230072969 + 3 ^ 40 * 3050770 * 2
def baseEnd_3050770 : Nat := 522170458772378027348257

theorem tailTrace_3050770 : CollatzResearch.WordTrace tailWord_3050770 prefixEnd_3050770 522170458772378027348257 := by
  unfold tailWord_3050770
  simp only [CollatzResearch.WordTrace]
  refine ⟨27817680789397198719947441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74180482105059196586526509 27817680789397198719947441)
  ·
    refine ⟨20863260592047899039960581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27817680789397198719947441 20863260592047899039960581)
    ·
      refine ⟨3911861361008981069992609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20863260592047899039960581 3911861361008981069992609)
      ·
        refine ⟨2933896020756735802494457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3911861361008981069992609 2933896020756735802494457)
        ·
          refine ⟨2200422015567551851870843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2933896020756735802494457 2200422015567551851870843)
          ·
            refine ⟨3300633023351327777806265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2200422015567551851870843 3300633023351327777806265)
            ·
              refine ⟨2475474767513495833354699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3300633023351327777806265 2475474767513495833354699)
              ·
                refine ⟨3713212151270243750032049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2475474767513495833354699 3713212151270243750032049)
                ·
                  refine ⟨2784909113452682812524037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3713212151270243750032049 2784909113452682812524037)
                  ·
                    refine ⟨522170458772378027348257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2784909113452682812524037 522170458772378027348257)
                    ·
                      rfl

theorem cell23_3050770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 1, 2, 1, 2, 4].length) (baseStart_3050770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3050770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3050770 prefixEnd_3050770 := by exact prefixLift 3050770
  have htrace : WordTrace (prefixWord ++ tailWord_3050770) baseStart_3050770 baseEnd_3050770 := by
    simpa [prefixWord, tailWord_3050770, baseEnd_3050770] using wordTrace_append hprefix tailTrace_3050770
  have hstable : (prefixWord ++ tailWord_3050770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3050770).length < 2 ^ (prefixWord ++ tailWord_3050770).sum := by decide
  have hdescent : baseEnd_3050770 < baseStart_3050770 := by decide
  rcases family_descends (prefixWord ++ tailWord_3050770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3050776 : List Nat := [2, 1, 2, 3, 1, 5, 2, 1, 2, 1, 3]
def baseStart_3050776 : Nat := 118140960795 + 3050776 * 2 ^ 59
def prefixEnd_3050776 : Nat := 4983230072969 + 3 ^ 40 * 3050776 * 2
def baseEnd_3050776 : Nat := 1566514457201061058569743

theorem tailTrace_3050776 : CollatzResearch.WordTrace tailWord_3050776 prefixEnd_3050776 1566514457201061058569743 := by
  unfold tailWord_3050776
  simp only [CollatzResearch.WordTrace]
  refine ⟨55635470997783528952254091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74180627997044705269672121 55635470997783528952254091)
  ·
    refine ⟨83453206496675293428381137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55635470997783528952254091 83453206496675293428381137)
    ·
      refine ⟨62589904872506470071285853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83453206496675293428381137 62589904872506470071285853)
      ·
        refine ⟨23471214327189926276732195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62589904872506470071285853 23471214327189926276732195)
        ·
          refine ⟨35206821490784889415098293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23471214327189926276732195 35206821490784889415098293)
          ·
            refine ⟨3300639514761083382665465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 35206821490784889415098293 3300639514761083382665465)
            ·
              refine ⟨2475479636070812536999099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3300639514761083382665465 2475479636070812536999099)
              ·
                refine ⟨3713219454106218805498649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2475479636070812536999099 3713219454106218805498649)
                ·
                  refine ⟨2784914590579664104123987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3713219454106218805498649 2784914590579664104123987)
                  ·
                    refine ⟨4177371885869496156185981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2784914590579664104123987 4177371885869496156185981)
                    ·
                      refine ⟨1566514457201061058569743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4177371885869496156185981 1566514457201061058569743)
                      ·
                        rfl

theorem cell23_3050776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 5, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 5, 2, 1, 2, 1, 3].length) (baseStart_3050776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3050776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3050776 prefixEnd_3050776 := by exact prefixLift 3050776
  have htrace : WordTrace (prefixWord ++ tailWord_3050776) baseStart_3050776 baseEnd_3050776 := by
    simpa [prefixWord, tailWord_3050776, baseEnd_3050776] using wordTrace_append hprefix tailTrace_3050776
  have hstable : (prefixWord ++ tailWord_3050776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3050776).length < 2 ^ (prefixWord ++ tailWord_3050776).sum := by decide
  have hdescent : baseEnd_3050776 < baseStart_3050776 := by decide
  rcases family_descends (prefixWord ++ tailWord_3050776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3050852 : List Nat := [2, 3, 1, 1, 3, 2, 3, 1, 2, 5]
def baseStart_3050852 : Nat := 118140960795 + 3050852 * 2 ^ 59
def prefixEnd_3050852 : Nat := 4983230072969 + 3 ^ 40 * 3050852 * 2
def baseEnd_3050852 : Nat := 522184493910267587073131

theorem tailTrace_3050852 : CollatzResearch.WordTrace tailWord_3050852 prefixEnd_3050852 522184493910267587073131 := by
  unfold tailWord_3050852
  simp only [CollatzResearch.WordTrace]
  refine ⟨55636856971645861442137405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74182475962194481922849873 55636856971645861442137405)
  ·
    refine ⟨20863821364367198040801527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55636856971645861442137405 20863821364367198040801527)
    ·
      refine ⟨31295732046550797061202291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20863821364367198040801527 31295732046550797061202291)
      ·
        refine ⟨46943598069826195591803437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31295732046550797061202291 46943598069826195591803437)
        ·
          refine ⟨17603849276184823346926289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46943598069826195591803437 17603849276184823346926289)
          ·
            refine ⟨13202886957138617510194717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17603849276184823346926289 13202886957138617510194717)
            ·
              refine ⟨4951082608926981566323019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13202886957138617510194717 4951082608926981566323019)
              ·
                refine ⟨7426623913390472349484529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4951082608926981566323019 7426623913390472349484529)
                ·
                  refine ⟨5569967935042854262113397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7426623913390472349484529 5569967935042854262113397)
                  ·
                    refine ⟨522184493910267587073131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5569967935042854262113397 522184493910267587073131)
                    ·
                      rfl

theorem cell23_3050852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 3, 1, 2, 5].length) (baseStart_3050852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3050852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3050852 prefixEnd_3050852 := by exact prefixLift 3050852
  have htrace : WordTrace (prefixWord ++ tailWord_3050852) baseStart_3050852 baseEnd_3050852 := by
    simpa [prefixWord, tailWord_3050852, baseEnd_3050852] using wordTrace_append hprefix tailTrace_3050852
  have hstable : (prefixWord ++ tailWord_3050852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3050852).length < 2 ^ (prefixWord ++ tailWord_3050852).sum := by decide
  have hdescent : baseEnd_3050852 < baseStart_3050852 := by decide
  rcases family_descends (prefixWord ++ tailWord_3050852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3050933 : List Nat := [1, 3, 3, 2, 2, 2, 3, 2, 1, 4]
def baseStart_3050933 : Nat := 118140960795 + 3050933 * 2 ^ 59
def prefixEnd_3050933 : Nat := 4983230072969 + 3 ^ 40 * 3050933 * 2
def baseEnd_3050933 : Nat := 522198357887938981435507

theorem tailTrace_3050933 : CollatzResearch.WordTrace tailWord_3050933 prefixEnd_3050933 522198357887938981435507 := by
  unfold tailWord_3050933
  simp only [CollatzResearch.WordTrace]
  refine ⟨111276668255998273717973453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74184445503998849145315635 111276668255998273717973453)
  ·
    refine ⟨41728750595999352644240045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111276668255998273717973453 41728750595999352644240045)
    ·
      refine ⟨15648281473499757241590017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41728750595999352644240045 15648281473499757241590017)
      ·
        refine ⟨11736211105124817931192513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15648281473499757241590017 11736211105124817931192513)
        ·
          refine ⟨8802158328843613448394385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11736211105124817931192513 8802158328843613448394385)
          ·
            refine ⟨6601618746632710086295789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8802158328843613448394385 6601618746632710086295789)
            ·
              refine ⟨2475607029987266282360921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6601618746632710086295789 2475607029987266282360921)
              ·
                refine ⟨1856705272490449711770691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2475607029987266282360921 1856705272490449711770691)
                ·
                  refine ⟨2785057908735674567656037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1856705272490449711770691 2785057908735674567656037)
                  ·
                    refine ⟨522198357887938981435507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2785057908735674567656037 522198357887938981435507)
                    ·
                      rfl

theorem cell23_3050933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 3, 2, 1, 4].length) (baseStart_3050933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3050933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3050933 prefixEnd_3050933 := by exact prefixLift 3050933
  have htrace : WordTrace (prefixWord ++ tailWord_3050933) baseStart_3050933 baseEnd_3050933 := by
    simpa [prefixWord, tailWord_3050933, baseEnd_3050933] using wordTrace_append hprefix tailTrace_3050933
  have hstable : (prefixWord ++ tailWord_3050933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3050933).length < 2 ^ (prefixWord ++ tailWord_3050933).sum := by decide
  have hdescent : baseEnd_3050933 < baseStart_3050933 := by decide
  rcases family_descends (prefixWord ++ tailWord_3050933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3050942 : List Nat := [4, 2, 1, 1, 1, 1, 1, 4, 3, 5]
def baseStart_3050942 : Nat := 118140960795 + 3050942 * 2 ^ 59
def prefixEnd_3050942 : Nat := 4983230072969 + 3 ^ 40 * 3050942 * 2
def baseEnd_3050942 : Nat := 522199898329902469697993

theorem tailTrace_3050942 : CollatzResearch.WordTrace tailWord_3050942 prefixEnd_3050942 522199898329902469697993 := by
  unfold tailWord_3050942
  simp only [CollatzResearch.WordTrace]
  refine ⟨13909624564120708531881385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74184664341977112170034053 13909624564120708531881385)
  ·
    refine ⟨10432218423090531398911039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13909624564120708531881385 10432218423090531398911039)
    ·
      refine ⟨15648327634635797098366559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10432218423090531398911039 15648327634635797098366559)
      ·
        refine ⟨23472491451953695647549839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15648327634635797098366559 23472491451953695647549839)
        ·
          refine ⟨35208737177930543471324759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23472491451953695647549839 35208737177930543471324759)
          ·
            refine ⟨52813105766895815206987139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35208737177930543471324759 52813105766895815206987139)
            ·
              refine ⟨79219658650343722810480709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52813105766895815206987139 79219658650343722810480709)
              ·
                refine ⟨14853685996939448026965133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 79219658650343722810480709 14853685996939448026965133)
                ·
                  refine ⟨5570132248852293010111925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14853685996939448026965133 5570132248852293010111925)
                  ·
                    refine ⟨522199898329902469697993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5570132248852293010111925 522199898329902469697993)
                    ·
                      rfl

theorem cell23_3050942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 4, 3, 5].length) (baseStart_3050942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3050942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3050942 prefixEnd_3050942 := by exact prefixLift 3050942
  have htrace : WordTrace (prefixWord ++ tailWord_3050942) baseStart_3050942 baseEnd_3050942 := by
    simpa [prefixWord, tailWord_3050942, baseEnd_3050942] using wordTrace_append hprefix tailTrace_3050942
  have hstable : (prefixWord ++ tailWord_3050942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3050942).length < 2 ^ (prefixWord ++ tailWord_3050942).sum := by decide
  have hdescent : baseEnd_3050942 < baseStart_3050942 := by decide
  rcases family_descends (prefixWord ++ tailWord_3050942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3050995 : List Nat := [1, 1, 1, 2, 2, 2, 2, 1, 2, 2, 7]
def baseStart_3050995 : Nat := 118140960795 + 3050995 * 2 ^ 59
def prefixEnd_3050995 : Nat := 4983230072969 + 3 ^ 40 * 3050995 * 2
def baseEnd_3050995 : Nat := 1566626909464395701731235

theorem tailTrace_3050995 : CollatzResearch.WordTrace tailWord_3050995 prefixEnd_3050995 1566626909464395701731235 := by
  unfold tailWord_3050995
  simp only [CollatzResearch.WordTrace]
  refine ⟨111278929581773658306730439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74185953054515772204486959 111278929581773658306730439)
  ·
    refine ⟨166918394372660487460095659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111278929581773658306730439 166918394372660487460095659)
    ·
      refine ⟨250377591558990731190143489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166918394372660487460095659 250377591558990731190143489)
      ·
        refine ⟨187783193669243048392607617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 250377591558990731190143489 187783193669243048392607617)
        ·
          refine ⟨140837395251932286294455713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 187783193669243048392607617 140837395251932286294455713)
          ·
            refine ⟨105628046438949214720841785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 140837395251932286294455713 105628046438949214720841785)
            ·
              refine ⟨79221034829211911040631339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 105628046438949214720841785 79221034829211911040631339)
              ·
                refine ⟨118831552243817866560947009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79221034829211911040631339 118831552243817866560947009)
                ·
                  refine ⟨89123664182863399920710257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 118831552243817866560947009 89123664182863399920710257)
                  ·
                    refine ⟨66842748137147549940532693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 89123664182863399920710257 66842748137147549940532693)
                    ·
                      refine ⟨1566626909464395701731235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 66842748137147549940532693 1566626909464395701731235)
                      ·
                        rfl

theorem cell23_3050995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 1, 2, 2, 7].length) (baseStart_3050995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3050995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3050995 prefixEnd_3050995 := by exact prefixLift 3050995
  have htrace : WordTrace (prefixWord ++ tailWord_3050995) baseStart_3050995 baseEnd_3050995 := by
    simpa [prefixWord, tailWord_3050995, baseEnd_3050995] using wordTrace_append hprefix tailTrace_3050995
  have hstable : (prefixWord ++ tailWord_3050995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3050995).length < 2 ^ (prefixWord ++ tailWord_3050995).sum := by decide
  have hdescent : baseEnd_3050995 < baseStart_3050995 := by decide
  rcases family_descends (prefixWord ++ tailWord_3050995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3051019 : List Nat := [1, 1, 1, 1, 8, 1, 3, 7]
def baseStart_3051019 : Nat := 118140960795 + 3051019 * 2 ^ 59
def prefixEnd_3051019 : Nat := 4983230072969 + 3 ^ 40 * 3051019 * 2
def baseEnd_3051019 : Nat := 58023675296300133623375

theorem tailTrace_3051019 : CollatzResearch.WordTrace tailWord_3051019 prefixEnd_3051019 58023675296300133623375 := by
  unfold tailWord_3051019
  simp only [CollatzResearch.WordTrace]
  refine ⟨111279804933686710405604111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74186536622457806937069407 111279804933686710405604111)
  ·
    refine ⟨166919707400530065608406167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111279804933686710405604111 166919707400530065608406167)
    ·
      refine ⟨250379561100795098412609251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166919707400530065608406167 250379561100795098412609251)
      ·
        refine ⟨375569341651192647618913877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 250379561100795098412609251 375569341651192647618913877)
        ·
          refine ⟨4401203222474913839284147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 375569341651192647618913877 4401203222474913839284147)
          ·
            refine ⟨6601804833712370758926221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4401203222474913839284147 6601804833712370758926221)
            ·
              refine ⟨2475676812642139034597333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6601804833712370758926221 2475676812642139034597333)
              ·
                refine ⟨58023675296300133623375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2475676812642139034597333 58023675296300133623375)
                ·
                  rfl

theorem cell23_3051019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 3, 7].length) (baseStart_3051019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3051019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3051019 prefixEnd_3051019 := by exact prefixLift 3051019
  have htrace : WordTrace (prefixWord ++ tailWord_3051019) baseStart_3051019 baseEnd_3051019 := by
    simpa [prefixWord, tailWord_3051019, baseEnd_3051019] using wordTrace_append hprefix tailTrace_3051019
  have hstable : (prefixWord ++ tailWord_3051019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3051019).length < 2 ^ (prefixWord ++ tailWord_3051019).sum := by decide
  have hdescent : baseEnd_3051019 < baseStart_3051019 := by decide
  rcases family_descends (prefixWord ++ tailWord_3051019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3051029 : List Nat := [1, 3, 2, 1, 3, 2, 2, 2, 1, 3, 3]
def baseStart_3051029 : Nat := 118140960795 + 3051029 * 2 ^ 59
def prefixEnd_3051029 : Nat := 4983230072969 + 3 ^ 40 * 3051029 * 2
def baseEnd_3051029 : Nat := 1566644367806648568706079

theorem tailTrace_3051029 : CollatzResearch.WordTrace tailWord_3051029 prefixEnd_3051029 1566644367806648568706079 := by
  unfold tailWord_3051029
  simp only [CollatzResearch.WordTrace]
  refine ⟨111280169663650482113468141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74186779775766988075645427 111280169663650482113468141)
  ·
    refine ⟨41730063623868930792550553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111280169663650482113468141 41730063623868930792550553)
    ·
      refine ⟨31297547717901698094412915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41730063623868930792550553 31297547717901698094412915)
      ·
        refine ⟨46946321576852547141619373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31297547717901698094412915 46946321576852547141619373)
        ·
          refine ⟨17604870591319705178107265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46946321576852547141619373 17604870591319705178107265)
          ·
            refine ⟨13203652943489778883580449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17604870591319705178107265 13203652943489778883580449)
            ·
              refine ⟨9902739707617334162685337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13203652943489778883580449 9902739707617334162685337)
              ·
                refine ⟨7427054780713000622014003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9902739707617334162685337 7427054780713000622014003)
                ·
                  refine ⟨11140582171069500933021005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7427054780713000622014003 11140582171069500933021005)
                  ·
                    refine ⟨4177718314151062849882877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11140582171069500933021005 4177718314151062849882877)
                    ·
                      refine ⟨1566644367806648568706079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4177718314151062849882877 1566644367806648568706079)
                      ·
                        rfl

theorem cell23_3051029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 2, 2, 1, 3, 3].length) (baseStart_3051029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3051029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3051029 prefixEnd_3051029 := by exact prefixLift 3051029
  have htrace : WordTrace (prefixWord ++ tailWord_3051029) baseStart_3051029 baseEnd_3051029 := by
    simpa [prefixWord, tailWord_3051029, baseEnd_3051029] using wordTrace_append hprefix tailTrace_3051029
  have hstable : (prefixWord ++ tailWord_3051029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3051029).length < 2 ^ (prefixWord ++ tailWord_3051029).sum := by decide
  have hdescent : baseEnd_3051029 < baseStart_3051029 := by decide
  rcases family_descends (prefixWord ++ tailWord_3051029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3051063 : List Nat := [1, 1, 3, 1, 2, 5, 3, 1, 2, 1, 3]
def baseStart_3051063 : Nat := 118140960795 + 3051063 * 2 ^ 59
def prefixEnd_3051063 : Nat := 4983230072969 + 3 ^ 40 * 3051063 * 2
def baseEnd_3051063 : Nat := 1566661826148901435680923

theorem tailTrace_3051063 : CollatzResearch.WordTrace tailWord_3051063 prefixEnd_3051063 1566661826148901435680923 := by
  unfold tailWord_3051063
  simp only [CollatzResearch.WordTrace]
  refine ⟨111281409745527305920205843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74187606497018203946803895 111281409745527305920205843)
  ·
    refine ⟨166922114618290958880308765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111281409745527305920205843 166922114618290958880308765)
    ·
      refine ⟨62595792981859109580115787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 166922114618290958880308765 62595792981859109580115787)
      ·
        refine ⟨93893689472788664370173681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62595792981859109580115787 93893689472788664370173681)
        ·
          refine ⟨70420267104591498277630261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93893689472788664370173681 70420267104591498277630261)
          ·
            refine ⟨6601900041055452963527837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 70420267104591498277630261 6601900041055452963527837)
            ·
              refine ⟨2475712515395794861322939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6601900041055452963527837 2475712515395794861322939)
              ·
                refine ⟨3713568773093692291984409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2475712515395794861322939 3713568773093692291984409)
                ·
                  refine ⟨2785176579820269218988307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3713568773093692291984409 2785176579820269218988307)
                  ·
                    refine ⟨4177764869730403828482461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2785176579820269218988307 4177764869730403828482461)
                    ·
                      refine ⟨1566661826148901435680923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4177764869730403828482461 1566661826148901435680923)
                      ·
                        rfl

theorem cell23_3051063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 3, 1, 2, 1, 3].length) (baseStart_3051063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3051063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3051063 prefixEnd_3051063 := by exact prefixLift 3051063
  have htrace : WordTrace (prefixWord ++ tailWord_3051063) baseStart_3051063 baseEnd_3051063 := by
    simpa [prefixWord, tailWord_3051063, baseEnd_3051063] using wordTrace_append hprefix tailTrace_3051063
  have hstable : (prefixWord ++ tailWord_3051063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3051063).length < 2 ^ (prefixWord ++ tailWord_3051063).sum := by decide
  have hdescent : baseEnd_3051063 < baseStart_3051063 := by decide
  rcases family_descends (prefixWord ++ tailWord_3051063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3051072 : List Nat := [2, 1, 1, 2, 2, 2, 1, 4, 2, 1, 5]
def baseStart_3051072 : Nat := 118140960795 + 3051072 * 2 ^ 59
def prefixEnd_3051072 : Nat := 4983230072969 + 3 ^ 40 * 3051072 * 2
def baseEnd_3051072 : Nat := 1566666447474791900468381

theorem tailTrace_3051072 : CollatzResearch.WordTrace tailWord_3051072 prefixEnd_3051072 1566666447474791900468381 := by
  unfold tailWord_3051072
  simp only [CollatzResearch.WordTrace]
  refine ⟨55640869001247350228641735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74187825334996466971522313 55640869001247350228641735)
  ·
    refine ⟨83461303501871025342962603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55640869001247350228641735 83461303501871025342962603)
    ·
      refine ⟨125191955252806538014443905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83461303501871025342962603 125191955252806538014443905)
      ·
        refine ⟨93893966439604903510832929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125191955252806538014443905 93893966439604903510832929)
        ·
          refine ⟨70420474829703677633124697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93893966439604903510832929 70420474829703677633124697)
          ·
            refine ⟨52815356122277758224843523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70420474829703677633124697 52815356122277758224843523)
            ·
              refine ⟨79223034183416637337265285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52815356122277758224843523 79223034183416637337265285)
              ·
                refine ⟨14854318909390619500737241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 79223034183416637337265285 14854318909390619500737241)
                ·
                  refine ⟨11140739182042964625552931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14854318909390619500737241 11140739182042964625552931)
                  ·
                    refine ⟨16711108773064446938329397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11140739182042964625552931 16711108773064446938329397)
                    ·
                      refine ⟨1566666447474791900468381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16711108773064446938329397 1566666447474791900468381)
                      ·
                        rfl

theorem cell23_3051072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 4, 2, 1, 5].length) (baseStart_3051072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3051072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3051072 prefixEnd_3051072 := by exact prefixLift 3051072
  have htrace : WordTrace (prefixWord ++ tailWord_3051072) baseStart_3051072 baseEnd_3051072 := by
    simpa [prefixWord, tailWord_3051072, baseEnd_3051072] using wordTrace_append hprefix tailTrace_3051072
  have hstable : (prefixWord ++ tailWord_3051072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3051072).length < 2 ^ (prefixWord ++ tailWord_3051072).sum := by decide
  have hdescent : baseEnd_3051072 < baseStart_3051072 := by decide
  rcases family_descends (prefixWord ++ tailWord_3051072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3051073 : List Nat := [1, 2, 5, 1, 1, 1, 4, 2, 1, 3, 2]
def baseStart_3051073 : Nat := 118140960795 + 3051073 * 2 ^ 59
def prefixEnd_3051073 : Nat := 4983230072969 + 3 ^ 40 * 3051073 * 2
def baseEnd_3051073 : Nat := 1566666960955446396555877

theorem tailTrace_3051073 : CollatzResearch.WordTrace tailWord_3051073 prefixEnd_3051073 1566666960955446396555877 := by
  unfold tailWord_3051073
  simp only [CollatzResearch.WordTrace]
  refine ⟨111281774475491077628069873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74187849650327385085379915 111281774475491077628069873)
  ·
    refine ⟨83461330856618308221052405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111281774475491077628069873 83461330856618308221052405)
    ·
      refine ⟨7824499767807966395723663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 83461330856618308221052405 7824499767807966395723663)
      ·
        refine ⟨11736749651711949593585495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7824499767807966395723663 11736749651711949593585495)
        ·
          refine ⟨17605124477567924390378243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11736749651711949593585495 17605124477567924390378243)
          ·
            refine ⟨26407686716351886585567365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17605124477567924390378243 26407686716351886585567365)
            ·
              refine ⟨4951441259315978734793881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26407686716351886585567365 4951441259315978734793881)
              ·
                refine ⟨3713580944486984051095411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4951441259315978734793881 3713580944486984051095411)
                ·
                  refine ⟨5570371416730476076643117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3713580944486984051095411 5570371416730476076643117)
                  ·
                    refine ⟨2088889281273928528741169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5570371416730476076643117 2088889281273928528741169)
                    ·
                      refine ⟨1566666960955446396555877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2088889281273928528741169 1566666960955446396555877)
                      ·
                        rfl

theorem cell23_3051073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 4, 2, 1, 3, 2].length) (baseStart_3051073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3051073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3051073 prefixEnd_3051073 := by exact prefixLift 3051073
  have htrace : WordTrace (prefixWord ++ tailWord_3051073) baseStart_3051073 baseEnd_3051073 := by
    simpa [prefixWord, tailWord_3051073, baseEnd_3051073] using wordTrace_append hprefix tailTrace_3051073
  have hstable : (prefixWord ++ tailWord_3051073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3051073).length < 2 ^ (prefixWord ++ tailWord_3051073).sum := by decide
  have hdescent : baseEnd_3051073 < baseStart_3051073 := by decide
  rcases family_descends (prefixWord ++ tailWord_3051073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3051109 : List Nat := [1, 3, 1, 3, 3, 1, 3, 1, 7]
def baseStart_3051109 : Nat := 118140960795 + 3051109 * 2 ^ 59
def prefixEnd_3051109 : Nat := 4983230072969 + 3 ^ 40 * 3051109 * 2
def baseEnd_3051109 : Nat := 174076160695445361745079

theorem tailTrace_3051109 : CollatzResearch.WordTrace tailWord_3051109 prefixEnd_3051109 174076160695445361745079 := by
  unfold tailWord_3051109
  simp only [CollatzResearch.WordTrace]
  refine ⟨111283087503360655776380381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74188725002240437184253587 111283087503360655776380381)
  ·
    refine ⟨41731157813760245916142643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111283087503360655776380381 41731157813760245916142643)
    ·
      refine ⟨62596736720640368874213965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41731157813760245916142643 62596736720640368874213965)
      ·
        refine ⟨23473776270240138327830237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62596736720640368874213965 23473776270240138327830237)
        ·
          refine ⟨8802666101340051872936339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23473776270240138327830237 8802666101340051872936339)
          ·
            refine ⟨13203999152010077809404509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8802666101340051872936339 13203999152010077809404509)
            ·
              refine ⟨4951499682003779178526691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13203999152010077809404509 4951499682003779178526691)
              ·
                refine ⟨7427249523005668767790037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4951499682003779178526691 7427249523005668767790037)
                ·
                  refine ⟨174076160695445361745079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7427249523005668767790037 174076160695445361745079)
                  ·
                    rfl

theorem cell23_3051109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 3, 1, 7].length) (baseStart_3051109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3051109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3051109 prefixEnd_3051109 := by exact prefixLift 3051109
  have htrace : WordTrace (prefixWord ++ tailWord_3051109) baseStart_3051109 baseEnd_3051109 := by
    simpa [prefixWord, tailWord_3051109, baseEnd_3051109] using wordTrace_append hprefix tailTrace_3051109
  have hstable : (prefixWord ++ tailWord_3051109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3051109).length < 2 ^ (prefixWord ++ tailWord_3051109).sum := by decide
  have hdescent : baseEnd_3051109 < baseStart_3051109 := by decide
  rcases family_descends (prefixWord ++ tailWord_3051109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3051120 : List Nat := [2, 1, 1, 1, 6, 1, 4, 1, 2, 2, 2]
def baseStart_3051120 : Nat := 118140960795 + 3051120 * 2 ^ 59
def prefixEnd_3051120 : Nat := 4983230072969 + 3 ^ 40 * 3051120 * 2
def baseEnd_3051120 : Nat := 1566691094546207712668161

theorem tailTrace_3051120 : CollatzResearch.WordTrace tailWord_3051120 prefixEnd_3051120 1566691094546207712668161 := by
  unfold tailWord_3051120
  simp only [CollatzResearch.WordTrace]
  refine ⟨55641744353160402327515407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74188992470880536436687209 55641744353160402327515407)
  ·
    refine ⟨83462616529740603491273111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55641744353160402327515407 83462616529740603491273111)
    ·
      refine ⟨125193924794610905236909667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83462616529740603491273111 125193924794610905236909667)
      ·
        refine ⟨187790887191916357855364501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125193924794610905236909667 187790887191916357855364501)
        ·
          refine ⟨8802697837121079274470211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 187790887191916357855364501 8802697837121079274470211)
          ·
            refine ⟨13204046755681618911705317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8802697837121079274470211 13204046755681618911705317)
            ·
              refine ⟨2475758766690303545944747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13204046755681618911705317 2475758766690303545944747)
              ·
                refine ⟨3713638150035455318917121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2475758766690303545944747 3713638150035455318917121)
                ·
                  refine ⟨2785228612526591489187841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3713638150035455318917121 2785228612526591489187841)
                  ·
                    refine ⟨2088921459394943616890881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2785228612526591489187841 2088921459394943616890881)
                    ·
                      refine ⟨1566691094546207712668161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2088921459394943616890881 1566691094546207712668161)
                      ·
                        rfl

theorem cell23_3051120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 4, 1, 2, 2, 2].length) (baseStart_3051120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3051120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3051120 prefixEnd_3051120 := by exact prefixLift 3051120
  have htrace : WordTrace (prefixWord ++ tailWord_3051120) baseStart_3051120 baseEnd_3051120 := by
    simpa [prefixWord, tailWord_3051120, baseEnd_3051120] using wordTrace_append hprefix tailTrace_3051120
  have hstable : (prefixWord ++ tailWord_3051120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3051120).length < 2 ^ (prefixWord ++ tailWord_3051120).sum := by decide
  have hdescent : baseEnd_3051120 < baseStart_3051120 := by decide
  rcases family_descends (prefixWord ++ tailWord_3051120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3051132 : List Nat := [2, 2, 2, 1, 1, 2, 1, 1, 3, 1, 7]
def baseStart_3051132 : Nat := 118140960795 + 3051132 * 2 ^ 59
def prefixEnd_3051132 : Nat := 4983230072969 + 3 ^ 40 * 3051132 * 2
def baseEnd_3051132 : Nat := 1566697256314061665718105

theorem tailTrace_3051132 : CollatzResearch.WordTrace tailWord_3051132 prefixEnd_3051132 1566697256314061665718105 := by
  unfold tailWord_3051132
  simp only [CollatzResearch.WordTrace]
  refine ⟨55641963191138665352233825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74189284254851553802978433 55641963191138665352233825)
  ·
    refine ⟨41731472393353999014175369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55641963191138665352233825 41731472393353999014175369)
    ·
      refine ⟨31298604295015499260631527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41731472393353999014175369 31298604295015499260631527)
      ·
        refine ⟨46947906442523248890947291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31298604295015499260631527 46947906442523248890947291)
        ·
          refine ⟨70421859663784873336420937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46947906442523248890947291 70421859663784873336420937)
          ·
            refine ⟨52816394747838655002315703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70421859663784873336420937 52816394747838655002315703)
            ·
              refine ⟨79224592121757982503473555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52816394747838655002315703 79224592121757982503473555)
              ·
                refine ⟨118836888182636973755210333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79224592121757982503473555 118836888182636973755210333)
                ·
                  refine ⟨44563833068488865158203875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 118836888182636973755210333 44563833068488865158203875)
                  ·
                    refine ⟨66845749602733297737305813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 44563833068488865158203875 66845749602733297737305813)
                    ·
                      refine ⟨1566697256314061665718105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 66845749602733297737305813 1566697256314061665718105)
                      ·
                        rfl

theorem cell23_3051132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 1, 3, 1, 7].length) (baseStart_3051132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3051132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3051132 prefixEnd_3051132 := by exact prefixLift 3051132
  have htrace : WordTrace (prefixWord ++ tailWord_3051132) baseStart_3051132 baseEnd_3051132 := by
    simpa [prefixWord, tailWord_3051132, baseEnd_3051132] using wordTrace_append hprefix tailTrace_3051132
  have hstable : (prefixWord ++ tailWord_3051132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3051132).length < 2 ^ (prefixWord ++ tailWord_3051132).sum := by decide
  have hdescent : baseEnd_3051132 < baseStart_3051132 := by decide
  rcases family_descends (prefixWord ++ tailWord_3051132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3051166 : List Nat := [4, 3, 1, 1, 1, 2, 2, 1, 1, 2, 5]
def baseStart_3051166 : Nat := 118140960795 + 3051166 * 2 ^ 59
def prefixEnd_3051166 : Nat := 4983230072969 + 3 ^ 40 * 3051166 * 2
def baseEnd_3051166 : Nat := 1566714714656314532692949

theorem tailTrace_3051166 : CollatzResearch.WordTrace tailWord_3051166 prefixEnd_3051166 1566714714656314532692949 := by
  unfold tailWord_3051166
  simp only [CollatzResearch.WordTrace]
  refine ⟨13910645808019269313900669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74190110976102769674136901 13910645808019269313900669)
  ·
    refine ⟨5216492178007225992712751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13910645808019269313900669 5216492178007225992712751)
    ·
      refine ⟨7824738267010838989069127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5216492178007225992712751 7824738267010838989069127)
      ·
        refine ⟨11737107400516258483603691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7824738267010838989069127 11737107400516258483603691)
        ·
          refine ⟨17605661100774387725405537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11737107400516258483603691 17605661100774387725405537)
          ·
            refine ⟨13204245825580790794054153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17605661100774387725405537 13204245825580790794054153)
            ·
              refine ⟨9903184369185593095540615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13204245825580790794054153 9903184369185593095540615)
              ·
                refine ⟨14854776553778389643310923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9903184369185593095540615 14854776553778389643310923)
                ·
                  refine ⟨22282164830667584464966385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14854776553778389643310923 22282164830667584464966385)
                  ·
                    refine ⟨16711623623000688348724789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22282164830667584464966385 16711623623000688348724789)
                    ·
                      refine ⟨1566714714656314532692949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16711623623000688348724789 1566714714656314532692949)
                      ·
                        rfl

theorem cell23_3051166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 2, 1, 1, 2, 5].length) (baseStart_3051166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3051166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3051166 prefixEnd_3051166 := by exact prefixLift 3051166
  have htrace : WordTrace (prefixWord ++ tailWord_3051166) baseStart_3051166 baseEnd_3051166 := by
    simpa [prefixWord, tailWord_3051166, baseEnd_3051166] using wordTrace_append hprefix tailTrace_3051166
  have hstable : (prefixWord ++ tailWord_3051166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3051166).length < 2 ^ (prefixWord ++ tailWord_3051166).sum := by decide
  have hdescent : baseEnd_3051166 < baseStart_3051166 := by decide
  rcases family_descends (prefixWord ++ tailWord_3051166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3051190 : List Nat := [5, 1, 3, 1, 1, 3, 1, 1, 2, 5]
def baseStart_3051190 : Nat := 118140960795 + 3051190 * 2 ^ 59
def prefixEnd_3051190 : Nat := 4983230072969 + 3 ^ 40 * 3051190 * 2
def baseEnd_3051190 : Nat := 522242346064007479597613

theorem tailTrace_3051190 : CollatzResearch.WordTrace tailWord_3051190 prefixEnd_3051190 522242346064007479597613 := by
  unfold tailWord_3051190
  simp only [CollatzResearch.WordTrace]
  refine ⟨6955377613504200413129939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 74190694544044804406719349 6955377613504200413129939)
  ·
    refine ⟨10433066420256300619694909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6955377613504200413129939 10433066420256300619694909)
    ·
      refine ⟨3912399907596112732385591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10433066420256300619694909 3912399907596112732385591)
      ·
        refine ⟨5868599861394169098578387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3912399907596112732385591 5868599861394169098578387)
        ·
          refine ⟨8802899792091253647867581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5868599861394169098578387 8802899792091253647867581)
          ·
            refine ⟨3301087422034220117950343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8802899792091253647867581 3301087422034220117950343)
            ·
              refine ⟨4951631133051330176925515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3301087422034220117950343 4951631133051330176925515)
              ·
                refine ⟨7427446699576995265388273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4951631133051330176925515 7427446699576995265388273)
                ·
                  refine ⟨5570585024682746449041205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7427446699576995265388273 5570585024682746449041205)
                  ·
                    refine ⟨522242346064007479597613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5570585024682746449041205 522242346064007479597613)
                    ·
                      rfl

theorem cell23_3051190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 3, 1, 1, 2, 5].length) (baseStart_3051190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3051190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3051190 prefixEnd_3051190 := by exact prefixLift 3051190
  have htrace : WordTrace (prefixWord ++ tailWord_3051190) baseStart_3051190 baseEnd_3051190 := by
    simpa [prefixWord, tailWord_3051190, baseEnd_3051190] using wordTrace_append hprefix tailTrace_3051190
  have hstable : (prefixWord ++ tailWord_3051190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3051190).length < 2 ^ (prefixWord ++ tailWord_3051190).sum := by decide
  have hdescent : baseEnd_3051190 < baseStart_3051190 := by decide
  rcases family_descends (prefixWord ++ tailWord_3051190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3051196 : List Nat := [2, 2, 2, 3, 1, 3, 1, 1, 1, 4, 3]
def baseStart_3051196 : Nat := 118140960795 + 3051196 * 2 ^ 59
def prefixEnd_3051196 : Nat := 4983230072969 + 3 ^ 40 * 3051196 * 2
def baseEnd_3051196 : Nat := 1566730119075949415317811

theorem tailTrace_3051196 : CollatzResearch.WordTrace tailWord_3051196 prefixEnd_3051196 1566730119075949415317811 := by
  unfold tailWord_3051196
  simp only [CollatzResearch.WordTrace]
  refine ⟨55643130327022734817398721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74190840436030313089864961 55643130327022734817398721)
  ·
    refine ⟨41732347745267051113049041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55643130327022734817398721 41732347745267051113049041)
    ·
      refine ⟨31299260808950288334786781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41732347745267051113049041 31299260808950288334786781)
      ·
        refine ⟨11737222803356358125545043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31299260808950288334786781 11737222803356358125545043)
        ·
          refine ⟨17605834205034537188317565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11737222803356358125545043 17605834205034537188317565)
          ·
            refine ⟨6602187826887951445619087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17605834205034537188317565 6602187826887951445619087)
            ·
              refine ⟨9903281740331927168428631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6602187826887951445619087 9903281740331927168428631)
              ·
                refine ⟨14854922610497890752642947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9903281740331927168428631 14854922610497890752642947)
                ·
                  refine ⟨22282383915746836128964421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14854922610497890752642947 22282383915746836128964421)
                  ·
                    refine ⟨4177946984202531774180829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22282383915746836128964421 4177946984202531774180829)
                    ·
                      refine ⟨1566730119075949415317811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4177946984202531774180829 1566730119075949415317811)
                      ·
                        rfl

theorem cell23_3051196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 1, 1, 1, 4, 3].length) (baseStart_3051196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3051196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3051196 prefixEnd_3051196 := by exact prefixLift 3051196
  have htrace : WordTrace (prefixWord ++ tailWord_3051196) baseStart_3051196 baseEnd_3051196 := by
    simpa [prefixWord, tailWord_3051196, baseEnd_3051196] using wordTrace_append hprefix tailTrace_3051196
  have hstable : (prefixWord ++ tailWord_3051196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3051196).length < 2 ^ (prefixWord ++ tailWord_3051196).sum := by decide
  have hdescent : baseEnd_3051196 < baseStart_3051196 := by decide
  rcases family_descends (prefixWord ++ tailWord_3051196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3051220 : List Nat := [2, 4, 1, 3, 1, 1, 2, 4, 1, 4]
def baseStart_3051220 : Nat := 118140960795 + 3051220 * 2 ^ 59
def prefixEnd_3051220 : Nat := 4983230072969 + 3 ^ 40 * 3051220 * 2
def baseEnd_3051220 : Nat := 522247480870552440472567

theorem tailTrace_3051220 : CollatzResearch.WordTrace tailWord_3051220 prefixEnd_3051220 522247480870552440472567 := by
  unfold tailWord_3051220
  simp only [CollatzResearch.WordTrace]
  refine ⟨55643568002979260866835557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74191424003972347822447409 55643568002979260866835557)
  ·
    refine ⟨10433169000558611412531667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55643568002979260866835557 10433169000558611412531667)
    ·
      refine ⟨15649753500837917118797501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10433169000558611412531667 15649753500837917118797501)
      ·
        refine ⟨5868657562814218919549063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15649753500837917118797501 5868657562814218919549063)
        ·
          refine ⟨8802986344221328379323595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5868657562814218919549063 8802986344221328379323595)
          ·
            refine ⟨13204479516331992568985393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8802986344221328379323595 13204479516331992568985393)
            ·
              refine ⟨9903359637248994426739045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13204479516331992568985393 9903359637248994426739045)
              ·
                refine ⟨1856879931984186455013571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9903359637248994426739045 1856879931984186455013571)
                ·
                  refine ⟨2785319897976279682520357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1856879931984186455013571 2785319897976279682520357)
                  ·
                    refine ⟨522247480870552440472567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2785319897976279682520357 522247480870552440472567)
                    ·
                      rfl

theorem cell23_3051220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 2, 4, 1, 4].length) (baseStart_3051220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3051220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3051220 prefixEnd_3051220 := by exact prefixLift 3051220
  have htrace : WordTrace (prefixWord ++ tailWord_3051220) baseStart_3051220 baseEnd_3051220 := by
    simpa [prefixWord, tailWord_3051220, baseEnd_3051220] using wordTrace_append hprefix tailTrace_3051220
  have hstable : (prefixWord ++ tailWord_3051220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3051220).length < 2 ^ (prefixWord ++ tailWord_3051220).sum := by decide
  have hdescent : baseEnd_3051220 < baseStart_3051220 := by decide
  rcases family_descends (prefixWord ++ tailWord_3051220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3051233 : List Nat := [1, 2, 3, 1, 5, 1, 3, 1, 6]
def baseStart_3051233 : Nat := 118140960795 + 3051233 * 2 ^ 59
def prefixEnd_3051233 : Nat := 4983230072969 + 3 ^ 40 * 3051233 * 2
def baseEnd_3051233 : Nat := 174083235317796196728349

theorem tailTrace_3051233 : CollatzResearch.WordTrace tailWord_3051233 prefixEnd_3051233 174083235317796196728349 := by
  unfold tailWord_3051233
  simp only [CollatzResearch.WordTrace]
  refine ⟨111287610154911424953894353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74191740103274283302596235 111287610154911424953894353)
  ·
    refine ⟨83465707616183568715420765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111287610154911424953894353 83465707616183568715420765)
    ·
      refine ⟨31299640356068838268282787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83465707616183568715420765 31299640356068838268282787)
      ·
        refine ⟨46949460534103257402424181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31299640356068838268282787 46949460534103257402424181)
        ·
          refine ⟨4401511925072180381477267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 46949460534103257402424181 4401511925072180381477267)
          ·
            refine ⟨6602267887608270572215901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4401511925072180381477267 6602267887608270572215901)
            ·
              refine ⟨2475850457853101464580963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6602267887608270572215901 2475850457853101464580963)
              ·
                refine ⟨3713775686779652196871445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2475850457853101464580963 3713775686779652196871445)
                ·
                  refine ⟨174083235317796196728349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3713775686779652196871445 174083235317796196728349)
                  ·
                    rfl

theorem cell23_3051233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 3, 1, 6].length) (baseStart_3051233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3051233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3051233 prefixEnd_3051233 := by exact prefixLift 3051233
  have htrace : WordTrace (prefixWord ++ tailWord_3051233) baseStart_3051233 baseEnd_3051233 := by
    simpa [prefixWord, tailWord_3051233, baseEnd_3051233] using wordTrace_append hprefix tailTrace_3051233
  have hstable : (prefixWord ++ tailWord_3051233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3051233).length < 2 ^ (prefixWord ++ tailWord_3051233).sum := by decide
  have hdescent : baseEnd_3051233 < baseStart_3051233 := by decide
  rcases family_descends (prefixWord ++ tailWord_3051233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3051236 : List Nat := [2, 3, 1, 1, 1, 3, 1, 1, 3, 5, 2]
def baseStart_3051236 : Nat := 118140960795 + 3051236 * 2 ^ 59
def prefixEnd_3051236 : Nat := 4983230072969 + 3 ^ 40 * 3051236 * 2
def baseEnd_3051236 : Nat := 1566750658302129258817627

theorem tailTrace_3051236 : CollatzResearch.WordTrace tailWord_3051236 prefixEnd_3051236 1566750658302129258817627 := by
  unfold tailWord_3051236
  simp only [CollatzResearch.WordTrace]
  refine ⟨55643859786950278233126781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74191813049267037644169041 55643859786950278233126781)
  ·
    refine ⟨20866447420106354337422543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55643859786950278233126781 20866447420106354337422543)
    ·
      refine ⟨31299671130159531506133815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20866447420106354337422543 31299671130159531506133815)
      ·
        refine ⟨46949506695239297259200723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31299671130159531506133815 46949506695239297259200723)
        ·
          refine ⟨70424260042858945888801085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46949506695239297259200723 70424260042858945888801085)
          ·
            refine ⟨26409097516072104708300407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70424260042858945888801085 26409097516072104708300407)
            ·
              refine ⟨39613646274108157062450611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26409097516072104708300407 39613646274108157062450611)
              ·
                refine ⟨59420469411162235593675917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39613646274108157062450611 59420469411162235593675917)
                ·
                  refine ⟨22282676029185838347628469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59420469411162235593675917 22282676029185838347628469)
                  ·
                    refine ⟨2089000877736172345090169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 22282676029185838347628469 2089000877736172345090169)
                    ·
                      refine ⟨1566750658302129258817627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2089000877736172345090169 1566750658302129258817627)
                      ·
                        rfl

theorem cell23_3051236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 1, 3, 5, 2].length) (baseStart_3051236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3051236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3051236 prefixEnd_3051236 := by exact prefixLift 3051236
  have htrace : WordTrace (prefixWord ++ tailWord_3051236) baseStart_3051236 baseEnd_3051236 := by
    simpa [prefixWord, tailWord_3051236, baseEnd_3051236] using wordTrace_append hprefix tailTrace_3051236
  have hstable : (prefixWord ++ tailWord_3051236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3051236).length < 2 ^ (prefixWord ++ tailWord_3051236).sum := by decide
  have hdescent : baseEnd_3051236 < baseStart_3051236 := by decide
  rcases family_descends (prefixWord ++ tailWord_3051236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3051276 : List Nat := [2, 2, 1, 2, 2, 1, 4, 1, 4, 4]
def baseStart_3051276 : Nat := 118140960795 + 3051276 * 2 ^ 59
def prefixEnd_3051276 : Nat := 4983230072969 + 3 ^ 40 * 3051276 * 2
def baseEnd_3051276 : Nat := 522257065842769700772481

theorem tailTrace_3051276 : CollatzResearch.WordTrace tailWord_3051276 prefixEnd_3051276 522257065842769700772481 := by
  unfold tailWord_3051276
  simp only [CollatzResearch.WordTrace]
  refine ⟨55644589246877821648854841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74192785662503762198473121 55644589246877821648854841)
  ·
    refine ⟨41733441935158366236641131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55644589246877821648854841 41733441935158366236641131)
    ·
      refine ⟨62600162902737549354961697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41733441935158366236641131 62600162902737549354961697)
      ·
        refine ⟨46950122177053162016221273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62600162902737549354961697 46950122177053162016221273)
        ·
          refine ⟨35212591632789871512165955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46950122177053162016221273 35212591632789871512165955)
          ·
            refine ⟨52818887449184807268248933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35212591632789871512165955 52818887449184807268248933)
            ·
              refine ⟨9903541396722151362796675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52818887449184807268248933 9903541396722151362796675)
              ·
                refine ⟨14855312095083227044195013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9903541396722151362796675 14855312095083227044195013)
                ·
                  refine ⟨2785371017828105070786565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14855312095083227044195013 2785371017828105070786565)
                  ·
                    refine ⟨522257065842769700772481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2785371017828105070786565 522257065842769700772481)
                    ·
                      rfl

theorem cell23_3051276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 4, 1, 4, 4].length) (baseStart_3051276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3051276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3051276 prefixEnd_3051276 := by exact prefixLift 3051276
  have htrace : WordTrace (prefixWord ++ tailWord_3051276) baseStart_3051276 baseEnd_3051276 := by
    simpa [prefixWord, tailWord_3051276, baseEnd_3051276] using wordTrace_append hprefix tailTrace_3051276
  have hstable : (prefixWord ++ tailWord_3051276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3051276).length < 2 ^ (prefixWord ++ tailWord_3051276).sum := by decide
  have hdescent : baseEnd_3051276 < baseStart_3051276 := by decide
  rcases family_descends (prefixWord ++ tailWord_3051276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3051279 : List Nat := [1, 1, 2, 1, 1, 1, 4, 1, 5, 2, 4]
def baseStart_3051279 : Nat := 118140960795 + 3051279 * 2 ^ 59
def prefixEnd_3051279 : Nat := 4983230072969 + 3 ^ 40 * 3051279 * 2
def baseEnd_3051279 : Nat := 1566772737970272590579929

theorem tailTrace_3051279 : CollatzResearch.WordTrace tailWord_3051279 prefixEnd_3051279 1566772737970272590579929 := by
  unfold tailWord_3051279
  simp only [CollatzResearch.WordTrace]
  refine ⟨111289287912744774810068891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74192858608496516540045927 111289287912744774810068891)
  ·
    refine ⟨166933931869117162215103337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111289287912744774810068891 166933931869117162215103337)
    ·
      refine ⟨125200448901837871661327503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166933931869117162215103337 125200448901837871661327503)
      ·
        refine ⟨187800673352756807491991255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125200448901837871661327503 187800673352756807491991255)
        ·
          refine ⟨281701010029135211237986883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 187800673352756807491991255 281701010029135211237986883)
          ·
            refine ⟨422551515043702816856980325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 281701010029135211237986883 422551515043702816856980325)
            ·
              refine ⟨79228409070694278160683811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 422551515043702816856980325 79228409070694278160683811)
              ·
                refine ⟨118842613606041417241025717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79228409070694278160683811 118842613606041417241025717)
                ·
                  refine ⟨11141495025566382866346161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 118842613606041417241025717 11141495025566382866346161)
                  ·
                    refine ⟨8356121269174787149759621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11141495025566382866346161 8356121269174787149759621)
                    ·
                      refine ⟨1566772737970272590579929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8356121269174787149759621 1566772737970272590579929)
                      ·
                        rfl

theorem cell23_3051279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 1, 5, 2, 4].length) (baseStart_3051279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3051279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3051279 prefixEnd_3051279 := by exact prefixLift 3051279
  have htrace : WordTrace (prefixWord ++ tailWord_3051279) baseStart_3051279 baseEnd_3051279 := by
    simpa [prefixWord, tailWord_3051279, baseEnd_3051279] using wordTrace_append hprefix tailTrace_3051279
  have hstable : (prefixWord ++ tailWord_3051279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3051279).length < 2 ^ (prefixWord ++ tailWord_3051279).sum := by decide
  have hdescent : baseEnd_3051279 < baseStart_3051279 := by decide
  rcases family_descends (prefixWord ++ tailWord_3051279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3051283 : List Nat := [1, 1, 1, 2, 1, 3, 2, 5, 3, 2, 2]
def baseStart_3051283 : Nat := 118140960795 + 3051283 * 2 ^ 59
def prefixEnd_3051283 : Nat := 4983230072969 + 3 ^ 40 * 3051283 * 2
def baseEnd_3051283 : Nat := 1566774791892890574929911

theorem tailTrace_3051283 : CollatzResearch.WordTrace tailWord_3051283 prefixEnd_3051283 1566774791892890574929911 := by
  unfold tailWord_3051283
  simp only [CollatzResearch.WordTrace]
  refine ⟨111289433804730283493214503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74192955869820188995476335 111289433804730283493214503)
  ·
    refine ⟨166934150707095425239821755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111289433804730283493214503 166934150707095425239821755)
    ·
      refine ⟨250401226060643137859732633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166934150707095425239821755 250401226060643137859732633)
      ·
        refine ⟨187800919545482353394799475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 250401226060643137859732633 187800919545482353394799475)
        ·
          refine ⟨281701379318223530092199213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 187800919545482353394799475 281701379318223530092199213)
          ·
            refine ⟨105638017244333823784574705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 281701379318223530092199213 105638017244333823784574705)
            ·
              refine ⟨79228512933250367838431029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 105638017244333823784574705 79228512933250367838431029)
              ·
                refine ⟨7427673087492221984852909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 79228512933250367838431029 7427673087492221984852909)
                ·
                  refine ⟨2785377407809583244319841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7427673087492221984852909 2785377407809583244319841)
                  ·
                    refine ⟨2089033055857187433239881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2785377407809583244319841 2089033055857187433239881)
                    ·
                      refine ⟨1566774791892890574929911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2089033055857187433239881 1566774791892890574929911)
                      ·
                        rfl

theorem cell23_3051283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 5, 3, 2, 2].length) (baseStart_3051283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3051283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3051283 prefixEnd_3051283 := by exact prefixLift 3051283
  have htrace : WordTrace (prefixWord ++ tailWord_3051283) baseStart_3051283 baseEnd_3051283 := by
    simpa [prefixWord, tailWord_3051283, baseEnd_3051283] using wordTrace_append hprefix tailTrace_3051283
  have hstable : (prefixWord ++ tailWord_3051283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3051283).length < 2 ^ (prefixWord ++ tailWord_3051283).sum := by decide
  have hdescent : baseEnd_3051283 < baseStart_3051283 := by decide
  rcases family_descends (prefixWord ++ tailWord_3051283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3051284 : List Nat := [2, 4, 4, 1, 1, 2, 2, 1, 6]
def baseStart_3051284 : Nat := 118140960795 + 3051284 * 2 ^ 59
def prefixEnd_3051284 : Nat := 4983230072969 + 3 ^ 40 * 3051284 * 2
def baseEnd_3051284 : Nat := 174086145041505007890823

theorem tailTrace_3051284 : CollatzResearch.WordTrace tailWord_3051284 prefixEnd_3051284 174086145041505007890823 := by
  unfold tailWord_3051284
  simp only [CollatzResearch.WordTrace]
  refine ⟨55644735138863330332000453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74192980185151107109333937 55644735138863330332000453)
  ·
    refine ⟨10433387838536874437250085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55644735138863330332000453 10433387838536874437250085)
    ·
      refine ⟨1956260219725663956984391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10433387838536874437250085 1956260219725663956984391)
      ·
        refine ⟨2934390329588495935476587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1956260219725663956984391 2934390329588495935476587)
        ·
          refine ⟨4401585494382743903214881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2934390329588495935476587 4401585494382743903214881)
          ·
            refine ⟨3301189120787057927411161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4401585494382743903214881 3301189120787057927411161)
            ·
              refine ⟨2475891840590293445558371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3301189120787057927411161 2475891840590293445558371)
              ·
                refine ⟨3713837760885440168337557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2475891840590293445558371 3713837760885440168337557)
                ·
                  refine ⟨174086145041505007890823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3713837760885440168337557 174086145041505007890823)
                  ·
                    rfl

theorem cell23_3051284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 2, 2, 1, 6].length) (baseStart_3051284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3051284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3051284 prefixEnd_3051284 := by exact prefixLift 3051284
  have htrace : WordTrace (prefixWord ++ tailWord_3051284) baseStart_3051284 baseEnd_3051284 := by
    simpa [prefixWord, tailWord_3051284, baseEnd_3051284] using wordTrace_append hprefix tailTrace_3051284
  have hstable : (prefixWord ++ tailWord_3051284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3051284).length < 2 ^ (prefixWord ++ tailWord_3051284).sum := by decide
  have hdescent : baseEnd_3051284 < baseStart_3051284 := by decide
  rcases family_descends (prefixWord ++ tailWord_3051284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3051296 : List Nat := [2, 1, 1, 5, 1, 1, 2, 3, 1, 2, 4]
def baseStart_3051296 : Nat := 118140960795 + 3051296 * 2 ^ 59
def prefixEnd_3051296 : Nat := 4983230072969 + 3 ^ 40 * 3051296 * 2
def baseEnd_3051296 : Nat := 1566781467141399024067351

theorem tailTrace_3051296 : CollatzResearch.WordTrace tailWord_3051296 prefixEnd_3051296 1566781467141399024067351 := by
  unfold tailWord_3051296
  simp only [CollatzResearch.WordTrace]
  refine ⟨55644953976841593356718871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74193271969122124475625161 55644953976841593356718871)
  ·
    refine ⟨83467430965262390035078307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55644953976841593356718871 83467430965262390035078307)
    ·
      refine ⟨125201146447893585052617461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83467430965262390035078307 125201146447893585052617461)
      ·
        refine ⟨11737607479490023598682887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 125201146447893585052617461 11737607479490023598682887)
        ·
          refine ⟨17606411219235035398024331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11737607479490023598682887 17606411219235035398024331)
          ·
            refine ⟨26409616828852553097036497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17606411219235035398024331 26409616828852553097036497)
            ·
              refine ⟨19807212621639414822777373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26409616828852553097036497 19807212621639414822777373)
              ·
                refine ⟨7427704733114780558541515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19807212621639414822777373 7427704733114780558541515)
                ·
                  refine ⟨11141557099672170837812273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7427704733114780558541515 11141557099672170837812273)
                  ·
                    refine ⟨8356167824754128128359205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11141557099672170837812273 8356167824754128128359205)
                    ·
                      refine ⟨1566781467141399024067351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8356167824754128128359205 1566781467141399024067351)
                      ·
                        rfl

theorem cell23_3051296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 3, 1, 2, 4].length) (baseStart_3051296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3051296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3051296 prefixEnd_3051296 := by exact prefixLift 3051296
  have htrace : WordTrace (prefixWord ++ tailWord_3051296) baseStart_3051296 baseEnd_3051296 := by
    simpa [prefixWord, tailWord_3051296, baseEnd_3051296] using wordTrace_append hprefix tailTrace_3051296
  have hstable : (prefixWord ++ tailWord_3051296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3051296).length < 2 ^ (prefixWord ++ tailWord_3051296).sum := by decide
  have hdescent : baseEnd_3051296 < baseStart_3051296 := by decide
  rcases family_descends (prefixWord ++ tailWord_3051296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3051300 : List Nat := [2, 3, 1, 3, 2, 3, 1, 2, 1, 1, 4]
def baseStart_3051300 : Nat := 118140960795 + 3051300 * 2 ^ 59
def prefixEnd_3051300 : Nat := 4983230072969 + 3 ^ 40 * 3051300 * 2
def baseEnd_3051300 : Nat := 1566783521064017008417333

theorem tailTrace_3051300 : CollatzResearch.WordTrace tailWord_3051300 prefixEnd_3051300 1566783521064017008417333 := by
  unfold tailWord_3051300
  simp only [CollatzResearch.WordTrace]
  refine ⟨55645026922834347698291677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74193369230445796931055569 55645026922834347698291677)
  ·
    refine ⟨20866885096062880386859379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55645026922834347698291677 20866885096062880386859379)
    ·
      refine ⟨31300327644094320580289069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20866885096062880386859379 31300327644094320580289069)
      ·
        refine ⟨11737622866535370217608401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31300327644094320580289069 11737622866535370217608401)
        ·
          refine ⟨8803217149901527663206301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11737622866535370217608401 8803217149901527663206301)
          ·
            refine ⟨3301206431213072873702363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8803217149901527663206301 3301206431213072873702363)
            ·
              refine ⟨4951809646819609310553545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3301206431213072873702363 4951809646819609310553545)
              ·
                refine ⟨3713857235114706982915159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4951809646819609310553545 3713857235114706982915159)
                ·
                  refine ⟨5570785852672060474372739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3713857235114706982915159 5570785852672060474372739)
                  ·
                    refine ⟨8356178779008090711559109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5570785852672060474372739 8356178779008090711559109)
                    ·
                      refine ⟨1566783521064017008417333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8356178779008090711559109 1566783521064017008417333)
                      ·
                        rfl

theorem cell23_3051300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 3, 1, 2, 1, 1, 4].length) (baseStart_3051300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3051300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3051300 prefixEnd_3051300 := by exact prefixLift 3051300
  have htrace : WordTrace (prefixWord ++ tailWord_3051300) baseStart_3051300 baseEnd_3051300 := by
    simpa [prefixWord, tailWord_3051300, baseEnd_3051300] using wordTrace_append hprefix tailTrace_3051300
  have hstable : (prefixWord ++ tailWord_3051300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3051300).length < 2 ^ (prefixWord ++ tailWord_3051300).sum := by decide
  have hdescent : baseEnd_3051300 < baseStart_3051300 := by decide
  rcases family_descends (prefixWord ++ tailWord_3051300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
