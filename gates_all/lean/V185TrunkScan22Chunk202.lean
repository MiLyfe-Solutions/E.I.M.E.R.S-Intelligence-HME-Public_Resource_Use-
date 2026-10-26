import V185TrunkScan22Chunk201

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_1801870 : List Nat := [4, 1, 1, 3, 1, 3, 9]
def baseStart_1801870 : Nat := 118140960795 + 1801870 * 2 ^ 59
def prefixEnd_1801870 : Nat := 4983230072969 + 3 ^ 40 * 1801870 * 2
def baseEnd_1801870 : Nat := 22845071281900503926873

theorem tailTrace_1801870 : CollatzResearch.WordTrace tailWord_1801870 prefixEnd_1801870 22845071281900503926873 := by
  unfold tailWord_1801870
  simp only [CollatzResearch.WordTrace]
  refine ⟨8214949747767524967635383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43813065321426799827388709 8214949747767524967635383)
  ·
    refine ⟨12322424621651287451453075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8214949747767524967635383 12322424621651287451453075)
    ·
      refine ⟨18483636932476931177179613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12322424621651287451453075 18483636932476931177179613)
      ·
        refine ⟨6931363849678849191442355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18483636932476931177179613 6931363849678849191442355)
        ·
          refine ⟨10397045774518273787163533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6931363849678849191442355 10397045774518273787163533)
          ·
            refine ⟨3898892165444352670186325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10397045774518273787163533 3898892165444352670186325)
            ·
              refine ⟨22845071281900503926873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3898892165444352670186325 22845071281900503926873)
              ·
                rfl

theorem cell22_1801870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 9].length) (baseStart_1801870 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1801870 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1801870 prefixEnd_1801870 := by exact prefixLift 1801870
  have htrace : WordTrace (prefixWord ++ tailWord_1801870) baseStart_1801870 baseEnd_1801870 := by
    simpa [prefixWord, tailWord_1801870, baseEnd_1801870] using wordTrace_append hprefix tailTrace_1801870
  have hstable : (prefixWord ++ tailWord_1801870).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1801870).length < 2 ^ (prefixWord ++ tailWord_1801870).sum := by decide
  have hdescent : baseEnd_1801870 < baseStart_1801870 := by decide
  rcases family_descends (prefixWord ++ tailWord_1801870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1801874 : List Nat := [3, 2, 3, 1, 3, 1, 1, 1, 4, 3]
def baseStart_1801874 : Nat := 118140960795 + 1801874 * 2 ^ 59
def prefixEnd_1801874 : Nat := 4983230072969 + 3 ^ 40 * 1801874 * 2
def baseEnd_1801874 : Nat := 616818293893058928925559

theorem tailTrace_1801874 : CollatzResearch.WordTrace tailWord_1801874 prefixEnd_1801874 616818293893058928925559 := by
  unfold tailWord_1801874
  simp only [CollatzResearch.WordTrace]
  refine ⟨16429935968531427106057169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43813162582750472282819117 16429935968531427106057169)
  ·
    refine ⟨12322451976398570329542877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16429935968531427106057169 12322451976398570329542877)
    ·
      refine ⟨4620919491149463873578579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12322451976398570329542877 4620919491149463873578579)
      ·
        refine ⟨6931379236724195810367869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4620919491149463873578579 6931379236724195810367869)
        ·
          refine ⟨2599267213771573428887951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6931379236724195810367869 2599267213771573428887951)
          ·
            refine ⟨3898900820657360143331927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2599267213771573428887951 3898900820657360143331927)
            ·
              refine ⟨5848351230986040214997891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3898900820657360143331927 5848351230986040214997891)
              ·
                refine ⟨8772526846479060322496837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5848351230986040214997891 8772526846479060322496837)
                ·
                  refine ⟨1644848783714823810468157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8772526846479060322496837 1644848783714823810468157)
                  ·
                    refine ⟨616818293893058928925559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1644848783714823810468157 616818293893058928925559)
                    ·
                      rfl

theorem cell22_1801874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 1, 1, 4, 3].length) (baseStart_1801874 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1801874 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1801874 prefixEnd_1801874 := by exact prefixLift 1801874
  have htrace : WordTrace (prefixWord ++ tailWord_1801874) baseStart_1801874 baseEnd_1801874 := by
    simpa [prefixWord, tailWord_1801874, baseEnd_1801874] using wordTrace_append hprefix tailTrace_1801874
  have hstable : (prefixWord ++ tailWord_1801874).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1801874).length < 2 ^ (prefixWord ++ tailWord_1801874).sum := by decide
  have hdescent : baseEnd_1801874 < baseStart_1801874 := by decide
  rcases family_descends (prefixWord ++ tailWord_1801874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1801942 : List Nat := [5, 2, 1, 3, 2, 1, 2, 1, 2, 3]
def baseStart_1801942 : Nat := 118140960795 + 1801942 * 2 ^ 59
def prefixEnd_1801942 : Nat := 4983230072969 + 3 ^ 40 * 1801942 * 2
def baseEnd_1801942 : Nat := 616841571682729418225351

theorem tailTrace_1801942 : CollatzResearch.WordTrace tailWord_1801942 prefixEnd_1801942 616841571682729418225351 := by
  unfold tailWord_1801942
  simp only [CollatzResearch.WordTrace]
  refine ⟨4107639002367459752356505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 43814816025252904025136053 4107639002367459752356505)
  ·
    refine ⟨3080729251775594814267379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4107639002367459752356505 3080729251775594814267379)
    ·
      refine ⟨4621093877663392221401069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3080729251775594814267379 4621093877663392221401069)
      ·
        refine ⟨1732910204123772083025401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4621093877663392221401069 1732910204123772083025401)
        ·
          refine ⟨1299682653092829062269051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1732910204123772083025401 1299682653092829062269051)
          ·
            refine ⟨1949523979639243593403577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1299682653092829062269051 1949523979639243593403577)
            ·
              refine ⟨1462142984729432695052683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1949523979639243593403577 1462142984729432695052683)
              ·
                refine ⟨2193214477094149042579025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1462142984729432695052683 2193214477094149042579025)
                ·
                  refine ⟨1644910857820611781934269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2193214477094149042579025 1644910857820611781934269)
                  ·
                    refine ⟨616841571682729418225351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1644910857820611781934269 616841571682729418225351)
                    ·
                      rfl

theorem cell22_1801942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 1, 2, 1, 2, 3].length) (baseStart_1801942 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1801942 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1801942 prefixEnd_1801942 := by exact prefixLift 1801942
  have htrace : WordTrace (prefixWord ++ tailWord_1801942) baseStart_1801942 baseEnd_1801942 := by
    simpa [prefixWord, tailWord_1801942, baseEnd_1801942] using wordTrace_append hprefix tailTrace_1801942
  have hstable : (prefixWord ++ tailWord_1801942).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1801942).length < 2 ^ (prefixWord ++ tailWord_1801942).sum := by decide
  have hdescent : baseEnd_1801942 < baseStart_1801942 := by decide
  rcases family_descends (prefixWord ++ tailWord_1801942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1801975 : List Nat := [1, 1, 3, 1, 1, 1, 5, 1, 3, 5]
def baseStart_1801975 : Nat := 118140960795 + 1801975 * 2 ^ 59
def prefixEnd_1801975 : Nat := 4983230072969 + 3 ^ 40 * 1801975 * 2
def baseEnd_1801975 : Nat := 616852868257128332150249

theorem tailTrace_1801975 : CollatzResearch.WordTrace tailWord_1801975 prefixEnd_1801975 616852868257128332150249 := by
  unfold tailWord_1801975
  simp only [CollatzResearch.WordTrace]
  refine ⟨65723427646759802673655379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43815618431173201782436919 65723427646759802673655379)
  ·
    refine ⟨98585141470139704010483069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65723427646759802673655379 98585141470139704010483069)
    ·
      refine ⟨36969428051302389003931151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98585141470139704010483069 36969428051302389003931151)
      ·
        refine ⟨55454142076953583505896727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36969428051302389003931151 55454142076953583505896727)
        ·
          refine ⟨83181213115430375258845091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55454142076953583505896727 83181213115430375258845091)
          ·
            refine ⟨124771819673145562888267637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83181213115430375258845091 124771819673145562888267637)
            ·
              refine ⟨11697358094357396520775091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 124771819673145562888267637 11697358094357396520775091)
              ·
                refine ⟨17546037141536094781162637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11697358094357396520775091 17546037141536094781162637)
                ·
                  refine ⟨6579763928076035542935989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17546037141536094781162637 6579763928076035542935989)
                  ·
                    refine ⟨616852868257128332150249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6579763928076035542935989 616852868257128332150249)
                    ·
                      rfl

theorem cell22_1801975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 1, 3, 5].length) (baseStart_1801975 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1801975 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1801975 prefixEnd_1801975 := by exact prefixLift 1801975
  have htrace : WordTrace (prefixWord ++ tailWord_1801975) baseStart_1801975 baseEnd_1801975 := by
    simpa [prefixWord, tailWord_1801975, baseEnd_1801975] using wordTrace_append hprefix tailTrace_1801975
  have hstable : (prefixWord ++ tailWord_1801975).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1801975).length < 2 ^ (prefixWord ++ tailWord_1801975).sum := by decide
  have hdescent : baseEnd_1801975 < baseStart_1801975 := by decide
  rcases family_descends (prefixWord ++ tailWord_1801975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1801994 : List Nat := [3, 1, 2, 2, 1, 4, 1, 4, 4]
def baseStart_1801994 : Nat := 118140960795 + 1801994 * 2 ^ 59
def prefixEnd_1801994 : Nat := 4983230072969 + 3 ^ 40 * 1801994 * 2
def baseEnd_1801994 : Nat := 205619790781806205308397

theorem tailTrace_1801994 : CollatzResearch.WordTrace tailWord_1801994 prefixEnd_1801994 205619790781806205308397 := by
  unfold tailWord_1801994
  simp only [CollatzResearch.WordTrace]
  refine ⟨16431030158422742229649259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43816080422460645945731357 16431030158422742229649259)
  ·
    refine ⟨24646545237634113344473889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16431030158422742229649259 24646545237634113344473889)
    ·
      refine ⟨18484908928225585008355417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24646545237634113344473889 18484908928225585008355417)
      ·
        refine ⟨13863681696169188756266563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18484908928225585008355417 13863681696169188756266563)
        ·
          refine ⟨20795522544253783134399845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13863681696169188756266563 20795522544253783134399845)
          ·
            refine ⟨3899160477047584337699971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20795522544253783134399845 3899160477047584337699971)
            ·
              refine ⟨5848740715571376506549957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3899160477047584337699971 5848740715571376506549957)
              ·
                refine ⟨1096638884169633094978117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5848740715571376506549957 1096638884169633094978117)
                ·
                  refine ⟨205619790781806205308397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1096638884169633094978117 205619790781806205308397)
                  ·
                    rfl

theorem cell22_1801994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 1, 4, 4].length) (baseStart_1801994 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1801994 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1801994 prefixEnd_1801994 := by exact prefixLift 1801994
  have htrace : WordTrace (prefixWord ++ tailWord_1801994) baseStart_1801994 baseEnd_1801994 := by
    simpa [prefixWord, tailWord_1801994, baseEnd_1801994] using wordTrace_append hprefix tailTrace_1801994
  have hstable : (prefixWord ++ tailWord_1801994).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1801994).length < 2 ^ (prefixWord ++ tailWord_1801994).sum := by decide
  have hdescent : baseEnd_1801994 < baseStart_1801994 := by decide
  rcases family_descends (prefixWord ++ tailWord_1801994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1802024 : List Nat := [2, 1, 5, 1, 1, 2, 3, 1, 2, 4]
def baseStart_1802024 : Nat := 118140960795 + 1802024 * 2 ^ 59
def prefixEnd_1802024 : Nat := 4983230072969 + 3 ^ 40 * 1802024 * 2
def baseEnd_1802024 : Nat := 616869641958508537675099

theorem tailTrace_1802024 : CollatzResearch.WordTrace tailWord_1802024 prefixEnd_1802024 616869641958508537675099 := by
  unfold tailWord_1802024
  simp only [CollatzResearch.WordTrace]
  refine ⟨32862607411791142021094563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43816809882388189361459417 32862607411791142021094563)
  ·
    refine ⟨49293911117686713031641845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32862607411791142021094563 49293911117686713031641845)
    ·
      refine ⟨4621304167283129346716423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 49293911117686713031641845 4621304167283129346716423)
      ·
        refine ⟨6931956250924694020074635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4621304167283129346716423 6931956250924694020074635)
        ·
          refine ⟨10397934376387041030111953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6931956250924694020074635 10397934376387041030111953)
          ·
            refine ⟨7798450782290280772583965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10397934376387041030111953 7798450782290280772583965)
            ·
              refine ⟨2924419043358855289718987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7798450782290280772583965 2924419043358855289718987)
              ·
                refine ⟨4386628565038282934578481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2924419043358855289718987 4386628565038282934578481)
                ·
                  refine ⟨3289971423778712200933861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4386628565038282934578481 3289971423778712200933861)
                  ·
                    refine ⟨616869641958508537675099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3289971423778712200933861 616869641958508537675099)
                    ·
                      rfl

theorem cell22_1802024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 3, 1, 2, 4].length) (baseStart_1802024 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1802024 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1802024 prefixEnd_1802024 := by exact prefixLift 1802024
  have htrace : WordTrace (prefixWord ++ tailWord_1802024) baseStart_1802024 baseEnd_1802024 := by
    simpa [prefixWord, tailWord_1802024, baseEnd_1802024] using wordTrace_append hprefix tailTrace_1802024
  have hstable : (prefixWord ++ tailWord_1802024).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1802024).length < 2 ^ (prefixWord ++ tailWord_1802024).sum := by decide
  have hdescent : baseEnd_1802024 < baseStart_1802024 := by decide
  rcases family_descends (prefixWord ++ tailWord_1802024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1802030 : List Nat := [4, 1, 3, 2, 3, 1, 2, 1, 1, 4]
def baseStart_1802030 : Nat := 118140960795 + 1802030 * 2 ^ 59
def prefixEnd_1802030 : Nat := 4983230072969 + 3 ^ 40 * 1802030 * 2
def baseEnd_1802030 : Nat := 616871695881126522025081

theorem tailTrace_1802030 : CollatzResearch.WordTrace tailWord_1802030 prefixEnd_1802030 616871695881126522025081 := by
  unfold tailWord_1802030
  simp only [CollatzResearch.WordTrace]
  refine ⟨8215679207695068383363443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43816955774373698044605029 8215679207695068383363443)
  ·
    refine ⟨12323518811542602575045165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8215679207695068383363443 12323518811542602575045165)
    ·
      refine ⟨4621319554328475965641937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12323518811542602575045165 4621319554328475965641937)
      ·
        refine ⟨3465989665746356974231453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4621319554328475965641937 3465989665746356974231453)
        ·
          refine ⟨1299746124654883865336795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3465989665746356974231453 1299746124654883865336795)
          ·
            refine ⟨1949619186982325798005193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1299746124654883865336795 1949619186982325798005193)
            ·
              refine ⟨1462214390236744348503895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1949619186982325798005193 1462214390236744348503895)
              ·
                refine ⟨2193321585355116522755843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1462214390236744348503895 2193321585355116522755843)
                ·
                  refine ⟨3289982378032674784133765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2193321585355116522755843 3289982378032674784133765)
                  ·
                    refine ⟨616871695881126522025081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3289982378032674784133765 616871695881126522025081)
                    ·
                      rfl

theorem cell22_1802030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 1, 2, 1, 1, 4].length) (baseStart_1802030 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1802030 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1802030 prefixEnd_1802030 := by exact prefixLift 1802030
  have htrace : WordTrace (prefixWord ++ tailWord_1802030) baseStart_1802030 baseEnd_1802030 := by
    simpa [prefixWord, tailWord_1802030, baseEnd_1802030] using wordTrace_append hprefix tailTrace_1802030
  have hstable : (prefixWord ++ tailWord_1802030).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1802030).length < 2 ^ (prefixWord ++ tailWord_1802030).sum := by decide
  have hdescent : baseEnd_1802030 < baseStart_1802030 := by decide
  rcases family_descends (prefixWord ++ tailWord_1802030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1802157 : List Nat := [1, 5, 2, 14]
def baseStart_1802157 : Nat := 118140960795 + 1802157 * 2 ^ 59
def prefixEnd_1802157 : Nat := 4983230072969 + 3 ^ 40 * 1802157 * 2
def baseEnd_1802157 : Nat := 846248519309383434979

theorem tailTrace_1802157 : CollatzResearch.WordTrace tailWord_1802157 prefixEnd_1802157 846248519309383434979 := by
  unfold tailWord_1802157
  simp only [CollatzResearch.WordTrace]
  refine ⟨65730065732100447756780725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43820043821400298504520483 65730065732100447756780725)
  ·
    refine ⟨6162193662384416977198193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 65730065732100447756780725 6162193662384416977198193)
    ·
      refine ⟨4621645246788312732898645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6162193662384416977198193 4621645246788312732898645)
      ·
        refine ⟨846248519309383434979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 14 4621645246788312732898645 846248519309383434979)
        ·
          rfl

theorem cell22_1802157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 14].length) (baseStart_1802157 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1802157 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1802157 prefixEnd_1802157 := by exact prefixLift 1802157
  have htrace : WordTrace (prefixWord ++ tailWord_1802157) baseStart_1802157 baseEnd_1802157 := by
    simpa [prefixWord, tailWord_1802157, baseEnd_1802157] using wordTrace_append hprefix tailTrace_1802157
  have hstable : (prefixWord ++ tailWord_1802157).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1802157).length < 2 ^ (prefixWord ++ tailWord_1802157).sum := by decide
  have hdescent : baseEnd_1802157 < baseStart_1802157 := by decide
  rcases family_descends (prefixWord ++ tailWord_1802157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1802161 : List Nat := [1, 2, 2, 4, 2, 1, 1, 4, 2, 3]
def baseStart_1802161 : Nat := 118140960795 + 1802161 * 2 ^ 59
def prefixEnd_1802161 : Nat := 4983230072969 + 3 ^ 40 * 1802161 * 2
def baseEnd_1802161 : Nat := 616916539858285846999679

theorem tailTrace_1802161 : CollatzResearch.WordTrace tailWord_1802161 prefixEnd_1802161 616916539858285846999679 := by
  unfold tailWord_1802161
  simp only [CollatzResearch.WordTrace]
  refine ⟨65730211624085956439926337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43820141082723970959950891 65730211624085956439926337)
  ·
    refine ⟨49297658718064467329944753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65730211624085956439926337 49297658718064467329944753)
    ·
      refine ⟨36973244038548350497458565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49297658718064467329944753 36973244038548350497458565)
      ·
        refine ⟨6932483257227815718273481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36973244038548350497458565 6932483257227815718273481)
        ·
          refine ⟨5199362442920861788705111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6932483257227815718273481 5199362442920861788705111)
          ·
            refine ⟨7799043664381292683057667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5199362442920861788705111 7799043664381292683057667)
            ·
              refine ⟨11698565496571939024586501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7799043664381292683057667 11698565496571939024586501)
              ·
                refine ⟨2193481030607238567109969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11698565496571939024586501 2193481030607238567109969)
                ·
                  refine ⟨1645110772955428925332477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2193481030607238567109969 1645110772955428925332477)
                  ·
                    refine ⟨616916539858285846999679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1645110772955428925332477 616916539858285846999679)
                    ·
                      rfl

theorem cell22_1802161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 4, 2, 3].length) (baseStart_1802161 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1802161 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1802161 prefixEnd_1802161 := by exact prefixLift 1802161
  have htrace : WordTrace (prefixWord ++ tailWord_1802161) baseStart_1802161 baseEnd_1802161 := by
    simpa [prefixWord, tailWord_1802161, baseEnd_1802161] using wordTrace_append hprefix tailTrace_1802161
  have hstable : (prefixWord ++ tailWord_1802161).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1802161).length < 2 ^ (prefixWord ++ tailWord_1802161).sum := by decide
  have hdescent : baseEnd_1802161 < baseStart_1802161 := by decide
  rcases family_descends (prefixWord ++ tailWord_1802161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1802174 : List Nat := [4, 2, 1, 1, 1, 3, 3, 7]
def baseStart_1802174 : Nat := 118140960795 + 1802174 * 2 ^ 59
def prefixEnd_1802174 : Nat := 4983230072969 + 3 ^ 40 * 1802174 * 2
def baseEnd_1802174 : Nat := 68546776669328682936071

theorem tailTrace_1802174 : CollatzResearch.WordTrace tailWord_1802174 prefixEnd_1802174 68546776669328682936071 := by
  unfold tailWord_1802174
  simp only [CollatzResearch.WordTrace]
  refine ⟨8216335721629857457518697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43820457182025906440099717 8216335721629857457518697)
  ·
    refine ⟨6162251791222393093139023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8216335721629857457518697 6162251791222393093139023)
    ·
      refine ⟨9243377686833589639708535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6162251791222393093139023 9243377686833589639708535)
      ·
        refine ⟨13865066530250384459562803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9243377686833589639708535 13865066530250384459562803)
        ·
          refine ⟨20797599795375576689344205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13865066530250384459562803 20797599795375576689344205)
          ·
            refine ⟨7799099923265841258504077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20797599795375576689344205 7799099923265841258504077)
            ·
              refine ⟨2924662471224690471939029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7799099923265841258504077 2924662471224690471939029)
              ·
                refine ⟨68546776669328682936071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2924662471224690471939029 68546776669328682936071)
                ·
                  rfl

theorem cell22_1802174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 3, 7].length) (baseStart_1802174 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1802174 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1802174 prefixEnd_1802174 := by exact prefixLift 1802174
  have htrace : WordTrace (prefixWord ++ tailWord_1802174) baseStart_1802174 baseEnd_1802174 := by
    simpa [prefixWord, tailWord_1802174, baseEnd_1802174] using wordTrace_append hprefix tailTrace_1802174
  have hstable : (prefixWord ++ tailWord_1802174).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1802174).length < 2 ^ (prefixWord ++ tailWord_1802174).sum := by decide
  have hdescent : baseEnd_1802174 < baseStart_1802174 := by decide
  rcases family_descends (prefixWord ++ tailWord_1802174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1802187 : List Nat := [1, 1, 1, 1, 3, 4, 1, 2, 2, 6]
def baseStart_1802187 : Nat := 118140960795 + 1802187 * 2 ^ 59
def prefixEnd_1802187 : Nat := 4983230072969 + 3 ^ 40 * 1802187 * 2
def baseEnd_1802187 : Nat := 616925440189630445849599

theorem tailTrace_1802187 : CollatzResearch.WordTrace tailWord_1802187 prefixEnd_1802187 616925440189630445849599 := by
  unfold tailWord_1802187
  simp only [CollatzResearch.WordTrace]
  refine ⟨65731159921991762880372815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43820773281327841920248543 65731159921991762880372815)
  ·
    refine ⟨98596739882987644320559223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65731159921991762880372815 98596739882987644320559223)
    ·
      refine ⟨147895109824481466480838835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98596739882987644320559223 147895109824481466480838835)
      ·
        refine ⟨221842664736722199721258253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147895109824481466480838835 221842664736722199721258253)
        ·
          refine ⟨83190999276270824895471845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 221842664736722199721258253 83190999276270824895471845)
          ·
            refine ⟨15598312364300779667900971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 83190999276270824895471845 15598312364300779667900971)
            ·
              refine ⟨23397468546451169501851457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15598312364300779667900971 23397468546451169501851457)
              ·
                refine ⟨17548101409838377126388593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23397468546451169501851457 17548101409838377126388593)
                ·
                  refine ⟨13161076057378782844791445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17548101409838377126388593 13161076057378782844791445)
                  ·
                    refine ⟨616925440189630445849599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13161076057378782844791445 616925440189630445849599)
                    ·
                      rfl

theorem cell22_1802187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 2, 2, 6].length) (baseStart_1802187 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1802187 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1802187 prefixEnd_1802187 := by exact prefixLift 1802187
  have htrace : WordTrace (prefixWord ++ tailWord_1802187) baseStart_1802187 baseEnd_1802187 := by
    simpa [prefixWord, tailWord_1802187, baseEnd_1802187] using wordTrace_append hprefix tailTrace_1802187
  have hstable : (prefixWord ++ tailWord_1802187).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1802187).length < 2 ^ (prefixWord ++ tailWord_1802187).sum := by decide
  have hdescent : baseEnd_1802187 < baseStart_1802187 := by decide
  rcases family_descends (prefixWord ++ tailWord_1802187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1802236 : List Nat := [2, 2, 2, 1, 2, 2, 5, 1, 5]
def baseStart_1802236 : Nat := 118140960795 + 1802236 * 2 ^ 59
def prefixEnd_1802236 : Nat := 4983230072969 + 3 ^ 40 * 1802236 * 2
def baseEnd_1802236 : Nat := 205647404630336883791483

theorem tailTrace_1802236 : CollatzResearch.WordTrace tailWord_1802236 prefixEnd_1802236 205647404630336883791483 := by
  unfold tailWord_1802236
  simp only [CollatzResearch.WordTrace]
  refine ⟨32866473549407122124453281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43821964732542829499271041 32866473549407122124453281)
  ·
    refine ⟨24649855162055341593339961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32866473549407122124453281 24649855162055341593339961)
    ·
      refine ⟨18487391371541506195004971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24649855162055341593339961 18487391371541506195004971)
      ·
        refine ⟨27731087057312259292507457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18487391371541506195004971 27731087057312259292507457)
        ·
          refine ⟨20798315292984194469380593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27731087057312259292507457 20798315292984194469380593)
          ·
            refine ⟨15598736469738145852035445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20798315292984194469380593 15598736469738145852035445)
            ·
              refine ⟨1462381544037951173628323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15598736469738145852035445 1462381544037951173628323)
              ·
                refine ⟨2193572316056926760442485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1462381544037951173628323 2193572316056926760442485)
                ·
                  refine ⟨205647404630336883791483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2193572316056926760442485 205647404630336883791483)
                  ·
                    rfl

theorem cell22_1802236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 5, 1, 5].length) (baseStart_1802236 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1802236 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1802236 prefixEnd_1802236 := by exact prefixLift 1802236
  have htrace : WordTrace (prefixWord ++ tailWord_1802236) baseStart_1802236 baseEnd_1802236 := by
    simpa [prefixWord, tailWord_1802236, baseEnd_1802236] using wordTrace_append hprefix tailTrace_1802236
  have hstable : (prefixWord ++ tailWord_1802236).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1802236).length < 2 ^ (prefixWord ++ tailWord_1802236).sum := by decide
  have hdescent : baseEnd_1802236 < baseStart_1802236 := by decide
  rcases family_descends (prefixWord ++ tailWord_1802236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1802266 : List Nat := [3, 1, 1, 3, 1, 3, 2, 3, 1, 4]
def baseStart_1802266 : Nat := 118140960795 + 1802266 * 2 ^ 59
def prefixEnd_1802266 : Nat := 4983230072969 + 3 ^ 40 * 1802266 * 2
def baseEnd_1802266 : Nat := 616952483504100573124357

theorem tailTrace_1802266 : CollatzResearch.WordTrace tailWord_1802266 prefixEnd_1802266 616952483504100573124357 := by
  unfold tailWord_1802266
  simp only [CollatzResearch.WordTrace]
  refine ⟨16433510322176389843124663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43822694192470372914999101 16433510322176389843124663)
  ·
    refine ⟨24650265483264584764686995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16433510322176389843124663 24650265483264584764686995)
    ·
      refine ⟨36975398224896877147030493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24650265483264584764686995 36975398224896877147030493)
      ·
        refine ⟨13865774334336328930136435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36975398224896877147030493 13865774334336328930136435)
        ·
          refine ⟨20798661501504493395204653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13865774334336328930136435 20798661501504493395204653)
          ·
            refine ⟨7799498063064185023201745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20798661501504493395204653 7799498063064185023201745)
            ·
              refine ⟨5849623547298138767401309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7799498063064185023201745 5849623547298138767401309)
              ·
                refine ⟨2193608830236802037775491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5849623547298138767401309 2193608830236802037775491)
                ·
                  refine ⟨3290413245355203056663237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2193608830236802037775491 3290413245355203056663237)
                  ·
                    refine ⟨616952483504100573124357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3290413245355203056663237 616952483504100573124357)
                    ·
                      rfl

theorem cell22_1802266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 2, 3, 1, 4].length) (baseStart_1802266 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1802266 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1802266 prefixEnd_1802266 := by exact prefixLift 1802266
  have htrace : WordTrace (prefixWord ++ tailWord_1802266) baseStart_1802266 baseEnd_1802266 := by
    simpa [prefixWord, tailWord_1802266, baseEnd_1802266] using wordTrace_append hprefix tailTrace_1802266
  have hstable : (prefixWord ++ tailWord_1802266).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1802266).length < 2 ^ (prefixWord ++ tailWord_1802266).sum := by decide
  have hdescent : baseEnd_1802266 < baseStart_1802266 := by decide
  rcases family_descends (prefixWord ++ tailWord_1802266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1802311 : List Nat := [1, 1, 4, 1, 3, 1, 4, 1, 2, 4]
def baseStart_1802311 : Nat := 118140960795 + 1802311 * 2 ^ 59
def prefixEnd_1802311 : Nat := 4983230072969 + 3 ^ 40 * 1802311 * 2
def baseEnd_1802311 : Nat := 616967887923735455749219

theorem tailTrace_1802311 : CollatzResearch.WordTrace tailWord_1802311 prefixEnd_1802311 616967887923735455749219 := by
  unfold tailWord_1802311
  simp only [CollatzResearch.WordTrace]
  refine ⟨65735682573542532057886787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43823788382361688038591191 65735682573542532057886787)
  ·
    refine ⟨98603523860313798086830181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65735682573542532057886787 98603523860313798086830181)
    ·
      refine ⟨18488160723808837141280659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 98603523860313798086830181 18488160723808837141280659)
      ·
        refine ⟨27732241085713255711920989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18488160723808837141280659 27732241085713255711920989)
        ·
          refine ⟨10399590407142470891970371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27732241085713255711920989 10399590407142470891970371)
          ·
            refine ⟨15599385610713706337955557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10399590407142470891970371 15599385610713706337955557)
            ·
              refine ⟨2924884802008819938366667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15599385610713706337955557 2924884802008819938366667)
              ·
                refine ⟨4387327203013229907550001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2924884802008819938366667 4387327203013229907550001)
                ·
                  refine ⟨3290495402259922430662501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4387327203013229907550001 3290495402259922430662501)
                  ·
                    refine ⟨616967887923735455749219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3290495402259922430662501 616967887923735455749219)
                    ·
                      rfl

theorem cell22_1802311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 4, 1, 2, 4].length) (baseStart_1802311 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1802311 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1802311 prefixEnd_1802311 := by exact prefixLift 1802311
  have htrace : WordTrace (prefixWord ++ tailWord_1802311) baseStart_1802311 baseEnd_1802311 := by
    simpa [prefixWord, tailWord_1802311, baseEnd_1802311] using wordTrace_append hprefix tailTrace_1802311
  have hstable : (prefixWord ++ tailWord_1802311).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1802311).length < 2 ^ (prefixWord ++ tailWord_1802311).sum := by decide
  have hdescent : baseEnd_1802311 < baseStart_1802311 := by decide
  rcases family_descends (prefixWord ++ tailWord_1802311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1802339 : List Nat := [1, 1, 1, 5, 1, 1, 3, 1, 2, 6]
def baseStart_1802339 : Nat := 118140960795 + 1802339 * 2 ^ 59
def prefixEnd_1802339 : Nat := 4983230072969 + 3 ^ 40 * 1802339 * 2
def baseEnd_1802339 : Nat := 616977472895952716049133

theorem tailTrace_1802339 : CollatzResearch.WordTrace tailWord_1802339 prefixEnd_1802339 616977472895952716049133 := by
  unfold tailWord_1802339
  simp only [CollatzResearch.WordTrace]
  refine ⟨65736703817441092839906071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43824469211627395226604047 65736703817441092839906071)
  ·
    refine ⟨98605055726161639259859107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65736703817441092839906071 98605055726161639259859107)
    ·
      refine ⟨147907583589242458889788661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98605055726161639259859107 147907583589242458889788661)
      ·
        refine ⟨13866335961491480520917687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 147907583589242458889788661 13866335961491480520917687)
        ·
          refine ⟨20799503942237220781376531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13866335961491480520917687 20799503942237220781376531)
          ·
            refine ⟨31199255913355831172064797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20799503942237220781376531 31199255913355831172064797)
            ·
              refine ⟨11699720967508436689524299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31199255913355831172064797 11699720967508436689524299)
              ·
                refine ⟨17549581451262655034286449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11699720967508436689524299 17549581451262655034286449)
                ·
                  refine ⟨13162186088446991275714837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17549581451262655034286449 13162186088446991275714837)
                  ·
                    refine ⟨616977472895952716049133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13162186088446991275714837 616977472895952716049133)
                    ·
                      rfl

theorem cell22_1802339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 1, 2, 6].length) (baseStart_1802339 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1802339 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1802339 prefixEnd_1802339 := by exact prefixLift 1802339
  have htrace : WordTrace (prefixWord ++ tailWord_1802339) baseStart_1802339 baseEnd_1802339 := by
    simpa [prefixWord, tailWord_1802339, baseEnd_1802339] using wordTrace_append hprefix tailTrace_1802339
  have hstable : (prefixWord ++ tailWord_1802339).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1802339).length < 2 ^ (prefixWord ++ tailWord_1802339).sum := by decide
  have hdescent : baseEnd_1802339 < baseStart_1802339 := by decide
  rcases family_descends (prefixWord ++ tailWord_1802339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1802358 : List Nat := [5, 1, 1, 2, 1, 2, 1, 1, 5, 3]
def baseStart_1802358 : Nat := 118140960795 + 1802358 * 2 ^ 59
def prefixEnd_1802358 : Nat := 4983230072969 + 3 ^ 40 * 1802358 * 2
def baseEnd_1802358 : Nat := 616983976984242999824075

theorem tailTrace_1802358 : CollatzResearch.WordTrace tailWord_1802358 prefixEnd_1802358 616983976984242999824075 := by
  unfold tailWord_1802358
  simp only [CollatzResearch.WordTrace]
  refine ⟨4108587300273266192802983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 43824931202914839389898485 4108587300273266192802983)
  ·
    refine ⟨6162880950409899289204475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4108587300273266192802983 6162880950409899289204475)
    ·
      refine ⟨9244321425614848933806713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6162880950409899289204475 9244321425614848933806713)
      ·
        refine ⟨6933241069211136700355035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9244321425614848933806713 6933241069211136700355035)
        ·
          refine ⟨10399861603816705050532553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6933241069211136700355035 10399861603816705050532553)
          ·
            refine ⟨7799896202862528787899415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10399861603816705050532553 7799896202862528787899415)
            ·
              refine ⟨11699844304293793181849123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7799896202862528787899415 11699844304293793181849123)
              ·
                refine ⟨17549766456440689772773685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11699844304293793181849123 17549766456440689772773685)
                ·
                  refine ⟨1645290605291314666197533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 17549766456440689772773685 1645290605291314666197533)
                  ·
                    refine ⟨616983976984242999824075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1645290605291314666197533 616983976984242999824075)
                    ·
                      rfl

theorem cell22_1802358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 1, 5, 3].length) (baseStart_1802358 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1802358 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1802358 prefixEnd_1802358 := by exact prefixLift 1802358
  have htrace : WordTrace (prefixWord ++ tailWord_1802358) baseStart_1802358 baseEnd_1802358 := by
    simpa [prefixWord, tailWord_1802358, baseEnd_1802358] using wordTrace_append hprefix tailTrace_1802358
  have hstable : (prefixWord ++ tailWord_1802358).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1802358).length < 2 ^ (prefixWord ++ tailWord_1802358).sum := by decide
  have hdescent : baseEnd_1802358 < baseStart_1802358 := by decide
  rcases family_descends (prefixWord ++ tailWord_1802358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1802386 : List Nat := [3, 2, 3, 1, 1, 1, 1, 1, 4, 5]
def baseStart_1802386 : Nat := 118140960795 + 1802386 * 2 ^ 59
def prefixEnd_1802386 : Nat := 4983230072969 + 3 ^ 40 * 1802386 * 2
def baseEnd_1802386 : Nat := 616993561956460260123989

theorem tailTrace_1802386 : CollatzResearch.WordTrace tailWord_1802386 prefixEnd_1802386 616993561956460260123989 := by
  unfold tailWord_1802386
  simp only [CollatzResearch.WordTrace]
  refine ⟨16434604512067704966716753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43825612032180546577911341 16434604512067704966716753)
  ·
    refine ⟨12325953384050778725037565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16434604512067704966716753 12325953384050778725037565)
    ·
      refine ⟨4622232519019042021889087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12325953384050778725037565 4622232519019042021889087)
      ·
        refine ⟨6933348778528563032833631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4622232519019042021889087 6933348778528563032833631)
        ·
          refine ⟨10400023167792844549250447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6933348778528563032833631 10400023167792844549250447)
          ·
            refine ⟨15600034751689266823875671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10400023167792844549250447 15600034751689266823875671)
            ·
              refine ⟨23400052127533900235813507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15600034751689266823875671 23400052127533900235813507)
              ·
                refine ⟨35100078191300850353720261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23400052127533900235813507 35100078191300850353720261)
                ·
                  refine ⟨6581264660868909441322549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35100078191300850353720261 6581264660868909441322549)
                  ·
                    refine ⟨616993561956460260123989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6581264660868909441322549 616993561956460260123989)
                    ·
                      rfl

theorem cell22_1802386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 1, 4, 5].length) (baseStart_1802386 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1802386 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1802386 prefixEnd_1802386 := by exact prefixLift 1802386
  have htrace : WordTrace (prefixWord ++ tailWord_1802386) baseStart_1802386 baseEnd_1802386 := by
    simpa [prefixWord, tailWord_1802386, baseEnd_1802386] using wordTrace_append hprefix tailTrace_1802386
  have hstable : (prefixWord ++ tailWord_1802386).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1802386).length < 2 ^ (prefixWord ++ tailWord_1802386).sum := by decide
  have hdescent : baseEnd_1802386 < baseStart_1802386 := by decide
  rcases family_descends (prefixWord ++ tailWord_1802386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1802418 : List Nat := [3, 2, 1, 1, 1, 3, 4, 2, 1, 4]
def baseStart_1802418 : Nat := 118140960795 + 1802418 * 2 ^ 59
def prefixEnd_1802418 : Nat := 4983230072969 + 3 ^ 40 * 1802418 * 2
def baseEnd_1802418 : Nat := 617004516210422843323891

theorem tailTrace_1802418 : CollatzResearch.WordTrace tailWord_1802418 prefixEnd_1802418 617004516210422843323891 := by
  unfold tailWord_1802418
  simp only [CollatzResearch.WordTrace]
  refine ⟨16434896296038722333007977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43826390122769926221354605 16434896296038722333007977)
  ·
    refine ⟨12326172222029041749755983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16434896296038722333007977 12326172222029041749755983)
    ·
      refine ⟨18489258333043562624633975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12326172222029041749755983 18489258333043562624633975)
      ·
        refine ⟨27733887499565343936950963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18489258333043562624633975 27733887499565343936950963)
        ·
          refine ⟨41600831249348015905426445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27733887499565343936950963 41600831249348015905426445)
          ·
            refine ⟨15600311718505505964534917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41600831249348015905426445 15600311718505505964534917)
            ·
              refine ⟨2925058447219782368350297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15600311718505505964534917 2925058447219782368350297)
              ·
                refine ⟨2193793835414836776262723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2925058447219782368350297 2193793835414836776262723)
                ·
                  refine ⟨3290690753122255164394085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2193793835414836776262723 3290690753122255164394085)
                  ·
                    refine ⟨617004516210422843323891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3290690753122255164394085 617004516210422843323891)
                    ·
                      rfl

theorem cell22_1802418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 4, 2, 1, 4].length) (baseStart_1802418 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1802418 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1802418 prefixEnd_1802418 := by exact prefixLift 1802418
  have htrace : WordTrace (prefixWord ++ tailWord_1802418) baseStart_1802418 baseEnd_1802418 := by
    simpa [prefixWord, tailWord_1802418, baseEnd_1802418] using wordTrace_append hprefix tailTrace_1802418
  have hstable : (prefixWord ++ tailWord_1802418).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1802418).length < 2 ^ (prefixWord ++ tailWord_1802418).sum := by decide
  have hdescent : baseEnd_1802418 < baseStart_1802418 := by decide
  rcases family_descends (prefixWord ++ tailWord_1802418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1802506 : List Nat := [3, 1, 2, 2, 1, 1, 2, 3, 7]
def baseStart_1802506 : Nat := 118140960795 + 1802506 * 2 ^ 59
def prefixEnd_1802506 : Nat := 4983230072969 + 3 ^ 40 * 1802506 * 2
def baseEnd_1802506 : Nat := 205678213469606649041207

theorem tailTrace_1802506 : CollatzResearch.WordTrace tailWord_1802506 prefixEnd_1802506 205678213469606649041207 := by
  unfold tailWord_1802506
  simp only [CollatzResearch.WordTrace]
  refine ⟨16435698701959020090308843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43828529871890720240823581 16435698701959020090308843)
  ·
    refine ⟨24653548052938530135463265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16435698701959020090308843 24653548052938530135463265)
    ·
      refine ⟨18490161039703897601597449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24653548052938530135463265 18490161039703897601597449)
      ·
        refine ⟨13867620779777923201198087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18490161039703897601597449 13867620779777923201198087)
        ·
          refine ⟨20801431169666884801797131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13867620779777923201198087 20801431169666884801797131)
          ·
            refine ⟨31202146754500327202695697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20801431169666884801797131 31202146754500327202695697)
            ·
              refine ⟨23401610065875245402021773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31202146754500327202695697 23401610065875245402021773)
              ·
                refine ⟨8775603774703217025758165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23401610065875245402021773 8775603774703217025758165)
                ·
                  refine ⟨205678213469606649041207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8775603774703217025758165 205678213469606649041207)
                  ·
                    rfl

theorem cell22_1802506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 3, 7].length) (baseStart_1802506 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1802506 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1802506 prefixEnd_1802506 := by exact prefixLift 1802506
  have htrace : WordTrace (prefixWord ++ tailWord_1802506) baseStart_1802506 baseEnd_1802506 := by
    simpa [prefixWord, tailWord_1802506, baseEnd_1802506] using wordTrace_append hprefix tailTrace_1802506
  have hstable : (prefixWord ++ tailWord_1802506).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1802506).length < 2 ^ (prefixWord ++ tailWord_1802506).sum := by decide
  have hdescent : baseEnd_1802506 < baseStart_1802506 := by decide
  rcases family_descends (prefixWord ++ tailWord_1802506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1802600 : List Nat := [2, 1, 4, 2, 2, 1, 1, 2, 4, 3]
def baseStart_1802600 : Nat := 118140960795 + 1802600 * 2 ^ 59
def prefixEnd_1802600 : Nat := 4983230072969 + 3 ^ 40 * 1802600 * 2
def baseEnd_1802600 : Nat := 617066818529835035273333

theorem tailTrace_1802600 : CollatzResearch.WordTrace tailWord_1802600 prefixEnd_1802600 617066818529835035273333 := by
  unfold tailWord_1802600
  simp only [CollatzResearch.WordTrace]
  refine ⟨32873111634747767207578627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43830815512997022943438169 32873111634747767207578627)
  ·
    refine ⟨49309667452121650811367941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32873111634747767207578627 49309667452121650811367941)
    ·
      refine ⟨9245562647272809527131489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49309667452121650811367941 9245562647272809527131489)
      ·
        refine ⟨6934171985454607145348617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9245562647272809527131489 6934171985454607145348617)
        ·
          refine ⟨5200628989090955359011463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6934171985454607145348617 5200628989090955359011463)
          ·
            refine ⟨7800943483636433038517195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5200628989090955359011463 7800943483636433038517195)
            ·
              refine ⟨11701415225454649557775793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7800943483636433038517195 11701415225454649557775793)
              ·
                refine ⟨8776061419090987168331845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11701415225454649557775793 8776061419090987168331845)
                ·
                  refine ⟨1645511516079560094062221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8776061419090987168331845 1645511516079560094062221)
                  ·
                    refine ⟨617066818529835035273333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1645511516079560094062221 617066818529835035273333)
                    ·
                      rfl

theorem cell22_1802600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 2, 4, 3].length) (baseStart_1802600 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1802600 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1802600 prefixEnd_1802600 := by exact prefixLift 1802600
  have htrace : WordTrace (prefixWord ++ tailWord_1802600) baseStart_1802600 baseEnd_1802600 := by
    simpa [prefixWord, tailWord_1802600, baseEnd_1802600] using wordTrace_append hprefix tailTrace_1802600
  have hstable : (prefixWord ++ tailWord_1802600).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1802600).length < 2 ^ (prefixWord ++ tailWord_1802600).sum := by decide
  have hdescent : baseEnd_1802600 < baseStart_1802600 := by decide
  rcases family_descends (prefixWord ++ tailWord_1802600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1802602 : List Nat := [3, 1, 3, 3, 1, 1, 3, 3, 4]
def baseStart_1802602 : Nat := 118140960795 + 1802602 * 2 ^ 59
def prefixEnd_1802602 : Nat := 4983230072969 + 3 ^ 40 * 1802602 * 2
def baseEnd_1802602 : Nat := 205689167723569232241109

theorem tailTrace_1802602 : CollatzResearch.WordTrace tailWord_1802602 prefixEnd_1802602 205689167723569232241109 := by
  unfold tailWord_1802602
  simp only [CollatzResearch.WordTrace]
  refine ⟨16436574053872072189182515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43830864143658859171153373 16436574053872072189182515)
  ·
    refine ⟨24654861080808108283773773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16436574053872072189182515 24654861080808108283773773)
    ·
      refine ⟨9245572905303040606415165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24654861080808108283773773 9245572905303040606415165)
      ·
        refine ⟨3467089839488640227405687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9245572905303040606415165 3467089839488640227405687)
        ·
          refine ⟨5200634759232960341108531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3467089839488640227405687 5200634759232960341108531)
          ·
            refine ⟨7800952138849440511662797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5200634759232960341108531 7800952138849440511662797)
            ·
              refine ⟨2925357052068540191873549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7800952138849440511662797 2925357052068540191873549)
              ·
                refine ⟨1097008894525702571952581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2925357052068540191873549 1097008894525702571952581)
                ·
                  refine ⟨205689167723569232241109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1097008894525702571952581 205689167723569232241109)
                  ·
                    rfl

theorem cell22_1802602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 3, 3, 4].length) (baseStart_1802602 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1802602 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1802602 prefixEnd_1802602 := by exact prefixLift 1802602
  have htrace : WordTrace (prefixWord ++ tailWord_1802602) baseStart_1802602 baseEnd_1802602 := by
    simpa [prefixWord, tailWord_1802602, baseEnd_1802602] using wordTrace_append hprefix tailTrace_1802602
  have hstable : (prefixWord ++ tailWord_1802602).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1802602).length < 2 ^ (prefixWord ++ tailWord_1802602).sum := by decide
  have hdescent : baseEnd_1802602 < baseStart_1802602 := by decide
  rcases family_descends (prefixWord ++ tailWord_1802602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1802611 : List Nat := [1, 1, 1, 2, 2, 1, 2, 2, 1, 9]
def baseStart_1802611 : Nat := 118140960795 + 1802611 * 2 ^ 59
def prefixEnd_1802611 : Nat := 4983230072969 + 3 ^ 40 * 1802611 * 2
def baseEnd_1802611 : Nat := 617070584054634673248299

theorem tailTrace_1802611 : CollatzResearch.WordTrace tailWord_1802611 prefixEnd_1802611 617070584054634673248299 := by
  unfold tailWord_1802611
  simp only [CollatzResearch.WordTrace]
  refine ⟨65746624472455683293807687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43831082981637122195871791 65746624472455683293807687)
  ·
    refine ⟨98619936708683524940711531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65746624472455683293807687 98619936708683524940711531)
    ·
      refine ⟨147929905063025287411067297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98619936708683524940711531 147929905063025287411067297)
      ·
        refine ⟨110947428797268965558300473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147929905063025287411067297 110947428797268965558300473)
        ·
          refine ⟨83210571597951724168725355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110947428797268965558300473 83210571597951724168725355)
          ·
            refine ⟨124815857396927586253088033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83210571597951724168725355 124815857396927586253088033)
            ·
              refine ⟨93611893047695689689816025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 124815857396927586253088033 93611893047695689689816025)
              ·
                refine ⟨70208919785771767267362019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93611893047695689689816025 70208919785771767267362019)
                ·
                  refine ⟨105313379678657650901043029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70208919785771767267362019 105313379678657650901043029)
                  ·
                    refine ⟨617070584054634673248299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 105313379678657650901043029 617070584054634673248299)
                    ·
                      rfl

theorem cell22_1802611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 2, 1, 9].length) (baseStart_1802611 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1802611 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1802611 prefixEnd_1802611 := by exact prefixLift 1802611
  have htrace : WordTrace (prefixWord ++ tailWord_1802611) baseStart_1802611 baseEnd_1802611 := by
    simpa [prefixWord, tailWord_1802611, baseEnd_1802611] using wordTrace_append hprefix tailTrace_1802611
  have hstable : (prefixWord ++ tailWord_1802611).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1802611).length < 2 ^ (prefixWord ++ tailWord_1802611).sum := by decide
  have hdescent : baseEnd_1802611 < baseStart_1802611 := by decide
  rcases family_descends (prefixWord ++ tailWord_1802611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1802613 : List Nat := [1, 3, 4, 1, 2, 1, 10]
def baseStart_1802613 : Nat := 118140960795 + 1802613 * 2 ^ 59
def prefixEnd_1802613 : Nat := 4983230072969 + 3 ^ 40 * 1802613 * 2
def baseEnd_1802613 : Nat := 22854491433166938322159

theorem tailTrace_1802613 : CollatzResearch.WordTrace tailWord_1802613 prefixEnd_1802613 22854491433166938322159 := by
  unfold tailWord_1802613
  simp only [CollatzResearch.WordTrace]
  refine ⟨65746697418448437635380493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43831131612298958423586995 65746697418448437635380493)
  ·
    refine ⟨24655011531918164113267685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65746697418448437635380493 24655011531918164113267685)
    ·
      refine ⟨4622814662234655771237691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24655011531918164113267685 4622814662234655771237691)
      ·
        refine ⟨6934221993351983656856537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4622814662234655771237691 6934221993351983656856537)
        ·
          refine ⟨5200666495013987742642403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6934221993351983656856537 5200666495013987742642403)
          ·
            refine ⟨7800999742520981613963605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5200666495013987742642403 7800999742520981613963605)
            ·
              refine ⟨22854491433166938322159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 7800999742520981613963605 22854491433166938322159)
              ·
                rfl

theorem cell22_1802613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 10].length) (baseStart_1802613 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1802613 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1802613 prefixEnd_1802613 := by exact prefixLift 1802613
  have htrace : WordTrace (prefixWord ++ tailWord_1802613) baseStart_1802613 baseEnd_1802613 := by
    simpa [prefixWord, tailWord_1802613, baseEnd_1802613] using wordTrace_append hprefix tailTrace_1802613
  have hstable : (prefixWord ++ tailWord_1802613).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1802613).length < 2 ^ (prefixWord ++ tailWord_1802613).sum := by decide
  have hdescent : baseEnd_1802613 < baseStart_1802613 := by decide
  rcases family_descends (prefixWord ++ tailWord_1802613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1802634 : List Nat := [3, 1, 2, 5, 1, 1, 1, 3, 2, 3]
def baseStart_1802634 : Nat := 118140960795 + 1802634 * 2 ^ 59
def prefixEnd_1802634 : Nat := 4983230072969 + 3 ^ 40 * 1802634 * 2
def baseEnd_1802634 : Nat := 617078457424670279923229

theorem tailTrace_1802634 : CollatzResearch.WordTrace tailWord_1802634 prefixEnd_1802634 617078457424670279923229 := by
  unfold tailWord_1802634
  simp only [CollatzResearch.WordTrace]
  refine ⟨16436865837843089555473739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43831642234248238814596637 16436865837843089555473739)
  ·
    refine ⟨24655298756764634333210609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16436865837843089555473739 24655298756764634333210609)
    ·
      refine ⟨18491474067573475749907957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24655298756764634333210609 18491474067573475749907957)
      ·
        refine ⟨1733575693835013351553871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 18491474067573475749907957 1733575693835013351553871)
        ·
          refine ⟨2600363540752520027330807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1733575693835013351553871 2600363540752520027330807)
          ·
            refine ⟨3900545311128780040996211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2600363540752520027330807 3900545311128780040996211)
            ·
              refine ⟨5850817966693170061494317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3900545311128780040996211 5850817966693170061494317)
              ·
                refine ⟨2194056737509938773060369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5850817966693170061494317 2194056737509938773060369)
                ·
                  refine ⟨1645542553132454079795277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2194056737509938773060369 1645542553132454079795277)
                  ·
                    refine ⟨617078457424670279923229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1645542553132454079795277 617078457424670279923229)
                    ·
                      rfl

theorem cell22_1802634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 1, 3, 2, 3].length) (baseStart_1802634 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1802634 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1802634 prefixEnd_1802634 := by exact prefixLift 1802634
  have htrace : WordTrace (prefixWord ++ tailWord_1802634) baseStart_1802634 baseEnd_1802634 := by
    simpa [prefixWord, tailWord_1802634, baseEnd_1802634] using wordTrace_append hprefix tailTrace_1802634
  have hstable : (prefixWord ++ tailWord_1802634).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1802634).length < 2 ^ (prefixWord ++ tailWord_1802634).sum := by decide
  have hdescent : baseEnd_1802634 < baseStart_1802634 := by decide
  rcases family_descends (prefixWord ++ tailWord_1802634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1802679 : List Nat := [1, 1, 3, 1, 3, 3, 4, 2, 1, 3]
def baseStart_1802679 : Nat := 118140960795 + 1802679 * 2 ^ 59
def prefixEnd_1802679 : Nat := 4983230072969 + 3 ^ 40 * 1802679 * 2
def baseEnd_1802679 : Nat := 617093861844305162548091

theorem tailTrace_1802679 : CollatzResearch.WordTrace tailWord_1802679 prefixEnd_1802679 617093861844305162548091 := by
  unfold tailWord_1802679
  simp only [CollatzResearch.WordTrace]
  refine ⟨65749104636209330907283091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43832736424139553938188727 65749104636209330907283091)
  ·
    refine ⟨98623656954313996360924637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65749104636209330907283091 98623656954313996360924637)
    ·
      refine ⟨36983871357867748635346739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98623656954313996360924637 36983871357867748635346739)
      ·
        refine ⟨55475807036801622953020109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36983871357867748635346739 55475807036801622953020109)
        ·
          refine ⟨20803427638800608607382541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55475807036801622953020109 20803427638800608607382541)
          ·
            refine ⟨7801285364550228227768453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20803427638800608607382541 7801285364550228227768453)
            ·
              refine ⟨1462741005853167792706585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7801285364550228227768453 1462741005853167792706585)
              ·
                refine ⟨1097055754389875844529939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1462741005853167792706585 1097055754389875844529939)
                ·
                  refine ⟨1645583631584813766794909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1097055754389875844529939 1645583631584813766794909)
                  ·
                    refine ⟨617093861844305162548091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1645583631584813766794909 617093861844305162548091)
                    ·
                      rfl

theorem cell22_1802679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 4, 2, 1, 3].length) (baseStart_1802679 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1802679 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1802679 prefixEnd_1802679 := by exact prefixLift 1802679
  have htrace : WordTrace (prefixWord ++ tailWord_1802679) baseStart_1802679 baseEnd_1802679 := by
    simpa [prefixWord, tailWord_1802679, baseEnd_1802679] using wordTrace_append hprefix tailTrace_1802679
  have hstable : (prefixWord ++ tailWord_1802679).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1802679).length < 2 ^ (prefixWord ++ tailWord_1802679).sum := by decide
  have hdescent : baseEnd_1802679 < baseStart_1802679 := by decide
  rcases family_descends (prefixWord ++ tailWord_1802679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1802748 : List Nat := [2, 2, 2, 1, 2, 1, 1, 11]
def baseStart_1802748 : Nat := 118140960795 + 1802748 * 2 ^ 59
def prefixEnd_1802748 : Nat := 4983230072969 + 3 ^ 40 * 1802748 * 2
def baseEnd_1802748 : Nat := 68568609106045775841431

theorem tailTrace_1802748 : CollatzResearch.WordTrace tailWord_1802748 prefixEnd_1802748 68568609106045775841431 := by
  unfold tailWord_1802748
  simp only [CollatzResearch.WordTrace]
  refine ⟨32875810636479677845772449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43834414181972903794363265 32875810636479677845772449)
  ·
    refine ⟨24656857977359758384329337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32875810636479677845772449 24656857977359758384329337)
    ·
      refine ⟨18492643483019818788247003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24656857977359758384329337 18492643483019818788247003)
      ·
        refine ⟨27738965224529728182370505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18492643483019818788247003 27738965224529728182370505)
        ·
          refine ⟨20804223918397296136777879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27738965224529728182370505 20804223918397296136777879)
          ·
            refine ⟨31206335877595944205166819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20804223918397296136777879 31206335877595944205166819)
            ·
              refine ⟨46809503816393916307750229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31206335877595944205166819 46809503816393916307750229)
              ·
                refine ⟨68568609106045775841431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 46809503816393916307750229 68568609106045775841431)
                ·
                  rfl

theorem cell22_1802748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 11].length) (baseStart_1802748 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1802748 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1802748 prefixEnd_1802748 := by exact prefixLift 1802748
  have htrace : WordTrace (prefixWord ++ tailWord_1802748) baseStart_1802748 baseEnd_1802748 := by
    simpa [prefixWord, tailWord_1802748, baseEnd_1802748] using wordTrace_append hprefix tailTrace_1802748
  have hstable : (prefixWord ++ tailWord_1802748).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1802748).length < 2 ^ (prefixWord ++ tailWord_1802748).sum := by decide
  have hdescent : baseEnd_1802748 < baseStart_1802748 := by decide
  rcases family_descends (prefixWord ++ tailWord_1802748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1802844 : List Nat := [2, 2, 4, 1, 3, 1, 2, 2, 5]
def baseStart_1802844 : Nat := 118140960795 + 1802844 * 2 ^ 59
def prefixEnd_1802844 : Nat := 4983230072969 + 3 ^ 40 * 1802844 * 2
def baseEnd_1802844 : Nat := 205716781572099910724195

theorem tailTrace_1802844 : CollatzResearch.WordTrace tailWord_1802844 prefixEnd_1802844 205716781572099910724195 := by
  unfold tailWord_1802844
  simp only [CollatzResearch.WordTrace]
  refine ⟨32877561340305782043519793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43836748453741042724693057 32877561340305782043519793)
  ·
    refine ⟨24658171005229336532639845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32877561340305782043519793 24658171005229336532639845)
    ·
      refine ⟨4623407063480500599869971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24658171005229336532639845 4623407063480500599869971)
      ·
        refine ⟨6935110595220750899804957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4623407063480500599869971 6935110595220750899804957)
        ·
          refine ⟨2600666473207781587426859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6935110595220750899804957 2600666473207781587426859)
          ·
            refine ⟨3900999709811672381140289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2600666473207781587426859 3900999709811672381140289)
            ·
              refine ⟨2925749782358754285855217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3900999709811672381140289 2925749782358754285855217)
              ·
                refine ⟨2194312336769065714391413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2925749782358754285855217 2194312336769065714391413)
                ·
                  refine ⟨205716781572099910724195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2194312336769065714391413 205716781572099910724195)
                  ·
                    rfl

theorem cell22_1802844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 2, 2, 5].length) (baseStart_1802844 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1802844 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1802844 prefixEnd_1802844 := by exact prefixLift 1802844
  have htrace : WordTrace (prefixWord ++ tailWord_1802844) baseStart_1802844 baseEnd_1802844 := by
    simpa [prefixWord, tailWord_1802844, baseEnd_1802844] using wordTrace_append hprefix tailTrace_1802844
  have hstable : (prefixWord ++ tailWord_1802844).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1802844).length < 2 ^ (prefixWord ++ tailWord_1802844).sum := by decide
  have hdescent : baseEnd_1802844 < baseStart_1802844 := by decide
  rcases family_descends (prefixWord ++ tailWord_1802844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1802855 : List Nat := [1, 1, 5, 1, 1, 1, 1, 5, 6]
def baseStart_1802855 : Nat := 118140960795 + 1802855 * 2 ^ 59
def prefixEnd_1802855 : Nat := 4983230072969 + 3 ^ 40 * 1802855 * 2
def baseEnd_1802855 : Nat := 205718036747033123382517

theorem tailTrace_1802855 : CollatzResearch.WordTrace tailWord_1802855 prefixEnd_1802855 205718036747033123382517 := by
  unfold tailWord_1802855
  simp only [CollatzResearch.WordTrace]
  refine ⟨65755523883571712965690019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43837015922381141977126679 65755523883571712965690019)
  ·
    refine ⟨98633285825357569448535029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65755523883571712965690019 98633285825357569448535029)
    ·
      refine ⟨9246870546127272135800159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 98633285825357569448535029 9246870546127272135800159)
      ·
        refine ⟨13870305819190908203700239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9246870546127272135800159 13870305819190908203700239)
        ·
          refine ⟨20805458728786362305550359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13870305819190908203700239 20805458728786362305550359)
          ·
            refine ⟨31208188093179543458325539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20805458728786362305550359 31208188093179543458325539)
            ·
              refine ⟨46812282139769315187488309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31208188093179543458325539 46812282139769315187488309)
              ·
                refine ⟨4388651450603373298827029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46812282139769315187488309 4388651450603373298827029)
                ·
                  refine ⟨205718036747033123382517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4388651450603373298827029 205718036747033123382517)
                  ·
                    rfl

theorem cell22_1802855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 5, 6].length) (baseStart_1802855 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1802855 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1802855 prefixEnd_1802855 := by exact prefixLift 1802855
  have htrace : WordTrace (prefixWord ++ tailWord_1802855) baseStart_1802855 baseEnd_1802855 := by
    simpa [prefixWord, tailWord_1802855, baseEnd_1802855] using wordTrace_append hprefix tailTrace_1802855
  have hstable : (prefixWord ++ tailWord_1802855).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1802855).length < 2 ^ (prefixWord ++ tailWord_1802855).sum := by decide
  have hdescent : baseEnd_1802855 < baseStart_1802855 := by decide
  rcases family_descends (prefixWord ++ tailWord_1802855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1802882 : List Nat := [3, 4, 3, 1, 1, 1, 2, 3, 1, 3]
def baseStart_1802882 : Nat := 118140960795 + 1802882 * 2 ^ 59
def prefixEnd_1802882 : Nat := 4983230072969 + 3 ^ 40 * 1802882 * 2
def baseEnd_1802882 : Nat := 617163352892880299722469

theorem tailTrace_1802882 : CollatzResearch.WordTrace tailWord_1802882 prefixEnd_1802882 617163352892880299722469 := by
  unfold tailWord_1802882
  simp only [CollatzResearch.WordTrace]
  refine ⟨16439127163618474144230725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43837672436315931051281933 16439127163618474144230725)
  ·
    refine ⟨3082336343178463902043261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16439127163618474144230725 3082336343178463902043261)
    ·
      refine ⟨1155876128691923963266223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3082336343178463902043261 1155876128691923963266223)
      ·
        refine ⟨1733814193037885944899335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1155876128691923963266223 1733814193037885944899335)
        ·
          refine ⟨2600721289556828917349003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1733814193037885944899335 2600721289556828917349003)
          ·
            refine ⟨3901081934335243376023505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2600721289556828917349003 3901081934335243376023505)
            ·
              refine ⟨2925811450751432532017629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3901081934335243376023505 2925811450751432532017629)
              ·
                refine ⟨1097179294031787199506611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2925811450751432532017629 1097179294031787199506611)
                ·
                  refine ⟨1645768941047680799259917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1097179294031787199506611 1645768941047680799259917)
                  ·
                    refine ⟨617163352892880299722469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1645768941047680799259917 617163352892880299722469)
                    ·
                      rfl

theorem cell22_1802882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 2, 3, 1, 3].length) (baseStart_1802882 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1802882 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1802882 prefixEnd_1802882 := by exact prefixLift 1802882
  have htrace : WordTrace (prefixWord ++ tailWord_1802882) baseStart_1802882 baseEnd_1802882 := by
    simpa [prefixWord, tailWord_1802882, baseEnd_1802882] using wordTrace_append hprefix tailTrace_1802882
  have hstable : (prefixWord ++ tailWord_1802882).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1802882).length < 2 ^ (prefixWord ++ tailWord_1802882).sum := by decide
  have hdescent : baseEnd_1802882 < baseStart_1802882 := by decide
  rcases family_descends (prefixWord ++ tailWord_1802882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1802887 : List Nat := [1, 1, 4, 2, 1, 2, 2, 2, 4, 3]
def baseStart_1802887 : Nat := 118140960795 + 1802887 * 2 ^ 59
def prefixEnd_1802887 : Nat := 4983230072969 + 3 ^ 40 * 1802887 * 2
def baseEnd_1802887 : Nat := 617165064495061953347453

theorem tailTrace_1802887 : CollatzResearch.WordTrace tailWord_1802887 prefixEnd_1802887 617165064495061953347453 := by
  unfold tailWord_1802887
  simp only [CollatzResearch.WordTrace]
  refine ⟨65756691019455782430854915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43837794012970521620569943 65756691019455782430854915)
  ·
    refine ⟨98635036529183673646282373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65756691019455782430854915 98635036529183673646282373)
    ·
      refine ⟨18494069349221938808677945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 98635036529183673646282373 18494069349221938808677945)
      ·
        refine ⟨13870552011916454106508459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18494069349221938808677945 13870552011916454106508459)
        ·
          refine ⟨20805828017874681159762689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13870552011916454106508459 20805828017874681159762689)
          ·
            refine ⟨15604371013406010869822017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20805828017874681159762689 15604371013406010869822017)
            ·
              refine ⟨11703278260054508152366513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15604371013406010869822017 11703278260054508152366513)
              ·
                refine ⟨8777458695040881114274885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11703278260054508152366513 8777458695040881114274885)
                ·
                  refine ⟨1645773505320165208926541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8777458695040881114274885 1645773505320165208926541)
                  ·
                    refine ⟨617165064495061953347453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1645773505320165208926541 617165064495061953347453)
                    ·
                      rfl

theorem cell22_1802887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 2, 4, 3].length) (baseStart_1802887 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1802887 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1802887 prefixEnd_1802887 := by exact prefixLift 1802887
  have htrace : WordTrace (prefixWord ++ tailWord_1802887) baseStart_1802887 baseEnd_1802887 := by
    simpa [prefixWord, tailWord_1802887, baseEnd_1802887] using wordTrace_append hprefix tailTrace_1802887
  have hstable : (prefixWord ++ tailWord_1802887).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1802887).length < 2 ^ (prefixWord ++ tailWord_1802887).sum := by decide
  have hdescent : baseEnd_1802887 < baseStart_1802887 := by decide
  rcases family_descends (prefixWord ++ tailWord_1802887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1802979 : List Nat := [1, 1, 1, 7, 1, 2, 1, 3, 5]
def baseStart_1802979 : Nat := 118140960795 + 1802979 * 2 ^ 59
def prefixEnd_1802979 : Nat := 4983230072969 + 3 ^ 40 * 1802979 * 2
def baseEnd_1802979 : Nat := 205732185991734793349057

theorem tailTrace_1802979 : CollatzResearch.WordTrace tailWord_1802979 prefixEnd_1802979 205732185991734793349057 := by
  unfold tailWord_1802979
  simp only [CollatzResearch.WordTrace]
  refine ⟨65760046535122482143203991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43840031023414988095469327 65760046535122482143203991)
  ·
    refine ⟨98640069802683723214805987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65760046535122482143203991 98640069802683723214805987)
    ·
      refine ⟨147960104704025584822208981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98640069802683723214805987 147960104704025584822208981)
      ·
        refine ⟨3467814954000599644270523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 147960104704025584822208981 3467814954000599644270523)
        ·
          refine ⟨5201722431000899466405785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3467814954000599644270523 5201722431000899466405785)
          ·
            refine ⟨3901291823250674599804339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5201722431000899466405785 3901291823250674599804339)
            ·
              refine ⟨5851937734876011899706509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3901291823250674599804339 5851937734876011899706509)
              ·
                refine ⟨2194476650578504462389941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5851937734876011899706509 2194476650578504462389941)
                ·
                  refine ⟨205732185991734793349057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2194476650578504462389941 205732185991734793349057)
                  ·
                    rfl

theorem cell22_1802979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 1, 3, 5].length) (baseStart_1802979 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1802979 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1802979 prefixEnd_1802979 := by exact prefixLift 1802979
  have htrace : WordTrace (prefixWord ++ tailWord_1802979) baseStart_1802979 baseEnd_1802979 := by
    simpa [prefixWord, tailWord_1802979, baseEnd_1802979] using wordTrace_append hprefix tailTrace_1802979
  have hstable : (prefixWord ++ tailWord_1802979).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1802979).length < 2 ^ (prefixWord ++ tailWord_1802979).sum := by decide
  have hdescent : baseEnd_1802979 < baseStart_1802979 := by decide
  rcases family_descends (prefixWord ++ tailWord_1802979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1802992 : List Nat := [2, 1, 1, 1, 3, 1, 5, 1, 3, 4]
def baseStart_1802992 : Nat := 118140960795 + 1802992 * 2 ^ 59
def prefixEnd_1802992 : Nat := 4983230072969 + 3 ^ 40 * 1802992 * 2
def baseEnd_1802992 : Nat := 617201008140876679472131

theorem tailTrace_1802992 : CollatzResearch.WordTrace tailWord_1802992 prefixEnd_1802992 617201008140876679472131 := by
  unfold tailWord_1802992
  simp only [CollatzResearch.WordTrace]
  refine ⟨32880260342037692681713615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43840347122716923575618153 32880260342037692681713615)
  ·
    refine ⟨49320390513056539022570423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32880260342037692681713615 49320390513056539022570423)
    ·
      refine ⟨73980585769584808533855635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49320390513056539022570423 73980585769584808533855635)
      ·
        refine ⟨110970878654377212800783453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73980585769584808533855635 110970878654377212800783453)
        ·
          refine ⟨41614079495391454800293795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 110970878654377212800783453 41614079495391454800293795)
          ·
            refine ⟨62421119243087182200440693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41614079495391454800293795 62421119243087182200440693)
            ·
              refine ⟨5851979929039423331291315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 62421119243087182200440693 5851979929039423331291315)
              ·
                refine ⟨8777969893559134996936973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5851979929039423331291315 8777969893559134996936973)
                ·
                  refine ⟨3291738710084675623851365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8777969893559134996936973 3291738710084675623851365)
                  ·
                    refine ⟨617201008140876679472131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3291738710084675623851365 617201008140876679472131)
                    ·
                      rfl

theorem cell22_1802992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 5, 1, 3, 4].length) (baseStart_1802992 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1802992 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1802992 prefixEnd_1802992 := by exact prefixLift 1802992
  have htrace : WordTrace (prefixWord ++ tailWord_1802992) baseStart_1802992 baseEnd_1802992 := by
    simpa [prefixWord, tailWord_1802992, baseEnd_1802992] using wordTrace_append hprefix tailTrace_1802992
  have hstable : (prefixWord ++ tailWord_1802992).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1802992).length < 2 ^ (prefixWord ++ tailWord_1802992).sum := by decide
  have hdescent : baseEnd_1802992 < baseStart_1802992 := by decide
  rcases family_descends (prefixWord ++ tailWord_1802992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1803022 : List Nat := [4, 1, 1, 2, 1, 1, 1, 1, 5, 5]
def baseStart_1803022 : Nat := 118140960795 + 1803022 * 2 ^ 59
def prefixEnd_1803022 : Nat := 4983230072969 + 3 ^ 40 * 1803022 * 2
def baseEnd_1803022 : Nat := 617211277753966601222039

theorem tailTrace_1803022 : CollatzResearch.WordTrace tailWord_1803022 prefixEnd_1803022 617211277753966601222039 := by
  unfold tailWord_1803022
  simp only [CollatzResearch.WordTrace]
  refine ⟨8220201859245837560877415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43841076582644466991346213 8220201859245837560877415)
  ·
    refine ⟨12330302788868756341316123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8220201859245837560877415 12330302788868756341316123)
    ·
      refine ⟨18495454183303134511974185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12330302788868756341316123 18495454183303134511974185)
      ·
        refine ⟨13871590637477350883980639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18495454183303134511974185 13871590637477350883980639)
        ·
          refine ⟨20807385956216026325970959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13871590637477350883980639 20807385956216026325970959)
          ·
            refine ⟨31211078934324039488956439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20807385956216026325970959 31211078934324039488956439)
            ·
              refine ⟨46816618401486059233434659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31211078934324039488956439 46816618401486059233434659)
              ·
                refine ⟨70224927602229088850151989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46816618401486059233434659 70224927602229088850151989)
                ·
                  refine ⟨6583586962708977079701749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 70224927602229088850151989 6583586962708977079701749)
                  ·
                    refine ⟨617211277753966601222039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6583586962708977079701749 617211277753966601222039)
                    ·
                      rfl

theorem cell22_1803022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 1, 5, 5].length) (baseStart_1803022 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1803022 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1803022 prefixEnd_1803022 := by exact prefixLift 1803022
  have htrace : WordTrace (prefixWord ++ tailWord_1803022) baseStart_1803022 baseEnd_1803022 := by
    simpa [prefixWord, tailWord_1803022, baseEnd_1803022] using wordTrace_append hprefix tailTrace_1803022
  have hstable : (prefixWord ++ tailWord_1803022).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1803022).length < 2 ^ (prefixWord ++ tailWord_1803022).sum := by decide
  have hdescent : baseEnd_1803022 < baseStart_1803022 := by decide
  rcases family_descends (prefixWord ++ tailWord_1803022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1803039 : List Nat := [1, 1, 2, 4, 2, 3, 2, 1, 1, 5]
def baseStart_1803039 : Nat := 118140960795 + 1803039 * 2 ^ 59
def prefixEnd_1803039 : Nat := 4983230072969 + 3 ^ 40 * 1803039 * 2
def baseEnd_1803039 : Nat := 617217097201384223546987

theorem tailTrace_1803039 : CollatzResearch.WordTrace tailWord_1803039 prefixEnd_1803039 617217097201384223546987 := by
  unfold tailWord_1803039
  simp only [CollatzResearch.WordTrace]
  refine ⟨65762234914905112390388171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43841489943270074926925447 65762234914905112390388171)
  ·
    refine ⟨98643352372357668585582257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65762234914905112390388171 98643352372357668585582257)
    ·
      refine ⟨73982514279268251439186693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98643352372357668585582257 73982514279268251439186693)
      ·
        refine ⟨13871721427362797144847505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 73982514279268251439186693 13871721427362797144847505)
        ·
          refine ⟨10403791070522097858635629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13871721427362797144847505 10403791070522097858635629)
          ·
            refine ⟨3901421651445786696988361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10403791070522097858635629 3901421651445786696988361)
            ·
              refine ⟨2926066238584340022741271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3901421651445786696988361 2926066238584340022741271)
              ·
                refine ⟨4389099357876510034111907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2926066238584340022741271 4389099357876510034111907)
                ·
                  refine ⟨6583649036814765051167861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4389099357876510034111907 6583649036814765051167861)
                  ·
                    refine ⟨617217097201384223546987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6583649036814765051167861 617217097201384223546987)
                    ·
                      rfl

theorem cell22_1803039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 2, 1, 1, 5].length) (baseStart_1803039 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1803039 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1803039 prefixEnd_1803039 := by exact prefixLift 1803039
  have htrace : WordTrace (prefixWord ++ tailWord_1803039) baseStart_1803039 baseEnd_1803039 := by
    simpa [prefixWord, tailWord_1803039, baseEnd_1803039] using wordTrace_append hprefix tailTrace_1803039
  have hstable : (prefixWord ++ tailWord_1803039).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1803039).length < 2 ^ (prefixWord ++ tailWord_1803039).sum := by decide
  have hdescent : baseEnd_1803039 < baseStart_1803039 := by decide
  rcases family_descends (prefixWord ++ tailWord_1803039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1803060 : List Nat := [2, 5, 1, 1, 3, 2, 2, 1, 1, 4]
def baseStart_1803060 : Nat := 118140960795 + 1803060 * 2 ^ 59
def prefixEnd_1803060 : Nat := 4983230072969 + 3 ^ 40 * 1803060 * 2
def baseEnd_1803060 : Nat := 617224285930547168771923

theorem tailTrace_1803060 : CollatzResearch.WordTrace tailWord_1803060 prefixEnd_1803060 617224285930547168771923 := by
  unfold tailWord_1803060
  simp only [CollatzResearch.WordTrace]
  refine ⟨32881500423914516488451317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43842000565219355317935089 32881500423914516488451317)
  ·
    refine ⟨3082640664741985920792311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 32881500423914516488451317 3082640664741985920792311)
    ·
      refine ⟨4623960997112978881188467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3082640664741985920792311 4623960997112978881188467)
      ·
        refine ⟨6935941495669468321782701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4623960997112978881188467 6935941495669468321782701)
        ·
          refine ⟨2600978060876050620668513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6935941495669468321782701 2600978060876050620668513)
          ·
            refine ⟨1950733545657037965501385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2600978060876050620668513 1950733545657037965501385)
            ·
              refine ⟨1463050159242778474126039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1950733545657037965501385 1463050159242778474126039)
              ·
                refine ⟨2194575238864167711189059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1463050159242778474126039 2194575238864167711189059)
                ·
                  refine ⟨3291862858296251566783589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2194575238864167711189059 3291862858296251566783589)
                  ·
                    refine ⟨617224285930547168771923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3291862858296251566783589 617224285930547168771923)
                    ·
                      rfl

theorem cell22_1803060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 2, 2, 1, 1, 4].length) (baseStart_1803060 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1803060 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1803060 prefixEnd_1803060 := by exact prefixLift 1803060
  have htrace : WordTrace (prefixWord ++ tailWord_1803060) baseStart_1803060 baseEnd_1803060 := by
    simpa [prefixWord, tailWord_1803060, baseEnd_1803060] using wordTrace_append hprefix tailTrace_1803060
  have hstable : (prefixWord ++ tailWord_1803060).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1803060).length < 2 ^ (prefixWord ++ tailWord_1803060).sum := by decide
  have hdescent : baseEnd_1803060 < baseStart_1803060 := by decide
  rcases family_descends (prefixWord ++ tailWord_1803060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1803069 : List Nat := [1, 4, 1, 4, 2, 1, 9]
def baseStart_1803069 : Nat := 118140960795 + 1803069 * 2 ^ 59
def prefixEnd_1803069 : Nat := 4983230072969 + 3 ^ 40 * 1803069 * 2
def baseEnd_1803069 : Nat := 22860272844980523899885

theorem tailTrace_1803069 : CollatzResearch.WordTrace tailWord_1803069 prefixEnd_1803069 22860272844980523899885 := by
  unfold tailWord_1803069
  simp only [CollatzResearch.WordTrace]
  refine ⟨65763329104796427513980261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43842219403197618342653507 65763329104796427513980261)
  ·
    refine ⟨12330624207149330158871299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65763329104796427513980261 12330624207149330158871299)
    ·
      refine ⟨18495936310723995238306949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12330624207149330158871299 18495936310723995238306949)
      ·
        refine ⟨3467988058260749107182553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18495936310723995238306949 3467988058260749107182553)
        ·
          refine ⟨2600991043695561830386915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3467988058260749107182553 2600991043695561830386915)
          ·
            refine ⟨3901486565543342745580373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2600991043695561830386915 3901486565543342745580373)
            ·
              refine ⟨22860272844980523899885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3901486565543342745580373 22860272844980523899885)
              ·
                rfl

theorem cell22_1803069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 9].length) (baseStart_1803069 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1803069 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1803069 prefixEnd_1803069 := by exact prefixLift 1803069
  have htrace : WordTrace (prefixWord ++ tailWord_1803069) baseStart_1803069 baseEnd_1803069 := by
    simpa [prefixWord, tailWord_1803069, baseEnd_1803069] using wordTrace_append hprefix tailTrace_1803069
  have hstable : (prefixWord ++ tailWord_1803069).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1803069).length < 2 ^ (prefixWord ++ tailWord_1803069).sum := by decide
  have hdescent : baseEnd_1803069 < baseStart_1803069 := by decide
  rcases family_descends (prefixWord ++ tailWord_1803069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1803073 : List Nat := [1, 2, 5, 3, 1, 1, 1, 1, 4, 3]
def baseStart_1803073 : Nat := 118140960795 + 1803073 * 2 ^ 59
def prefixEnd_1803073 : Nat := 4983230072969 + 3 ^ 40 * 1803073 * 2
def baseEnd_1803073 : Nat := 617228736096219468196883

theorem tailTrace_1803073 : CollatzResearch.WordTrace tailWord_1803073 prefixEnd_1803073 617228736096219468196883 := by
  unfold tailWord_1803073
  simp only [CollatzResearch.WordTrace]
  refine ⟨65763474996781936197125873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43842316664521290798083915 65763474996781936197125873)
  ·
    refine ⟨49322606247586452147844405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65763474996781936197125873 49322606247586452147844405)
    ·
      refine ⟨4623994335711229888860413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 49322606247586452147844405 4623994335711229888860413)
      ·
        refine ⟨1733997875891711208322655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4623994335711229888860413 1733997875891711208322655)
        ·
          refine ⟨2600996813837566812483983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1733997875891711208322655 2600996813837566812483983)
          ·
            refine ⟨3901495220756350218725975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2600996813837566812483983 3901495220756350218725975)
            ·
              refine ⟨5852242831134525328088963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3901495220756350218725975 5852242831134525328088963)
              ·
                refine ⟨8778364246701787992133445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5852242831134525328088963 8778364246701787992133445)
                ·
                  refine ⟨1645943296256585248525021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8778364246701787992133445 1645943296256585248525021)
                  ·
                    refine ⟨617228736096219468196883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1645943296256585248525021 617228736096219468196883)
                    ·
                      rfl

theorem cell22_1803073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 1, 1, 4, 3].length) (baseStart_1803073 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1803073 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1803073 prefixEnd_1803073 := by exact prefixLift 1803073
  have htrace : WordTrace (prefixWord ++ tailWord_1803073) baseStart_1803073 baseEnd_1803073 := by
    simpa [prefixWord, tailWord_1803073, baseEnd_1803073] using wordTrace_append hprefix tailTrace_1803073
  have hstable : (prefixWord ++ tailWord_1803073).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1803073).length < 2 ^ (prefixWord ++ tailWord_1803073).sum := by decide
  have hdescent : baseEnd_1803073 < baseStart_1803073 := by decide
  rcases family_descends (prefixWord ++ tailWord_1803073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1803082 : List Nat := [3, 1, 2, 1, 1, 1, 2, 3, 2, 6]
def baseStart_1803082 : Nat := 118140960795 + 1803082 * 2 ^ 59
def prefixEnd_1803082 : Nat := 4983230072969 + 3 ^ 40 * 1803082 * 2
def baseEnd_1803082 : Nat := 617231816980146444721855

theorem tailTrace_1803082 : CollatzResearch.WordTrace tailWord_1803082 prefixEnd_1803082 617231816980146444721855 := by
  unfold tailWord_1803082
  simp only [CollatzResearch.WordTrace]
  refine ⟨16440950813437332683550875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43842535502499553822802333 16440950813437332683550875)
  ·
    refine ⟨24661426220155999025326313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16440950813437332683550875 24661426220155999025326313)
    ·
      refine ⟨18496069665116999268994735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24661426220155999025326313 18496069665116999268994735)
      ·
        refine ⟨27744104497675498903492103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18496069665116999268994735 27744104497675498903492103)
        ·
          refine ⟨41616156746513248355238155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27744104497675498903492103 41616156746513248355238155)
          ·
            refine ⟨62424235119769872532857233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41616156746513248355238155 62424235119769872532857233)
            ·
              refine ⟨46818176339827404399642925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62424235119769872532857233 46818176339827404399642925)
              ·
                refine ⟨17556816127435276649866097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46818176339827404399642925 17556816127435276649866097)
                ·
                  refine ⟨13167612095576457487399573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17556816127435276649866097 13167612095576457487399573)
                  ·
                    refine ⟨617231816980146444721855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13167612095576457487399573 617231816980146444721855)
                    ·
                      rfl

theorem cell22_1803082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 3, 2, 6].length) (baseStart_1803082 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1803082 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1803082 prefixEnd_1803082 := by exact prefixLift 1803082
  have htrace : WordTrace (prefixWord ++ tailWord_1803082) baseStart_1803082 baseEnd_1803082 := by
    simpa [prefixWord, tailWord_1803082, baseEnd_1803082] using wordTrace_append hprefix tailTrace_1803082
  have hstable : (prefixWord ++ tailWord_1803082).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1803082).length < 2 ^ (prefixWord ++ tailWord_1803082).sum := by decide
  have hdescent : baseEnd_1803082 < baseStart_1803082 := by decide
  rcases family_descends (prefixWord ++ tailWord_1803082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1803191 : List Nat := [1, 1, 3, 1, 3, 1, 3, 4, 2, 3]
def baseStart_1803191 : Nat := 118140960795 + 1803191 * 2 ^ 59
def prefixEnd_1803191 : Nat := 4983230072969 + 3 ^ 40 * 1803191 * 2
def baseEnd_1803191 : Nat := 617269129907706493746521

theorem tailTrace_1803191 : CollatzResearch.WordTrace tailWord_1803191 prefixEnd_1803191 617269129907706493746521 := by
  unfold tailWord_1803191
  simp only [CollatzResearch.WordTrace]
  refine ⟨65767778810354442349921427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43845185873569628233280951 65767778810354442349921427)
  ·
    refine ⟨98651668215531663524882141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65767778810354442349921427 98651668215531663524882141)
    ·
      refine ⟨36994375580824373821830803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98651668215531663524882141 36994375580824373821830803)
      ·
        refine ⟨55491563371236560732746205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36994375580824373821830803 55491563371236560732746205)
        ·
          refine ⟨20809336264213710274779827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55491563371236560732746205 20809336264213710274779827)
          ·
            refine ⟨31214004396320565412169741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20809336264213710274779827 31214004396320565412169741)
            ·
              refine ⟨11705251648620212029563653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31214004396320565412169741 11705251648620212029563653)
              ·
                refine ⟨2194734684116289755543185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11705251648620212029563653 2194734684116289755543185)
                ·
                  refine ⟨1646051013087217316657389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2194734684116289755543185 1646051013087217316657389)
                  ·
                    refine ⟨617269129907706493746521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1646051013087217316657389 617269129907706493746521)
                    ·
                      rfl

theorem cell22_1803191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 4, 2, 3].length) (baseStart_1803191 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1803191 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1803191 prefixEnd_1803191 := by exact prefixLift 1803191
  have htrace : WordTrace (prefixWord ++ tailWord_1803191) baseStart_1803191 baseEnd_1803191 := by
    simpa [prefixWord, tailWord_1803191, baseEnd_1803191] using wordTrace_append hprefix tailTrace_1803191
  have hstable : (prefixWord ++ tailWord_1803191).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1803191).length < 2 ^ (prefixWord ++ tailWord_1803191).sum := by decide
  have hdescent : baseEnd_1803191 < baseStart_1803191 := by decide
  rcases family_descends (prefixWord ++ tailWord_1803191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1803193 : List Nat := [1, 2, 1, 4, 2, 2, 4, 2, 4]
def baseStart_1803193 : Nat := 118140960795 + 1803193 * 2 ^ 59
def prefixEnd_1803193 : Nat := 4983230072969 + 3 ^ 40 * 1803193 * 2
def baseEnd_1803193 : Nat := 205756604849526385065505

theorem tailTrace_1803193 : CollatzResearch.WordTrace tailWord_1803193 prefixEnd_1803193 205756604849526385065505 := by
  unfold tailWord_1803193
  simp only [CollatzResearch.WordTrace]
  refine ⟨65767851756347196691494233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43845234504231464460996155 65767851756347196691494233)
  ·
    refine ⟨49325888817260397518620675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65767851756347196691494233 49325888817260397518620675)
    ·
      refine ⟨73988833225890596277931013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49325888817260397518620675 73988833225890596277931013)
      ·
        refine ⟨13872906229854486802112065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 73988833225890596277931013 13872906229854486802112065)
        ·
          refine ⟨10404679672390865101584049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13872906229854486802112065 10404679672390865101584049)
          ·
            refine ⟨7803509754293148826188037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10404679672390865101584049 7803509754293148826188037)
            ·
              refine ⟨1463158078929965404910257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7803509754293148826188037 1463158078929965404910257)
              ·
                refine ⟨1097368559197474053682693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1463158078929965404910257 1097368559197474053682693)
                ·
                  refine ⟨205756604849526385065505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1097368559197474053682693 205756604849526385065505)
                  ·
                    rfl

theorem cell22_1803193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 4, 2, 4].length) (baseStart_1803193 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1803193 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1803193 prefixEnd_1803193 := by exact prefixLift 1803193
  have htrace : WordTrace (prefixWord ++ tailWord_1803193) baseStart_1803193 baseEnd_1803193 := by
    simpa [prefixWord, tailWord_1803193, baseEnd_1803193] using wordTrace_append hprefix tailTrace_1803193
  have hstable : (prefixWord ++ tailWord_1803193).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1803193).length < 2 ^ (prefixWord ++ tailWord_1803193).sum := by decide
  have hdescent : baseEnd_1803193 < baseStart_1803193 := by decide
  rcases family_descends (prefixWord ++ tailWord_1803193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1803287 : List Nat := [1, 1, 3, 5, 1, 3, 1, 3, 1, 3]
def baseStart_1803287 : Nat := 118140960795 + 1803287 * 2 ^ 59
def prefixEnd_1803287 : Nat := 4983230072969 + 3 ^ 40 * 1803287 * 2
def baseEnd_1803287 : Nat := 617301992669594243346227

theorem tailTrace_1803287 : CollatzResearch.WordTrace tailWord_1803287 prefixEnd_1803287 617301992669594243346227 := by
  unfold tailWord_1803287
  simp only [CollatzResearch.WordTrace]
  refine ⟨65771280218006650745416115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43847520145337767163610743 65771280218006650745416115)
  ·
    refine ⟨98656920327009976118124173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65771280218006650745416115 98656920327009976118124173)
    ·
      refine ⟨36996345122628741044296565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98656920327009976118124173 36996345122628741044296565)
      ·
        refine ⟨3468407355246444472902803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 36996345122628741044296565 3468407355246444472902803)
        ·
          refine ⟨5202611032869666709354205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3468407355246444472902803 5202611032869666709354205)
          ·
            refine ⟨1950979137326125016007827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5202611032869666709354205 1950979137326125016007827)
            ·
              refine ⟨2926468705989187524011741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1950979137326125016007827 2926468705989187524011741)
              ·
                refine ⟨1097425764745945321504403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2926468705989187524011741 1097425764745945321504403)
                ·
                  refine ⟨1646138647118917982256605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1097425764745945321504403 1646138647118917982256605)
                  ·
                    refine ⟨617301992669594243346227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1646138647118917982256605 617301992669594243346227)
                    ·
                      rfl

theorem cell22_1803287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 3, 1, 3, 1, 3].length) (baseStart_1803287 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1803287 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1803287 prefixEnd_1803287 := by exact prefixLift 1803287
  have htrace : WordTrace (prefixWord ++ tailWord_1803287) baseStart_1803287 baseEnd_1803287 := by
    simpa [prefixWord, tailWord_1803287, baseEnd_1803287] using wordTrace_append hprefix tailTrace_1803287
  have hstable : (prefixWord ++ tailWord_1803287).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1803287).length < 2 ^ (prefixWord ++ tailWord_1803287).sum := by decide
  have hdescent : baseEnd_1803287 < baseStart_1803287 := by decide
  rcases family_descends (prefixWord ++ tailWord_1803287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1803362 : List Nat := [3, 3, 2, 2, 1, 1, 4, 2, 4]
def baseStart_1803362 : Nat := 118140960795 + 1803362 * 2 ^ 59
def prefixEnd_1803362 : Nat := 4983230072969 + 3 ^ 40 * 1803362 * 2
def baseEnd_1803362 : Nat := 205775888900773015906999

theorem tailTrace_1803362 : CollatzResearch.WordTrace tailWord_1803362 prefixEnd_1803362 205775888900773015906999 := by
  unfold tailWord_1803362
  simp only [CollatzResearch.WordTrace]
  refine ⟨16443503923183734638599085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43849343795156625702930893 16443503923183734638599085)
  ·
    refine ⟨6166313971193900489474657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16443503923183734638599085 6166313971193900489474657)
    ·
      refine ⟨4624735478395425367105993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6166313971193900489474657 4624735478395425367105993)
      ·
        refine ⟨3468551608796569025329495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4624735478395425367105993 3468551608796569025329495)
        ·
          refine ⟨5202827413194853537994243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3468551608796569025329495 5202827413194853537994243)
          ·
            refine ⟨7804241119792280306991365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5202827413194853537994243 7804241119792280306991365)
            ·
              refine ⟨1463295209961052557560881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7804241119792280306991365 1463295209961052557560881)
              ·
                refine ⟨1097471407470789418170661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1463295209961052557560881 1097471407470789418170661)
                ·
                  refine ⟨205775888900773015906999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1097471407470789418170661 205775888900773015906999)
                  ·
                    rfl

theorem cell22_1803362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 4, 2, 4].length) (baseStart_1803362 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1803362 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1803362 prefixEnd_1803362 := by exact prefixLift 1803362
  have htrace : WordTrace (prefixWord ++ tailWord_1803362) baseStart_1803362 baseEnd_1803362 := by
    simpa [prefixWord, tailWord_1803362, baseEnd_1803362] using wordTrace_append hprefix tailTrace_1803362
  have hstable : (prefixWord ++ tailWord_1803362).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1803362).length < 2 ^ (prefixWord ++ tailWord_1803362).sum := by decide
  have hdescent : baseEnd_1803362 < baseStart_1803362 := by decide
  rcases family_descends (prefixWord ++ tailWord_1803362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1803371 : List Nat := [1, 1, 1, 1, 2, 2, 1, 1, 9, 3]
def baseStart_1803371 : Nat := 118140960795 + 1803371 * 2 ^ 59
def prefixEnd_1803371 : Nat := 4983230072969 + 3 ^ 40 * 1803371 * 2
def baseEnd_1803371 : Nat := 617330747586246024245969

theorem tailTrace_1803371 : CollatzResearch.WordTrace tailWord_1803371 prefixEnd_1803371 617330747586246024245969 := by
  unfold tailWord_1803371
  simp only [CollatzResearch.WordTrace]
  refine ⟨65774343949702333091473967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43849562633134888727649311 65774343949702333091473967)
  ·
    refine ⟨98661515924553499637210951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65774343949702333091473967 98661515924553499637210951)
    ·
      refine ⟨147992273886830249455816427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98661515924553499637210951 147992273886830249455816427)
      ·
        refine ⟨221988410830245374183724641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147992273886830249455816427 221988410830245374183724641)
        ·
          refine ⟨166491308122684030637793481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 221988410830245374183724641 166491308122684030637793481)
          ·
            refine ⟨124868481092013022978345111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 166491308122684030637793481 124868481092013022978345111)
            ·
              refine ⟨187302721638019534467517667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124868481092013022978345111 187302721638019534467517667)
              ·
                refine ⟨280954082457029301701276501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 187302721638019534467517667 280954082457029301701276501)
                ·
                  refine ⟨1646215326896656064655917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 280954082457029301701276501 1646215326896656064655917)
                  ·
                    refine ⟨617330747586246024245969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1646215326896656064655917 617330747586246024245969)
                    ·
                      rfl

theorem cell22_1803371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 9, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 9, 3].length) (baseStart_1803371 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1803371 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1803371 prefixEnd_1803371 := by exact prefixLift 1803371
  have htrace : WordTrace (prefixWord ++ tailWord_1803371) baseStart_1803371 baseEnd_1803371 := by
    simpa [prefixWord, tailWord_1803371, baseEnd_1803371] using wordTrace_append hprefix tailTrace_1803371
  have hstable : (prefixWord ++ tailWord_1803371).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1803371).length < 2 ^ (prefixWord ++ tailWord_1803371).sum := by decide
  have hdescent : baseEnd_1803371 < baseStart_1803371 := by decide
  rcases family_descends (prefixWord ++ tailWord_1803371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1803373 : List Nat := [1, 5, 1, 1, 2, 4, 1, 7]
def baseStart_1803373 : Nat := 118140960795 + 1803373 * 2 ^ 59
def prefixEnd_1803373 : Nat := 4983230072969 + 3 ^ 40 * 1803373 * 2
def baseEnd_1803373 : Nat := 68592381358568742855107

theorem tailTrace_1803373 : CollatzResearch.WordTrace tailWord_1803373 prefixEnd_1803373 68592381358568742855107 := by
  unfold tailWord_1803373
  simp only [CollatzResearch.WordTrace]
  refine ⟨65774416895695087433046773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43849611263796724955364515 65774416895695087433046773)
  ·
    refine ⟨6166351583971414446848135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 65774416895695087433046773 6166351583971414446848135)
    ·
      refine ⟨9249527375957121670272203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6166351583971414446848135 9249527375957121670272203)
      ·
        refine ⟨13874291063935682505408305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9249527375957121670272203 13874291063935682505408305)
        ·
          refine ⟨10405718297951761879056229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13874291063935682505408305 10405718297951761879056229)
          ·
            refine ⟨1951072180865955352323043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10405718297951761879056229 1951072180865955352323043)
            ·
              refine ⟨2926608271298933028484565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1951072180865955352323043 2926608271298933028484565)
              ·
                refine ⟨68592381358568742855107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2926608271298933028484565 68592381358568742855107)
                ·
                  rfl

theorem cell22_1803373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 4, 1, 7].length) (baseStart_1803373 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1803373 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1803373 prefixEnd_1803373 := by exact prefixLift 1803373
  have htrace : WordTrace (prefixWord ++ tailWord_1803373) baseStart_1803373 baseEnd_1803373 := by
    simpa [prefixWord, tailWord_1803373, baseEnd_1803373] using wordTrace_append hprefix tailTrace_1803373
  have hstable : (prefixWord ++ tailWord_1803373).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1803373).length < 2 ^ (prefixWord ++ tailWord_1803373).sum := by decide
  have hdescent : baseEnd_1803373 < baseStart_1803373 := by decide
  rcases family_descends (prefixWord ++ tailWord_1803373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1803388 : List Nat := [2, 2, 2, 1, 1, 3, 3, 2, 3, 3]
def baseStart_1803388 : Nat := 118140960795 + 1803388 * 2 ^ 59
def prefixEnd_1803388 : Nat := 4983230072969 + 3 ^ 40 * 1803388 * 2
def baseEnd_1803388 : Nat := 617336567033663646570917

theorem tailTrace_1803388 : CollatzResearch.WordTrace tailWord_1803388 prefixEnd_1803388 617336567033663646570917 := by
  unfold tailWord_1803388
  simp only [CollatzResearch.WordTrace]
  refine ⟨32887481995320372497421409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43849975993760496663228545 32887481995320372497421409)
  ·
    refine ⟨24665611496490279373066057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32887481995320372497421409 24665611496490279373066057)
    ·
      refine ⟨18499208622367709529799543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24665611496490279373066057 18499208622367709529799543)
      ·
        refine ⟨27748812933551564294699315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18499208622367709529799543 27748812933551564294699315)
        ·
          refine ⟨41623219400327346442048973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27748812933551564294699315 41623219400327346442048973)
          ·
            refine ⟨15608707275122754915768365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41623219400327346442048973 15608707275122754915768365)
            ·
              refine ⟨5853265228171033093413137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15608707275122754915768365 5853265228171033093413137)
              ·
                refine ⟨4389948921128274820059853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5853265228171033093413137 4389948921128274820059853)
                ·
                  refine ⟨1646230845423103057522445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4389948921128274820059853 1646230845423103057522445)
                  ·
                    refine ⟨617336567033663646570917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1646230845423103057522445 617336567033663646570917)
                    ·
                      rfl

theorem cell22_1803388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 3, 2, 3, 3].length) (baseStart_1803388 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1803388 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1803388 prefixEnd_1803388 := by exact prefixLift 1803388
  have htrace : WordTrace (prefixWord ++ tailWord_1803388) baseStart_1803388 baseEnd_1803388 := by
    simpa [prefixWord, tailWord_1803388, baseEnd_1803388] using wordTrace_append hprefix tailTrace_1803388
  have hstable : (prefixWord ++ tailWord_1803388).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1803388).length < 2 ^ (prefixWord ++ tailWord_1803388).sum := by decide
  have hdescent : baseEnd_1803388 < baseStart_1803388 := by decide
  rcases family_descends (prefixWord ++ tailWord_1803388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1803418 : List Nat := [3, 1, 1, 5, 1, 2, 1, 1, 7]
def baseStart_1803418 : Nat := 118140960795 + 1803418 * 2 ^ 59
def prefixEnd_1803418 : Nat := 4983230072969 + 3 ^ 40 * 1803418 * 2
def baseEnd_1803418 : Nat := 205782278882251189440275

theorem tailTrace_1803418 : CollatzResearch.WordTrace tailWord_1803418 prefixEnd_1803418 205782278882251189440275 := by
  unfold tailWord_1803418
  simp only [CollatzResearch.WordTrace]
  refine ⟨16444014545133015029608727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43850705453688040078956605 16444014545133015029608727)
  ·
    refine ⟨24666021817699522544413091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16444014545133015029608727 24666021817699522544413091)
    ·
      refine ⟨36999032726549283816619637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24666021817699522544413091 36999032726549283816619637)
      ·
        refine ⟨3468659318113995357808091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 36999032726549283816619637 3468659318113995357808091)
        ·
          refine ⟨5202988977170993036712137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3468659318113995357808091 5202988977170993036712137)
          ·
            refine ⟨3902241732878244777534103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5202988977170993036712137 3902241732878244777534103)
            ·
              refine ⟨5853362599317367166301155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3902241732878244777534103 5853362599317367166301155)
              ·
                refine ⟨8780043898976050749451733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5853362599317367166301155 8780043898976050749451733)
                ·
                  refine ⟨205782278882251189440275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8780043898976050749451733 205782278882251189440275)
                  ·
                    rfl

theorem cell22_1803418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 1, 1, 7].length) (baseStart_1803418 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1803418 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1803418 prefixEnd_1803418 := by exact prefixLift 1803418
  have htrace : WordTrace (prefixWord ++ tailWord_1803418) baseStart_1803418 baseEnd_1803418 := by
    simpa [prefixWord, tailWord_1803418, baseEnd_1803418] using wordTrace_append hprefix tailTrace_1803418
  have hstable : (prefixWord ++ tailWord_1803418).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1803418).length < 2 ^ (prefixWord ++ tailWord_1803418).sum := by decide
  have hdescent : baseEnd_1803418 < baseStart_1803418 := by decide
  rcases family_descends (prefixWord ++ tailWord_1803418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1803422 : List Nat := [4, 3, 1, 1, 2, 2, 2, 1, 3, 3]
def baseStart_1803422 : Nat := 118140960795 + 1803422 * 2 ^ 59
def prefixEnd_1803422 : Nat := 4983230072969 + 3 ^ 40 * 1803422 * 2
def baseEnd_1803422 : Nat := 617348205928498891220813

theorem tailTrace_1803422 : CollatzResearch.WordTrace tailWord_1803422 prefixEnd_1803422 617348205928498891220813 := by
  unfold tailWord_1803422
  simp only [CollatzResearch.WordTrace]
  refine ⟨8222025509064696100197565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43850802715011712534387013 8222025509064696100197565)
  ·
    refine ⟨3083259565899261037574087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8222025509064696100197565 3083259565899261037574087)
    ·
      refine ⟨4624889348848891556361131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3083259565899261037574087 4624889348848891556361131)
      ·
        refine ⟨6937334023273337334541697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4624889348848891556361131 6937334023273337334541697)
        ·
          refine ⟨5203000517455003000906273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6937334023273337334541697 5203000517455003000906273)
          ·
            refine ⟨3902250388091252250679705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5203000517455003000906273 3902250388091252250679705)
            ·
              refine ⟨2926687791068439188009779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3902250388091252250679705 2926687791068439188009779)
              ·
                refine ⟨4390031686602658782014669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2926687791068439188009779 4390031686602658782014669)
                ·
                  refine ⟨1646261882475997043255501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4390031686602658782014669 1646261882475997043255501)
                  ·
                    refine ⟨617348205928498891220813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1646261882475997043255501 617348205928498891220813)
                    ·
                      rfl

theorem cell22_1803422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 2, 1, 3, 3].length) (baseStart_1803422 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1803422 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1803422 prefixEnd_1803422 := by exact prefixLift 1803422
  have htrace : WordTrace (prefixWord ++ tailWord_1803422) baseStart_1803422 baseEnd_1803422 := by
    simpa [prefixWord, tailWord_1803422, baseEnd_1803422] using wordTrace_append hprefix tailTrace_1803422
  have hstable : (prefixWord ++ tailWord_1803422).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1803422).length < 2 ^ (prefixWord ++ tailWord_1803422).sum := by decide
  have hdescent : baseEnd_1803422 < baseStart_1803422 := by decide
  rcases family_descends (prefixWord ++ tailWord_1803422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1803461 : List Nat := [1, 3, 1, 1, 1, 1, 3, 3, 3, 5]
def baseStart_1803461 : Nat := 118140960795 + 1803461 * 2 ^ 59
def prefixEnd_1803461 : Nat := 4983230072969 + 3 ^ 40 * 1803461 * 2
def baseEnd_1803461 : Nat := 617361556425515789495693

theorem tailTrace_1803461 : CollatzResearch.WordTrace tailWord_1803461 prefixEnd_1803461 617361556425515789495693 := by
  unfold tailWord_1803461
  simp only [CollatzResearch.WordTrace]
  refine ⟨65777626519376278462250237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43851751012917518974833491 65777626519376278462250237)
  ·
    refine ⟨24666609944766104423343839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65777626519376278462250237 24666609944766104423343839)
    ·
      refine ⟨36999914917149156635015759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24666609944766104423343839 36999914917149156635015759)
      ·
        refine ⟨55499872375723734952523639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36999914917149156635015759 55499872375723734952523639)
        ·
          refine ⟨83249808563585602428785459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55499872375723734952523639 83249808563585602428785459)
          ·
            refine ⟨124874712845378403643178189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83249808563585602428785459 124874712845378403643178189)
            ·
              refine ⟨46828017317016901366191821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 124874712845378403643178189 46828017317016901366191821)
              ·
                refine ⟨17560506493881338012321933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46828017317016901366191821 17560506493881338012321933)
                ·
                  refine ⟨6585189935205501754620725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17560506493881338012321933 6585189935205501754620725)
                  ·
                    refine ⟨617361556425515789495693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6585189935205501754620725 617361556425515789495693)
                    ·
                      rfl

theorem cell22_1803461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 3, 3, 5].length) (baseStart_1803461 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1803461 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1803461 prefixEnd_1803461 := by exact prefixLift 1803461
  have htrace : WordTrace (prefixWord ++ tailWord_1803461) baseStart_1803461 baseEnd_1803461 := by
    simpa [prefixWord, tailWord_1803461, baseEnd_1803461] using wordTrace_append hprefix tailTrace_1803461
  have hstable : (prefixWord ++ tailWord_1803461).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1803461).length < 2 ^ (prefixWord ++ tailWord_1803461).sum := by decide
  have hdescent : baseEnd_1803461 < baseStart_1803461 := by decide
  rcases family_descends (prefixWord ++ tailWord_1803461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1803480 : List Nat := [2, 1, 2, 2, 5, 2, 1, 1, 6]
def baseStart_1803480 : Nat := 118140960795 + 1803480 * 2 ^ 59
def prefixEnd_1803480 : Nat := 4983230072969 + 3 ^ 40 * 1803480 * 2
def baseEnd_1803480 : Nat := 205789353504602024423545

theorem tailTrace_1803480 : CollatzResearch.WordTrace tailWord_1803480 prefixEnd_1803480 205789353504602024423545 := by
  unfold tailWord_1803480
  simp only [CollatzResearch.WordTrace]
  refine ⟨32889159753153722353595947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43852213004204963138127929 32889159753153722353595947)
  ·
    refine ⟨49333739629730583530393921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32889159753153722353595947 49333739629730583530393921)
    ·
      refine ⟨37000304722297937647795441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49333739629730583530393921 37000304722297937647795441)
      ·
        refine ⟨27750228541723453235846581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37000304722297937647795441 27750228541723453235846581)
        ·
          refine ⟨2601583925786573740860617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 27750228541723453235846581 2601583925786573740860617)
          ·
            refine ⟨1951187944339930305645463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2601583925786573740860617 1951187944339930305645463)
            ·
              refine ⟨2926781916509895458468195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1951187944339930305645463 2926781916509895458468195)
              ·
                refine ⟨4390172874764843187702293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2926781916509895458468195 4390172874764843187702293)
                ·
                  refine ⟨205789353504602024423545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4390172874764843187702293 205789353504602024423545)
                  ·
                    rfl

theorem cell22_1803480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 2, 1, 1, 6].length) (baseStart_1803480 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1803480 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1803480 prefixEnd_1803480 := by exact prefixLift 1803480
  have htrace : WordTrace (prefixWord ++ tailWord_1803480) baseStart_1803480 baseEnd_1803480 := by
    simpa [prefixWord, tailWord_1803480, baseEnd_1803480] using wordTrace_append hprefix tailTrace_1803480
  have hstable : (prefixWord ++ tailWord_1803480).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1803480).length < 2 ^ (prefixWord ++ tailWord_1803480).sum := by decide
  have hdescent : baseEnd_1803480 < baseStart_1803480 := by decide
  rcases family_descends (prefixWord ++ tailWord_1803480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1803536 : List Nat := [2, 1, 1, 1, 1, 1, 1, 1, 13]
def baseStart_1803536 : Nat := 118140960795 + 1803536 * 2 ^ 59
def prefixEnd_1803536 : Nat := 4983230072969 + 3 ^ 40 * 1803536 * 2
def baseEnd_1803536 : Nat := 205795743486080197956821

theorem tailTrace_1803536 : CollatzResearch.WordTrace tailWord_1803536 prefixEnd_1803536 205795743486080197956821 := by
  unfold tailWord_1803536
  simp only [CollatzResearch.WordTrace]
  refine ⟨32890180997052283135615231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43853574662736377514153641 32890180997052283135615231)
  ·
    refine ⟨49335271495578424703422847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32890180997052283135615231 49335271495578424703422847)
    ·
      refine ⟨74002907243367637055134271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49335271495578424703422847 74002907243367637055134271)
      ·
        refine ⟨111004360865051455582701407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74002907243367637055134271 111004360865051455582701407)
        ·
          refine ⟨166506541297577183374052111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111004360865051455582701407 166506541297577183374052111)
          ·
            refine ⟨249759811946365775061078167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166506541297577183374052111 249759811946365775061078167)
            ·
              refine ⟨374639717919548662591617251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 249759811946365775061078167 374639717919548662591617251)
              ·
                refine ⟨561959576879322993887425877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 374639717919548662591617251 561959576879322993887425877)
                ·
                  refine ⟨205795743486080197956821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 13 561959576879322993887425877 205795743486080197956821)
                  ·
                    rfl

theorem cell22_1803536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 13].length) (baseStart_1803536 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1803536 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1803536 prefixEnd_1803536 := by exact prefixLift 1803536
  have htrace : WordTrace (prefixWord ++ tailWord_1803536) baseStart_1803536 baseEnd_1803536 := by
    simpa [prefixWord, tailWord_1803536, baseEnd_1803536] using wordTrace_append hprefix tailTrace_1803536
  have hstable : (prefixWord ++ tailWord_1803536).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1803536).length < 2 ^ (prefixWord ++ tailWord_1803536).sum := by decide
  have hdescent : baseEnd_1803536 < baseStart_1803536 := by decide
  rcases family_descends (prefixWord ++ tailWord_1803536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1803585 : List Nat := [1, 2, 5, 2, 1, 1, 1, 2, 2, 5]
def baseStart_1803585 : Nat := 118140960795 + 1803585 * 2 ^ 59
def prefixEnd_1803585 : Nat := 4983230072969 + 3 ^ 40 * 1803585 * 2
def baseEnd_1803585 : Nat := 617404004159620799395313

theorem tailTrace_1803585 : CollatzResearch.WordTrace tailWord_1803585 prefixEnd_1803585 617404004159620799395313 := by
  unfold tailWord_1803585
  simp only [CollatzResearch.WordTrace]
  refine ⟨65782149170927047639764209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43854766113951365093176139 65782149170927047639764209)
  ·
    refine ⟨49336611878195285729823157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65782149170927047639764209 49336611878195285729823157)
    ·
      refine ⟨4625307363580808037170921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 49336611878195285729823157 4625307363580808037170921)
      ·
        refine ⟨3468980522685606027878191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4625307363580808037170921 3468980522685606027878191)
        ·
          refine ⟨5203470784028409041817287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3468980522685606027878191 5203470784028409041817287)
          ·
            refine ⟨7805206176042613562725931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5203470784028409041817287 7805206176042613562725931)
            ·
              refine ⟨11707809264063920344088897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7805206176042613562725931 11707809264063920344088897)
              ·
                refine ⟨8780856948047940258066673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11707809264063920344088897 8780856948047940258066673)
                ·
                  refine ⟨6585642711035955193550005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8780856948047940258066673 6585642711035955193550005)
                  ·
                    refine ⟨617404004159620799395313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6585642711035955193550005 617404004159620799395313)
                    ·
                      rfl

theorem cell22_1803585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 2, 2, 5].length) (baseStart_1803585 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1803585 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1803585 prefixEnd_1803585 := by exact prefixLift 1803585
  have htrace : WordTrace (prefixWord ++ tailWord_1803585) baseStart_1803585 baseEnd_1803585 := by
    simpa [prefixWord, tailWord_1803585, baseEnd_1803585] using wordTrace_append hprefix tailTrace_1803585
  have hstable : (prefixWord ++ tailWord_1803585).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1803585).length < 2 ^ (prefixWord ++ tailWord_1803585).sum := by decide
  have hdescent : baseEnd_1803585 < baseStart_1803585 := by decide
  rcases family_descends (prefixWord ++ tailWord_1803585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1803645 : List Nat := [1, 4, 1, 1, 2, 2, 3, 2, 2, 4]
def baseStart_1803645 : Nat := 118140960795 + 1803645 * 2 ^ 59
def prefixEnd_1803645 : Nat := 4983230072969 + 3 ^ 40 * 1803645 * 2
def baseEnd_1803645 : Nat := 617424543385800642895129

theorem tailTrace_1803645 : CollatzResearch.WordTrace tailWord_1803645 prefixEnd_1803645 617424543385800642895129 := by
  unfold tailWord_1803645
  simp only [CollatzResearch.WordTrace]
  refine ⟨65784337550709677886948389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43856225033806451924632259 65784337550709677886948389)
  ·
    refine ⟨12334563290758064603802823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65784337550709677886948389 12334563290758064603802823)
    ·
      refine ⟨18501844936137096905704235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12334563290758064603802823 18501844936137096905704235)
      ·
        refine ⟨27752767404205645358556353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18501844936137096905704235 27752767404205645358556353)
        ·
          refine ⟨20814575553154234018917265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27752767404205645358556353 20814575553154234018917265)
          ·
            refine ⟨15610931664865675514187949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20814575553154234018917265 15610931664865675514187949)
            ·
              refine ⟨5854099374324628317820481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15610931664865675514187949 5854099374324628317820481)
              ·
                refine ⟨4390574530743471238365361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5854099374324628317820481 4390574530743471238365361)
                ·
                  refine ⟨3292930898057603428774021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4390574530743471238365361 3292930898057603428774021)
                  ·
                    refine ⟨617424543385800642895129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3292930898057603428774021 617424543385800642895129)
                    ·
                      rfl

theorem cell22_1803645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 3, 2, 2, 4].length) (baseStart_1803645 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1803645 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1803645 prefixEnd_1803645 := by exact prefixLift 1803645
  have htrace : WordTrace (prefixWord ++ tailWord_1803645) baseStart_1803645 baseEnd_1803645 := by
    simpa [prefixWord, tailWord_1803645, baseEnd_1803645] using wordTrace_append hprefix tailTrace_1803645
  have hstable : (prefixWord ++ tailWord_1803645).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1803645).length < 2 ^ (prefixWord ++ tailWord_1803645).sum := by decide
  have hdescent : baseEnd_1803645 < baseStart_1803645 := by decide
  rcases family_descends (prefixWord ++ tailWord_1803645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1803649 : List Nat := [1, 2, 4, 3, 3, 1, 1, 1, 6]
def baseStart_1803649 : Nat := 118140960795 + 1803649 * 2 ^ 59
def prefixEnd_1803649 : Nat := 4983230072969 + 3 ^ 40 * 1803649 * 2
def baseEnd_1803649 : Nat := 205808637555848655265039

theorem tailTrace_1803649 : CollatzResearch.WordTrace tailWord_1803649 prefixEnd_1803649 205808637555848655265039 := by
  unfold tailWord_1803649
  simp only [CollatzResearch.WordTrace]
  refine ⟨65784483442695186570094001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43856322295130124380062667 65784483442695186570094001)
  ·
    refine ⟨49338362582021389927570501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65784483442695186570094001 49338362582021389927570501)
    ·
      refine ⟨9250942984129010611419469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49338362582021389927570501 9250942984129010611419469)
      ·
        refine ⟨3469103619048378979282301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9250942984129010611419469 3469103619048378979282301)
        ·
          refine ⟨1300913857143142117230863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3469103619048378979282301 1300913857143142117230863)
          ·
            refine ⟨1951370785714713175846295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1300913857143142117230863 1951370785714713175846295)
            ·
              refine ⟨2927056178572069763769443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1951370785714713175846295 2927056178572069763769443)
              ·
                refine ⟨4390584267858104645654165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2927056178572069763769443 4390584267858104645654165)
                ·
                  refine ⟨205808637555848655265039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4390584267858104645654165 205808637555848655265039)
                  ·
                    rfl

theorem cell22_1803649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 1, 1, 1, 6].length) (baseStart_1803649 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1803649 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1803649 prefixEnd_1803649 := by exact prefixLift 1803649
  have htrace : WordTrace (prefixWord ++ tailWord_1803649) baseStart_1803649 baseEnd_1803649 := by
    simpa [prefixWord, tailWord_1803649, baseEnd_1803649] using wordTrace_append hprefix tailTrace_1803649
  have hstable : (prefixWord ++ tailWord_1803649).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1803649).length < 2 ^ (prefixWord ++ tailWord_1803649).sum := by decide
  have hdescent : baseEnd_1803649 < baseStart_1803649 := by decide
  rcases family_descends (prefixWord ++ tailWord_1803649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1803709 : List Nat := [1, 4, 1, 2, 2, 1, 3, 4, 1, 3]
def baseStart_1803709 : Nat := 118140960795 + 1803709 * 2 ^ 59
def prefixEnd_1803709 : Nat := 4983230072969 + 3 ^ 40 * 1803709 * 2
def baseEnd_1803709 : Nat := 617446451893725809294933

theorem tailTrace_1803709 : CollatzResearch.WordTrace tailWord_1803709 prefixEnd_1803709 617446451893725809294933 := by
  unfold tailWord_1803709
  simp only [CollatzResearch.WordTrace]
  refine ⟨65786671822477816817278181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43857781214985211211518787 65786671822477816817278181)
  ·
    refine ⟨12335000966714590653239659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65786671822477816817278181 12335000966714590653239659)
    ·
      refine ⟨18502501450071885979859489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12335000966714590653239659 18502501450071885979859489)
      ·
        refine ⟨13876876087553914484894617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18502501450071885979859489 13876876087553914484894617)
        ·
          refine ⟨10407657065665435863670963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13876876087553914484894617 10407657065665435863670963)
          ·
            refine ⟨15611485598498153795506445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10407657065665435863670963 15611485598498153795506445)
            ·
              refine ⟨5854307099436807673314917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15611485598498153795506445 5854307099436807673314917)
              ·
                refine ⟨1097682581144401438746547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5854307099436807673314917 1097682581144401438746547)
                ·
                  refine ⟨1646523871716602158119821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1097682581144401438746547 1646523871716602158119821)
                  ·
                    refine ⟨617446451893725809294933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1646523871716602158119821 617446451893725809294933)
                    ·
                      rfl

theorem cell22_1803709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 3, 4, 1, 3].length) (baseStart_1803709 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1803709 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1803709 prefixEnd_1803709 := by exact prefixLift 1803709
  have htrace : WordTrace (prefixWord ++ tailWord_1803709) baseStart_1803709 baseEnd_1803709 := by
    simpa [prefixWord, tailWord_1803709, baseEnd_1803709] using wordTrace_append hprefix tailTrace_1803709
  have hstable : (prefixWord ++ tailWord_1803709).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1803709).length < 2 ^ (prefixWord ++ tailWord_1803709).sum := by decide
  have hdescent : baseEnd_1803709 < baseStart_1803709 := by decide
  rcases family_descends (prefixWord ++ tailWord_1803709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1803720 : List Nat := [2, 1, 3, 1, 3, 1, 3, 1, 2, 5]
def baseStart_1803720 : Nat := 118140960795 + 1803720 * 2 ^ 59
def prefixEnd_1803720 : Nat := 4983230072969 + 3 ^ 40 * 1803720 * 2
def baseEnd_1803720 : Nat := 617450217418525447269899

theorem tailTrace_1803720 : CollatzResearch.WordTrace tailWord_1803720 prefixEnd_1803720 617450217418525447269899 := by
  unfold tailWord_1803720
  simp only [CollatzResearch.WordTrace]
  refine ⟨32893536512718982847964307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43858048683625310463952409 32893536512718982847964307)
  ·
    refine ⟨49340304769078474271946461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32893536512718982847964307 49340304769078474271946461)
    ·
      refine ⟨18502614288404427851979923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49340304769078474271946461 18502614288404427851979923)
      ·
        refine ⟨27753921432606641777969885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18502614288404427851979923 27753921432606641777969885)
        ·
          refine ⟨10407720537227490666738707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27753921432606641777969885 10407720537227490666738707)
          ·
            refine ⟨15611580805841236000108061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10407720537227490666738707 15611580805841236000108061)
            ·
              refine ⟨5854342802190463500040523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15611580805841236000108061 5854342802190463500040523)
              ·
                refine ⟨8781514203285695250060785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5854342802190463500040523 8781514203285695250060785)
                ·
                  refine ⟨6586135652464271437545589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8781514203285695250060785 6586135652464271437545589)
                  ·
                    refine ⟨617450217418525447269899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6586135652464271437545589 617450217418525447269899)
                    ·
                      rfl

theorem cell22_1803720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 3, 1, 2, 5].length) (baseStart_1803720 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1803720 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1803720 prefixEnd_1803720 := by exact prefixLift 1803720
  have htrace : WordTrace (prefixWord ++ tailWord_1803720) baseStart_1803720 baseEnd_1803720 := by
    simpa [prefixWord, tailWord_1803720, baseEnd_1803720] using wordTrace_append hprefix tailTrace_1803720
  have hstable : (prefixWord ++ tailWord_1803720).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1803720).length < 2 ^ (prefixWord ++ tailWord_1803720).sum := by decide
  have hdescent : baseEnd_1803720 < baseStart_1803720 := by decide
  rcases family_descends (prefixWord ++ tailWord_1803720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1803752 : List Nat := [2, 1, 4, 1, 1, 2, 3, 3, 1, 4]
def baseStart_1803752 : Nat := 118140960795 + 1803752 * 2 ^ 59
def prefixEnd_1803752 : Nat := 4983230072969 + 3 ^ 40 * 1803752 * 2
def baseEnd_1803752 : Nat := 617461171672488030469801

theorem tailTrace_1803752 : CollatzResearch.WordTrace tailWord_1803752 prefixEnd_1803752 617461171672488030469801 := by
  unfold tailWord_1803752
  simp only [CollatzResearch.WordTrace]
  refine ⟨32894120080661017580546755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43858826774214690107395673 32894120080661017580546755)
  ·
    refine ⟨49341180120991526370820133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32894120080661017580546755 49341180120991526370820133)
    ·
      refine ⟨9251471272685911194528775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49341180120991526370820133 9251471272685911194528775)
      ·
        refine ⟨13877206909028866791793163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9251471272685911194528775 13877206909028866791793163)
        ·
          refine ⟨20815810363543300187689745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13877206909028866791793163 20815810363543300187689745)
          ·
            refine ⟨15611857772657475140767309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20815810363543300187689745 15611857772657475140767309)
            ·
              refine ⟨5854446664746553177787741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15611857772657475140767309 5854446664746553177787741)
              ·
                refine ⟨2195417499279957441670403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5854446664746553177787741 2195417499279957441670403)
                ·
                  refine ⟨3293126248919936162505605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2195417499279957441670403 3293126248919936162505605)
                  ·
                    refine ⟨617461171672488030469801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3293126248919936162505605 617461171672488030469801)
                    ·
                      rfl

theorem cell22_1803752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 3, 3, 1, 4].length) (baseStart_1803752 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1803752 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1803752 prefixEnd_1803752 := by exact prefixLift 1803752
  have htrace : WordTrace (prefixWord ++ tailWord_1803752) baseStart_1803752 baseEnd_1803752 := by
    simpa [prefixWord, tailWord_1803752, baseEnd_1803752] using wordTrace_append hprefix tailTrace_1803752
  have hstable : (prefixWord ++ tailWord_1803752).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1803752).length < 2 ^ (prefixWord ++ tailWord_1803752).sum := by decide
  have hdescent : baseEnd_1803752 < baseStart_1803752 := by decide
  rcases family_descends (prefixWord ++ tailWord_1803752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1803795 : List Nat := [1, 1, 1, 2, 1, 7, 1, 8]
def baseStart_1803795 : Nat := 118140960795 + 1803795 * 2 ^ 59
def prefixEnd_1803795 : Nat := 4983230072969 + 3 ^ 40 * 1803795 * 2
def baseEnd_1803795 : Nat := 68608432383472250182741

theorem tailTrace_1803795 : CollatzResearch.WordTrace tailWord_1803795 prefixEnd_1803795 68608432383472250182741 := by
  unfold tailWord_1803795
  simp only [CollatzResearch.WordTrace]
  refine ⟨65789808500166253504908839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43859872333444169003272559 65789808500166253504908839)
  ·
    refine ⟨98684712750249380257363259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65789808500166253504908839 98684712750249380257363259)
    ·
      refine ⟨148027069125374070386044889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98684712750249380257363259 148027069125374070386044889)
      ·
        refine ⟨111020301844030552789533667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148027069125374070386044889 111020301844030552789533667)
        ·
          refine ⟨166530452766045829184300501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111020301844030552789533667 166530452766045829184300501)
          ·
            refine ⟨3903057486704199121507043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 166530452766045829184300501 3903057486704199121507043)
            ·
              refine ⟨5854586230056298682260565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3903057486704199121507043 5854586230056298682260565)
              ·
                refine ⟨68608432383472250182741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5854586230056298682260565 68608432383472250182741)
                ·
                  rfl

theorem cell22_1803795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 1, 8].length) (baseStart_1803795 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1803795 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1803795 prefixEnd_1803795 := by exact prefixLift 1803795
  have htrace : WordTrace (prefixWord ++ tailWord_1803795) baseStart_1803795 baseEnd_1803795 := by
    simpa [prefixWord, tailWord_1803795, baseEnd_1803795] using wordTrace_append hprefix tailTrace_1803795
  have hstable : (prefixWord ++ tailWord_1803795).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1803795).length < 2 ^ (prefixWord ++ tailWord_1803795).sum := by decide
  have hdescent : baseEnd_1803795 < baseStart_1803795 := by decide
  rcases family_descends (prefixWord ++ tailWord_1803795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1803825 : List Nat := [1, 2, 2, 3, 1, 1, 1, 3, 2, 6]
def baseStart_1803825 : Nat := 118140960795 + 1803825 * 2 ^ 59
def prefixEnd_1803825 : Nat := 4983230072969 + 3 ^ 40 * 1803825 * 2
def baseEnd_1803825 : Nat := 617486161064340173394577

theorem tailTrace_1803825 : CollatzResearch.WordTrace tailWord_1803825 prefixEnd_1803825 617486161064340173394577 := by
  unfold tailWord_1803825
  simp only [CollatzResearch.WordTrace]
  refine ⟨65790902690057568628500929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43860601793371712419000619 65790902690057568628500929)
  ·
    refine ⟨49343177017543176471375697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65790902690057568628500929 49343177017543176471375697)
    ·
      refine ⟨37007382763157382353531773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49343177017543176471375697 37007382763157382353531773)
      ·
        refine ⟨13877768536184018382574415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37007382763157382353531773 13877768536184018382574415)
        ·
          refine ⟨20816652804276027573861623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13877768536184018382574415 20816652804276027573861623)
          ·
            refine ⟨31224979206414041360792435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20816652804276027573861623 31224979206414041360792435)
            ·
              refine ⟨46837468809621062041188653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31224979206414041360792435 46837468809621062041188653)
              ·
                refine ⟨17564050803607898265445745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46837468809621062041188653 17564050803607898265445745)
                ·
                  refine ⟨13173038102705923699084309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17564050803607898265445745 13173038102705923699084309)
                  ·
                    refine ⟨617486161064340173394577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13173038102705923699084309 617486161064340173394577)
                    ·
                      rfl

theorem cell22_1803825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 3, 2, 6].length) (baseStart_1803825 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1803825 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1803825 prefixEnd_1803825 := by exact prefixLift 1803825
  have htrace : WordTrace (prefixWord ++ tailWord_1803825) baseStart_1803825 baseEnd_1803825 := by
    simpa [prefixWord, tailWord_1803825, baseEnd_1803825] using wordTrace_append hprefix tailTrace_1803825
  have hstable : (prefixWord ++ tailWord_1803825).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1803825).length < 2 ^ (prefixWord ++ tailWord_1803825).sum := by decide
  have hdescent : baseEnd_1803825 < baseStart_1803825 := by decide
  rcases family_descends (prefixWord ++ tailWord_1803825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1803855 : List Nat := [1, 1, 2, 1, 1, 2, 3, 2, 4, 5]
def baseStart_1803855 : Nat := 118140960795 + 1803855 * 2 ^ 59
def prefixEnd_1803855 : Nat := 4983230072969 + 3 ^ 40 * 1803855 * 2
def baseEnd_1803855 : Nat := 617496430677430095144485

theorem tailTrace_1803855 : CollatzResearch.WordTrace tailWord_1803855 prefixEnd_1803855 617496430677430095144485 := by
  unfold tailWord_1803855
  simp only [CollatzResearch.WordTrace]
  refine ⟨65791996879948883752093019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43861331253299255834728679 65791996879948883752093019)
  ·
    refine ⟨98687995319923325628139529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65791996879948883752093019 98687995319923325628139529)
    ·
      refine ⟨74015996489942494221104647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98687995319923325628139529 74015996489942494221104647)
      ·
        refine ⟨111023994734913741331656971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74015996489942494221104647 111023994734913741331656971)
        ·
          refine ⟨166535992102370611997485457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111023994734913741331656971 166535992102370611997485457)
          ·
            refine ⟨124901994076777958998114093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 166535992102370611997485457 124901994076777958998114093)
            ·
              refine ⟨46838247778791734624292785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 124901994076777958998114093 46838247778791734624292785)
              ·
                refine ⟨35128685834093800968219589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46838247778791734624292785 35128685834093800968219589)
                ·
                  refine ⟨6586628593892587681541173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35128685834093800968219589 6586628593892587681541173)
                  ·
                    refine ⟨617496430677430095144485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6586628593892587681541173 617496430677430095144485)
                    ·
                      rfl

theorem cell22_1803855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 2, 4, 5].length) (baseStart_1803855 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1803855 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1803855 prefixEnd_1803855 := by exact prefixLift 1803855
  have htrace : WordTrace (prefixWord ++ tailWord_1803855) baseStart_1803855 baseEnd_1803855 := by
    simpa [prefixWord, tailWord_1803855, baseEnd_1803855] using wordTrace_append hprefix tailTrace_1803855
  have hstable : (prefixWord ++ tailWord_1803855).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1803855).length < 2 ^ (prefixWord ++ tailWord_1803855).sum := by decide
  have hdescent : baseEnd_1803855 < baseStart_1803855 := by decide
  rcases family_descends (prefixWord ++ tailWord_1803855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1803951 : List Nat := [1, 1, 2, 1, 2, 4, 5, 1, 2, 3]
def baseStart_1803951 : Nat := 118140960795 + 1803951 * 2 ^ 59
def prefixEnd_1803951 : Nat := 4983230072969 + 3 ^ 40 * 1803951 * 2
def baseEnd_1803951 : Nat := 617529293439317844744191

theorem tailTrace_1803951 : CollatzResearch.WordTrace tailWord_1803951 prefixEnd_1803951 617529293439317844744191 := by
  unfold tailWord_1803951
  simp only [CollatzResearch.WordTrace]
  refine ⟨65795498287601092147587707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43863665525067394765058471 65795498287601092147587707)
  ·
    refine ⟨98693247431401638221381561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65795498287601092147587707 98693247431401638221381561)
    ·
      refine ⟨74019935573551228666036171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98693247431401638221381561 74019935573551228666036171)
      ·
        refine ⟨111029903360326842999054257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74019935573551228666036171 111029903360326842999054257)
        ·
          refine ⟨83272427520245132249290693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111029903360326842999054257 83272427520245132249290693)
          ·
            refine ⟨15613580160045962296742005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 83272427520245132249290693 15613580160045962296742005)
            ·
              refine ⟨1463773140004308965319563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15613580160045962296742005 1463773140004308965319563)
              ·
                refine ⟨2195659710006463447979345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1463773140004308965319563 2195659710006463447979345)
                ·
                  refine ⟨1646744782504847585984509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2195659710006463447979345 1646744782504847585984509)
                  ·
                    refine ⟨617529293439317844744191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1646744782504847585984509 617529293439317844744191)
                    ·
                      rfl

theorem cell22_1803951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 5, 1, 2, 3].length) (baseStart_1803951 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1803951 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1803951 prefixEnd_1803951 := by exact prefixLift 1803951
  have htrace : WordTrace (prefixWord ++ tailWord_1803951) baseStart_1803951 baseEnd_1803951 := by
    simpa [prefixWord, tailWord_1803951, baseEnd_1803951] using wordTrace_append hprefix tailTrace_1803951
  have hstable : (prefixWord ++ tailWord_1803951).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1803951).length < 2 ^ (prefixWord ++ tailWord_1803951).sum := by decide
  have hdescent : baseEnd_1803951 < baseStart_1803951 := by decide
  rcases family_descends (prefixWord ++ tailWord_1803951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1803964 : List Nat := [2, 2, 2, 3, 1, 2, 4, 6]
def baseStart_1803964 : Nat := 118140960795 + 1803964 * 2 ^ 59
def prefixEnd_1803964 : Nat := 4983230072969 + 3 ^ 40 * 1803964 * 2
def baseEnd_1803964 : Nat := 68614860400554460463239

theorem tailTrace_1803964 : CollatzResearch.WordTrace tailWord_1803964 prefixEnd_1803964 68614860400554460463239 := by
  unfold tailWord_1803964
  simp only [CollatzResearch.WordTrace]
  refine ⟨32897986218276997683905473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43863981624369330245207297 32897986218276997683905473)
  ·
    refine ⟨24673489663707748262929105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32897986218276997683905473 24673489663707748262929105)
    ·
      refine ⟨18505117247780811197196829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24673489663707748262929105 18505117247780811197196829)
      ·
        refine ⟨6939418967917804198948811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18505117247780811197196829 6939418967917804198948811)
        ·
          refine ⟨10409128451876706298423217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6939418967917804198948811 10409128451876706298423217)
          ·
            refine ⟨7806846338907529723817413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10409128451876706298423217 7806846338907529723817413)
            ·
              refine ⟨1463783688545161823215765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7806846338907529723817413 1463783688545161823215765)
              ·
                refine ⟨68614860400554460463239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1463783688545161823215765 68614860400554460463239)
                ·
                  rfl

theorem cell22_1803964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 4, 6].length) (baseStart_1803964 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1803964 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1803964 prefixEnd_1803964 := by exact prefixLift 1803964
  have htrace : WordTrace (prefixWord ++ tailWord_1803964) baseStart_1803964 baseEnd_1803964 := by
    simpa [prefixWord, tailWord_1803964, baseEnd_1803964] using wordTrace_append hprefix tailTrace_1803964
  have hstable : (prefixWord ++ tailWord_1803964).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1803964).length < 2 ^ (prefixWord ++ tailWord_1803964).sum := by decide
  have hdescent : baseEnd_1803964 < baseStart_1803964 := by decide
  rcases family_descends (prefixWord ++ tailWord_1803964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1803981 : List Nat := [1, 6, 2, 1, 1, 3, 8]
def baseStart_1803981 : Nat := 118140960795 + 1803981 * 2 ^ 59
def prefixEnd_1803981 : Nat := 4983230072969 + 3 ^ 40 * 1803981 * 2
def baseEnd_1803981 : Nat := 22871835668607695055337

theorem tailTrace_1803981 : CollatzResearch.WordTrace tailWord_1803981 prefixEnd_1803981 22871835668607695055337 := by
  unfold tailWord_1803981
  simp only [CollatzResearch.WordTrace]
  refine ⟨65796592477492407271179797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43864394984994938180786531 65796592477492407271179797)
  ·
    refine ⟨3084215272382456590836553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 65796592477492407271179797 3084215272382456590836553)
    ·
      refine ⟨2313161454286842443127415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3084215272382456590836553 2313161454286842443127415)
      ·
        refine ⟨3469742181430263664691123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2313161454286842443127415 3469742181430263664691123)
        ·
          refine ⟨5204613272145395497036685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3469742181430263664691123 5204613272145395497036685)
          ·
            refine ⟨1951729977054523311388757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5204613272145395497036685 1951729977054523311388757)
            ·
              refine ⟨22871835668607695055337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1951729977054523311388757 22871835668607695055337)
              ·
                rfl

theorem cell22_1803981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 3, 8].length) (baseStart_1803981 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1803981 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1803981 prefixEnd_1803981 := by exact prefixLift 1803981
  have htrace : WordTrace (prefixWord ++ tailWord_1803981) baseStart_1803981 baseEnd_1803981 := by
    simpa [prefixWord, tailWord_1803981, baseEnd_1803981] using wordTrace_append hprefix tailTrace_1803981
  have hstable : (prefixWord ++ tailWord_1803981).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1803981).length < 2 ^ (prefixWord ++ tailWord_1803981).sum := by decide
  have hdescent : baseEnd_1803981 < baseStart_1803981 := by decide
  rcases family_descends (prefixWord ++ tailWord_1803981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1803992 : List Nat := [2, 1, 2, 2, 3, 1, 1, 3, 7]
def baseStart_1803992 : Nat := 118140960795 + 1803992 * 2 ^ 59
def prefixEnd_1803992 : Nat := 4983230072969 + 3 ^ 40 * 1803992 * 2
def baseEnd_1803992 : Nat := 205847776192402468156355

theorem tailTrace_1803992 : CollatzResearch.WordTrace tailWord_1803992 prefixEnd_1803992 205847776192402468156355 := by
  unfold tailWord_1803992
  simp only [CollatzResearch.WordTrace]
  refine ⟨32898496840226278074915115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43864662453635037433220153 32898496840226278074915115)
  ·
    refine ⟨49347745260339417112372673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32898496840226278074915115 49347745260339417112372673)
    ·
      refine ⟨37010808945254562834279505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49347745260339417112372673 37010808945254562834279505)
      ·
        refine ⟨27758106708940922125709629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37010808945254562834279505 27758106708940922125709629)
        ·
          refine ⟨10409290015852845797141111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27758106708940922125709629 10409290015852845797141111)
          ·
            refine ⟨15613935023779268695711667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10409290015852845797141111 15613935023779268695711667)
            ·
              refine ⟨23420902535668903043567501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15613935023779268695711667 23420902535668903043567501)
              ·
                refine ⟨8782838450875838641337813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23420902535668903043567501 8782838450875838641337813)
                ·
                  refine ⟨205847776192402468156355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8782838450875838641337813 205847776192402468156355)
                  ·
                    rfl

theorem cell22_1803992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 3, 7].length) (baseStart_1803992 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1803992 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1803992 prefixEnd_1803992 := by exact prefixLift 1803992
  have htrace : WordTrace (prefixWord ++ tailWord_1803992) baseStart_1803992 baseEnd_1803992 := by
    simpa [prefixWord, tailWord_1803992, baseEnd_1803992] using wordTrace_append hprefix tailTrace_1803992
  have hstable : (prefixWord ++ tailWord_1803992).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1803992).length < 2 ^ (prefixWord ++ tailWord_1803992).sum := by decide
  have hdescent : baseEnd_1803992 < baseStart_1803992 := by decide
  rcases family_descends (prefixWord ++ tailWord_1803992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1804038 : List Nat := [6, 2, 2, 1, 2, 1, 2, 2, 4]
def baseStart_1804038 : Nat := 118140960795 + 1804038 * 2 ^ 59
def prefixEnd_1804038 : Nat := 4983230072969 + 3 ^ 40 * 1804038 * 2
def baseEnd_1804038 : Nat := 205853025105759539272975

theorem tailTrace_1804038 : CollatzResearch.WordTrace tailWord_1804038 prefixEnd_1804038 205853025105759539272975 := by
  unfold tailWord_1804038
  simp only [CollatzResearch.WordTrace]
  refine ⟨2056208482446434562687649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 43865780958857270670669845 2056208482446434562687649)
  ·
    refine ⟨1542156361834825922015737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2056208482446434562687649 1542156361834825922015737)
    ·
      refine ⟨1156617271376119441511803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1542156361834825922015737 1156617271376119441511803)
      ·
        refine ⟨1734925907064179162267705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1156617271376119441511803 1734925907064179162267705)
        ·
          refine ⟨1301194430298134371700779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1734925907064179162267705 1301194430298134371700779)
          ·
            refine ⟨1951791645447201557551169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1301194430298134371700779 1951791645447201557551169)
            ·
              refine ⟨1463843734085401168163377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1951791645447201557551169 1463843734085401168163377)
              ·
                refine ⟨1097882800564050876122533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1463843734085401168163377 1097882800564050876122533)
                ·
                  refine ⟨205853025105759539272975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1097882800564050876122533 205853025105759539272975)
                  ·
                    rfl

theorem cell22_1804038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 1, 2, 2, 4].length) (baseStart_1804038 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1804038 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1804038 prefixEnd_1804038 := by exact prefixLift 1804038
  have htrace : WordTrace (prefixWord ++ tailWord_1804038) baseStart_1804038 baseEnd_1804038 := by
    simpa [prefixWord, tailWord_1804038, baseEnd_1804038] using wordTrace_append hprefix tailTrace_1804038
  have hstable : (prefixWord ++ tailWord_1804038).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1804038).length < 2 ^ (prefixWord ++ tailWord_1804038).sum := by decide
  have hdescent : baseEnd_1804038 < baseStart_1804038 := by decide
  rcases family_descends (prefixWord ++ tailWord_1804038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1804069 : List Nat := [1, 3, 1, 2, 3, 2, 1, 3, 1, 5]
def baseStart_1804069 : Nat := 118140960795 + 1804069 * 2 ^ 59
def prefixEnd_1804069 : Nat := 4983230072969 + 3 ^ 40 * 1804069 * 2
def baseEnd_1804069 : Nat := 617569687250804870293829

theorem tailTrace_1804069 : CollatzResearch.WordTrace tailWord_1804069 prefixEnd_1804069 617569687250804870293829 := by
  unfold tailWord_1804069
  simp only [CollatzResearch.WordTrace]
  refine ⟨65799802101173598300383261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43866534734115732200255507 65799802101173598300383261)
  ·
    refine ⟨24674925787940099362643723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65799802101173598300383261 24674925787940099362643723)
    ·
      refine ⟨37012388681910149043965585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24674925787940099362643723 37012388681910149043965585)
      ·
        refine ⟨27759291511432611782974189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37012388681910149043965585 27759291511432611782974189)
        ·
          refine ⟨10409734316787229418615321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27759291511432611782974189 10409734316787229418615321)
          ·
            refine ⟨7807300737590422063961491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10409734316787229418615321 7807300737590422063961491)
            ·
              refine ⟨11710951106385633095942237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7807300737590422063961491 11710951106385633095942237)
              ·
                refine ⟨4391606664894612410978339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11710951106385633095942237 4391606664894612410978339)
                ·
                  refine ⟨6587409997341918616467509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4391606664894612410978339 6587409997341918616467509)
                  ·
                    refine ⟨617569687250804870293829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6587409997341918616467509 617569687250804870293829)
                    ·
                      rfl

theorem cell22_1804069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 3, 1, 5].length) (baseStart_1804069 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1804069 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1804069 prefixEnd_1804069 := by exact prefixLift 1804069
  have htrace : WordTrace (prefixWord ++ tailWord_1804069) baseStart_1804069 baseEnd_1804069 := by
    simpa [prefixWord, tailWord_1804069, baseEnd_1804069] using wordTrace_append hprefix tailTrace_1804069
  have hstable : (prefixWord ++ tailWord_1804069).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1804069).length < 2 ^ (prefixWord ++ tailWord_1804069).sum := by decide
  have hdescent : baseEnd_1804069 < baseStart_1804069 := by decide
  rcases family_descends (prefixWord ++ tailWord_1804069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1804165 : List Nat := [1, 3, 1, 1, 3, 2, 5, 2, 1, 3]
def baseStart_1804165 : Nat := 118140960795 + 1804165 * 2 ^ 59
def prefixEnd_1804165 : Nat := 4983230072969 + 3 ^ 40 * 1804165 * 2
def baseEnd_1804165 : Nat := 617602550012692619893535

theorem tailTrace_1804165 : CollatzResearch.WordTrace tailWord_1804165 prefixEnd_1804165 617602550012692619893535 := by
  unfold tailWord_1804165
  simp only [CollatzResearch.WordTrace]
  refine ⟨65803303508825806695877949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43868869005883871130585299 65803303508825806695877949)
  ·
    refine ⟨24676238815809677510954231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65803303508825806695877949 24676238815809677510954231)
    ·
      refine ⟨37014358223714516266431347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24676238815809677510954231 37014358223714516266431347)
      ·
        refine ⟨55521537335571774399647021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37014358223714516266431347 55521537335571774399647021)
        ·
          refine ⟨20820576500839415399867633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55521537335571774399647021 20820576500839415399867633)
          ·
            refine ⟨15615432375629561549900725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20820576500839415399867633 15615432375629561549900725)
            ·
              refine ⟨1463946785215271395303193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15615432375629561549900725 1463946785215271395303193)
              ·
                refine ⟨1097960088911453546477395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1463946785215271395303193 1097960088911453546477395)
                ·
                  refine ⟨1646940133367180319716093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1097960088911453546477395 1646940133367180319716093)
                  ·
                    refine ⟨617602550012692619893535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1646940133367180319716093 617602550012692619893535)
                    ·
                      rfl

theorem cell22_1804165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 5, 2, 1, 3].length) (baseStart_1804165 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1804165 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1804165 prefixEnd_1804165 := by exact prefixLift 1804165
  have htrace : WordTrace (prefixWord ++ tailWord_1804165) baseStart_1804165 baseEnd_1804165 := by
    simpa [prefixWord, tailWord_1804165, baseEnd_1804165] using wordTrace_append hprefix tailTrace_1804165
  have hstable : (prefixWord ++ tailWord_1804165).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1804165).length < 2 ^ (prefixWord ++ tailWord_1804165).sum := by decide
  have hdescent : baseEnd_1804165 < baseStart_1804165 := by decide
  rcases family_descends (prefixWord ++ tailWord_1804165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1804178 : List Nat := [3, 2, 3, 2, 1, 2, 1, 3, 5]
def baseStart_1804178 : Nat := 118140960795 + 1804178 * 2 ^ 59
def prefixEnd_1804178 : Nat := 4983230072969 + 3 ^ 40 * 1804178 * 2
def baseEnd_1804178 : Nat := 205869000059454973106165

theorem tailTrace_1804178 : CollatzResearch.WordTrace tailWord_1804178 prefixEnd_1804178 205869000059454973106165 := by
  unfold tailWord_1804178
  simp only [CollatzResearch.WordTrace]
  refine ⟨16450944414444677479025297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43869185105185806610734125 16450944414444677479025297)
  ·
    refine ⟨12338208310833508109268973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16450944414444677479025297 12338208310833508109268973)
    ·
      refine ⟨4626828116562565540975865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12338208310833508109268973 4626828116562565540975865)
      ·
        refine ⟨3470121087421924155731899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4626828116562565540975865 3470121087421924155731899)
        ·
          refine ⟨5205181631132886233597849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3470121087421924155731899 5205181631132886233597849)
          ·
            refine ⟨3903886223349664675198387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5205181631132886233597849 3903886223349664675198387)
            ·
              refine ⟨5855829335024497012797581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3903886223349664675198387 5855829335024497012797581)
              ·
                refine ⟨2195936000634186379799093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5855829335024497012797581 2195936000634186379799093)
                ·
                  refine ⟨205869000059454973106165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2195936000634186379799093 205869000059454973106165)
                  ·
                    rfl

theorem cell22_1804178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 1, 3, 5].length) (baseStart_1804178 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1804178 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1804178 prefixEnd_1804178 := by exact prefixLift 1804178
  have htrace : WordTrace (prefixWord ++ tailWord_1804178) baseStart_1804178 baseEnd_1804178 := by
    simpa [prefixWord, tailWord_1804178, baseEnd_1804178] using wordTrace_append hprefix tailTrace_1804178
  have hstable : (prefixWord ++ tailWord_1804178).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1804178).length < 2 ^ (prefixWord ++ tailWord_1804178).sum := by decide
  have hdescent : baseEnd_1804178 < baseStart_1804178 := by decide
  rcases family_descends (prefixWord ++ tailWord_1804178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1804238 : List Nat := [4, 1, 1, 1, 2, 2, 1, 5, 2, 3]
def baseStart_1804238 : Nat := 118140960795 + 1804238 * 2 ^ 59
def prefixEnd_1804238 : Nat := 4983230072969 + 3 ^ 40 * 1804238 * 2
def baseEnd_1804238 : Nat := 617627539404544762818311

theorem tailTrace_1804238 : CollatzResearch.WordTrace tailWord_1804238 prefixEnd_1804238 617627539404544762818311 := by
  unfold tailWord_1804238
  simp only [CollatzResearch.WordTrace]
  refine ⟨8225745754695167520410671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43870644025040893442190245 8225745754695167520410671)
  ·
    refine ⟨12338618632042751280616007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8225745754695167520410671 12338618632042751280616007)
    ·
      refine ⟨18507927948064126920924011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12338618632042751280616007 18507927948064126920924011)
      ·
        refine ⟨27761891922096190381386017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18507927948064126920924011 27761891922096190381386017)
        ·
          refine ⟨20821418941572142786039513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27761891922096190381386017 20821418941572142786039513)
          ·
            refine ⟨15616064206179107089529635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20821418941572142786039513 15616064206179107089529635)
            ·
              refine ⟨23424096309268660634294453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15616064206179107089529635 23424096309268660634294453)
              ·
                refine ⟨2196009028993936934465105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23424096309268660634294453 2196009028993936934465105)
                ·
                  refine ⟨1647006771745452700848829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2196009028993936934465105 1647006771745452700848829)
                  ·
                    refine ⟨617627539404544762818311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1647006771745452700848829 617627539404544762818311)
                    ·
                      rfl

theorem cell22_1804238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 5, 2, 3].length) (baseStart_1804238 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1804238 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1804238 prefixEnd_1804238 := by exact prefixLift 1804238
  have htrace : WordTrace (prefixWord ++ tailWord_1804238) baseStart_1804238 baseEnd_1804238 := by
    simpa [prefixWord, tailWord_1804238, baseEnd_1804238] using wordTrace_append hprefix tailTrace_1804238
  have hstable : (prefixWord ++ tailWord_1804238).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1804238).length < 2 ^ (prefixWord ++ tailWord_1804238).sum := by decide
  have hdescent : baseEnd_1804238 < baseStart_1804238 := by decide
  rcases family_descends (prefixWord ++ tailWord_1804238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1804253 : List Nat := [1, 4, 3, 1, 3, 1, 1, 1, 1, 6]
def baseStart_1804253 : Nat := 118140960795 + 1804253 * 2 ^ 59
def prefixEnd_1804253 : Nat := 4983230072969 + 3 ^ 40 * 1804253 * 2
def baseEnd_1804253 : Nat := 617632674211089723693265

theorem tailTrace_1804253 : CollatzResearch.WordTrace tailWord_1804253 prefixEnd_1804253 617632674211089723693265 := by
  unfold tailWord_1804253
  simp only [CollatzResearch.WordTrace]
  refine ⟨65806513132506997725081413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43871008755004665150054275 65806513132506997725081413)
  ·
    refine ⟨12338721212345062073452765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65806513132506997725081413 12338721212345062073452765)
    ·
      refine ⟨4627020454629398277544787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12338721212345062073452765 4627020454629398277544787)
      ·
        refine ⟨6940530681944097416317181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4627020454629398277544787 6940530681944097416317181)
        ·
          refine ⟨2602699005729036531118943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6940530681944097416317181 2602699005729036531118943)
          ·
            refine ⟨3904048508593554796678415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2602699005729036531118943 3904048508593554796678415)
            ·
              refine ⟨5856072762890332195017623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3904048508593554796678415 5856072762890332195017623)
              ·
                refine ⟨8784109144335498292526435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5856072762890332195017623 8784109144335498292526435)
                ·
                  refine ⟨13176163716503247438789653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8784109144335498292526435 13176163716503247438789653)
                  ·
                    refine ⟨617632674211089723693265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13176163716503247438789653 617632674211089723693265)
                    ·
                      rfl

theorem cell22_1804253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 1, 1, 1, 6].length) (baseStart_1804253 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1804253 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1804253 prefixEnd_1804253 := by exact prefixLift 1804253
  have htrace : WordTrace (prefixWord ++ tailWord_1804253) baseStart_1804253 baseEnd_1804253 := by
    simpa [prefixWord, tailWord_1804253, baseEnd_1804253] using wordTrace_append hprefix tailTrace_1804253
  have hstable : (prefixWord ++ tailWord_1804253).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1804253).length < 2 ^ (prefixWord ++ tailWord_1804253).sum := by decide
  have hdescent : baseEnd_1804253 < baseStart_1804253 := by decide
  rcases family_descends (prefixWord ++ tailWord_1804253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1804317 : List Nat := [1, 4, 2, 2, 2, 1, 3, 3, 1, 3]
def baseStart_1804317 : Nat := 118140960795 + 1804317 * 2 ^ 59
def prefixEnd_1804317 : Nat := 4983230072969 + 3 ^ 40 * 1804317 * 2
def baseEnd_1804317 : Nat := 617654582719014890093069

theorem tailTrace_1804317 : CollatzResearch.WordTrace tailWord_1804317 prefixEnd_1804317 617654582719014890093069 := by
  unfold tailWord_1804317
  simp only [CollatzResearch.WordTrace]
  refine ⟨65808847404275136655411205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43872564936183424436940803 65808847404275136655411205)
  ·
    refine ⟨12339158888301588122889601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65808847404275136655411205 12339158888301588122889601)
    ·
      refine ⟨9254369166226191092167201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12339158888301588122889601 9254369166226191092167201)
      ·
        refine ⟨6940776874669643319125401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9254369166226191092167201 6940776874669643319125401)
        ·
          refine ⟨5205582656002232489344051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6940776874669643319125401 5205582656002232489344051)
          ·
            refine ⟨7808373984003348734016077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5205582656002232489344051 7808373984003348734016077)
            ·
              refine ⟨2928140244001255775256029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7808373984003348734016077 2928140244001255775256029)
              ·
                refine ⟨1098052591500470915721011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2928140244001255775256029 1098052591500470915721011)
                ·
                  refine ⟨1647078887250706373581517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1098052591500470915721011 1647078887250706373581517)
                  ·
                    refine ⟨617654582719014890093069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1647078887250706373581517 617654582719014890093069)
                    ·
                      rfl

theorem cell22_1804317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 3, 3, 1, 3].length) (baseStart_1804317 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1804317 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1804317 prefixEnd_1804317 := by exact prefixLift 1804317
  have htrace : WordTrace (prefixWord ++ tailWord_1804317) baseStart_1804317 baseEnd_1804317 := by
    simpa [prefixWord, tailWord_1804317, baseEnd_1804317] using wordTrace_append hprefix tailTrace_1804317
  have hstable : (prefixWord ++ tailWord_1804317).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1804317).length < 2 ^ (prefixWord ++ tailWord_1804317).sum := by decide
  have hdescent : baseEnd_1804317 < baseStart_1804317 := by decide
  rcases family_descends (prefixWord ++ tailWord_1804317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1804334 : List Nat := [4, 1, 3, 1, 1, 3, 3, 2, 1, 3]
def baseStart_1804334 : Nat := 118140960795 + 1804334 * 2 ^ 59
def prefixEnd_1804334 : Nat := 4983230072969 + 3 ^ 40 * 1804334 * 2
def baseEnd_1804334 : Nat := 617660402166432512418017

theorem tailTrace_1804334 : CollatzResearch.WordTrace tailWord_1804334 prefixEnd_1804334 617660402166432512418017 := by
  unfold tailWord_1804334
  simp only [CollatzResearch.WordTrace]
  refine ⟨8226183430651693569847507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43872978296809032372520037 8226183430651693569847507)
  ·
    refine ⟨12339275145977540354771261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8226183430651693569847507 12339275145977540354771261)
    ·
      refine ⟨4627228179741577633039223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12339275145977540354771261 4627228179741577633039223)
      ·
        refine ⟨6940842269612366449558835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4627228179741577633039223 6940842269612366449558835)
        ·
          refine ⟨10411263404418549674338253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6940842269612366449558835 10411263404418549674338253)
          ·
            refine ⟨3904223776656956127876845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10411263404418549674338253 3904223776656956127876845)
            ·
              refine ⟨1464083916246358547953817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3904223776656956127876845 1464083916246358547953817)
              ·
                refine ⟨1098062937184768910965363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1464083916246358547953817 1098062937184768910965363)
                ·
                  refine ⟨1647094405777153366448045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1098062937184768910965363 1647094405777153366448045)
                  ·
                    refine ⟨617660402166432512418017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1647094405777153366448045 617660402166432512418017)
                    ·
                      rfl

theorem cell22_1804334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 3, 2, 1, 3].length) (baseStart_1804334 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1804334 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1804334 prefixEnd_1804334 := by exact prefixLift 1804334
  have htrace : WordTrace (prefixWord ++ tailWord_1804334) baseStart_1804334 baseEnd_1804334 := by
    simpa [prefixWord, tailWord_1804334, baseEnd_1804334] using wordTrace_append hprefix tailTrace_1804334
  have hstable : (prefixWord ++ tailWord_1804334).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1804334).length < 2 ^ (prefixWord ++ tailWord_1804334).sum := by decide
  have hdescent : baseEnd_1804334 < baseStart_1804334 := by decide
  rcases family_descends (prefixWord ++ tailWord_1804334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1804373 : List Nat := [1, 3, 2, 2, 1, 4, 1, 2, 1, 5]
def baseStart_1804373 : Nat := 118140960795 + 1804373 * 2 ^ 59
def prefixEnd_1804373 : Nat := 4983230072969 + 3 ^ 40 * 1804373 * 2
def baseEnd_1804373 : Nat := 617673752663449410692897

theorem tailTrace_1804373 : CollatzResearch.WordTrace tailWord_1804373 prefixEnd_1804373 617673752663449410692897 := by
  unfold tailWord_1804373
  simp only [CollatzResearch.WordTrace]
  refine ⟨65810889892072258219449773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43873926594714838812966515 65810889892072258219449773)
  ·
    refine ⟨24679083709527096832293665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65810889892072258219449773 24679083709527096832293665)
    ·
      refine ⟨18509312782145322624220249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24679083709527096832293665 18509312782145322624220249)
      ·
        refine ⟨13881984586608991968165187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18509312782145322624220249 13881984586608991968165187)
        ·
          refine ⟨20822976879913487952247781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13881984586608991968165187 20822976879913487952247781)
          ·
            refine ⟨3904308164983778991046459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20822976879913487952247781 3904308164983778991046459)
            ·
              refine ⟨5856462247475668486569689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3904308164983778991046459 5856462247475668486569689)
              ·
                refine ⟨4392346685606751364927267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5856462247475668486569689 4392346685606751364927267)
                ·
                  refine ⟨6588520028410127047390901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4392346685606751364927267 6588520028410127047390901)
                  ·
                    refine ⟨617673752663449410692897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6588520028410127047390901 617673752663449410692897)
                    ·
                      rfl

theorem cell22_1804373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 1, 2, 1, 5].length) (baseStart_1804373 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1804373 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1804373 prefixEnd_1804373 := by exact prefixLift 1804373
  have htrace : WordTrace (prefixWord ++ tailWord_1804373) baseStart_1804373 baseEnd_1804373 := by
    simpa [prefixWord, tailWord_1804373, baseEnd_1804373] using wordTrace_append hprefix tailTrace_1804373
  have hstable : (prefixWord ++ tailWord_1804373).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1804373).length < 2 ^ (prefixWord ++ tailWord_1804373).sum := by decide
  have hdescent : baseEnd_1804373 < baseStart_1804373 := by decide
  rcases family_descends (prefixWord ++ tailWord_1804373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1804388 : List Nat := [2, 3, 1, 1, 2, 1, 4, 2, 2, 4]
def baseStart_1804388 : Nat := 118140960795 + 1804388 * 2 ^ 59
def prefixEnd_1804388 : Nat := 4983230072969 + 3 ^ 40 * 1804388 * 2
def baseEnd_1804388 : Nat := 617678887469994371567851

theorem tailTrace_1804388 : CollatzResearch.WordTrace tailWord_1804388 prefixEnd_1804388 617678887469994371567851 := by
  unfold tailWord_1804388
  simp only [CollatzResearch.WordTrace]
  refine ⟨32905718493508957890622909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43874291324678610520830545 32905718493508957890622909)
  ·
    refine ⟨12339644435065859208983591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32905718493508957890622909 12339644435065859208983591)
    ·
      refine ⟨18509466652598788813475387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12339644435065859208983591 18509466652598788813475387)
      ·
        refine ⟨27764199978898183220213081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18509466652598788813475387 27764199978898183220213081)
        ·
          refine ⟨20823149984173637415159811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27764199978898183220213081 20823149984173637415159811)
          ·
            refine ⟨31234724976260456122739717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20823149984173637415159811 31234724976260456122739717)
            ·
              refine ⟨5856510933048835523013697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31234724976260456122739717 5856510933048835523013697)
              ·
                refine ⟨4392383199786626642260273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5856510933048835523013697 4392383199786626642260273)
                ·
                  refine ⟨3294287399839969981695205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4392383199786626642260273 3294287399839969981695205)
                  ·
                    refine ⟨617678887469994371567851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3294287399839969981695205 617678887469994371567851)
                    ·
                      rfl

theorem cell22_1804388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 4, 2, 2, 4].length) (baseStart_1804388 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1804388 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1804388 prefixEnd_1804388 := by exact prefixLift 1804388
  have htrace : WordTrace (prefixWord ++ tailWord_1804388) baseStart_1804388 baseEnd_1804388 := by
    simpa [prefixWord, tailWord_1804388, baseEnd_1804388] using wordTrace_append hprefix tailTrace_1804388
  have hstable : (prefixWord ++ tailWord_1804388).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1804388).length < 2 ^ (prefixWord ++ tailWord_1804388).sum := by decide
  have hdescent : baseEnd_1804388 < baseStart_1804388 := by decide
  rcases family_descends (prefixWord ++ tailWord_1804388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1804416 : List Nat := [2, 1, 1, 2, 1, 3, 1, 1, 4, 6]
def baseStart_1804416 : Nat := 118140960795 + 1804416 * 2 ^ 59
def prefixEnd_1804416 : Nat := 4983230072969 + 3 ^ 40 * 1804416 * 2
def baseEnd_1804416 : Nat := 617688472442211631867765

theorem tailTrace_1804416 : CollatzResearch.WordTrace tailWord_1804416 prefixEnd_1804416 617688472442211631867765 := by
  unfold tailWord_1804416
  simp only [CollatzResearch.WordTrace]
  refine ⟨32906229115458238281632551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43874972153944317708843401 32906229115458238281632551)
  ·
    refine ⟨49359343673187357422448827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32906229115458238281632551 49359343673187357422448827)
    ·
      refine ⟨74039015509781036133673241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49359343673187357422448827 74039015509781036133673241)
      ·
        refine ⟨55529261632335777100254931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74039015509781036133673241 55529261632335777100254931)
        ·
          refine ⟨83293892448503665650382397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55529261632335777100254931 83293892448503665650382397)
          ·
            refine ⟨31235209668188874618893399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83293892448503665650382397 31235209668188874618893399)
            ·
              refine ⟨46852814502283311928340099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31235209668188874618893399 46852814502283311928340099)
              ·
                refine ⟨70279221753424967892510149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46852814502283311928340099 70279221753424967892510149)
                ·
                  refine ⟨13177354078767181479845653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 70279221753424967892510149 13177354078767181479845653)
                  ·
                    refine ⟨617688472442211631867765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13177354078767181479845653 617688472442211631867765)
                    ·
                      rfl

theorem cell22_1804416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 1, 4, 6].length) (baseStart_1804416 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1804416 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1804416 prefixEnd_1804416 := by exact prefixLift 1804416
  have htrace : WordTrace (prefixWord ++ tailWord_1804416) baseStart_1804416 baseEnd_1804416 := by
    simpa [prefixWord, tailWord_1804416, baseEnd_1804416] using wordTrace_append hprefix tailTrace_1804416
  have hstable : (prefixWord ++ tailWord_1804416).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1804416).length < 2 ^ (prefixWord ++ tailWord_1804416).sum := by decide
  have hdescent : baseEnd_1804416 < baseStart_1804416 := by decide
  rcases family_descends (prefixWord ++ tailWord_1804416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1804448 : List Nat := [2, 1, 1, 4, 2, 3, 1, 1, 7]
def baseStart_1804448 : Nat := 118140960795 + 1804448 * 2 ^ 59
def prefixEnd_1804448 : Nat := 4983230072969 + 3 ^ 40 * 1804448 * 2
def baseEnd_1804448 : Nat := 205899808898724738355889

theorem tailTrace_1804448 : CollatzResearch.WordTrace tailWord_1804448 prefixEnd_1804448 205899808898724738355889 := by
  unfold tailWord_1804448
  simp only [CollatzResearch.WordTrace]
  refine ⟨32906812683400273014214999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43875750244533697352286665 32906812683400273014214999)
  ·
    refine ⟨49360219025100409521322499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32906812683400273014214999 49360219025100409521322499)
    ·
      refine ⟨74040328537650614281983749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49360219025100409521322499 74040328537650614281983749)
      ·
        refine ⟨13882561600809490177871953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74040328537650614281983749 13882561600809490177871953)
        ·
          refine ⟨10411921200607117633403965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13882561600809490177871953 10411921200607117633403965)
          ·
            refine ⟨3904470450227669112526487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10411921200607117633403965 3904470450227669112526487)
            ·
              refine ⟨5856705675341503668789731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3904470450227669112526487 5856705675341503668789731)
              ·
                refine ⟨8785058513012255503184597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5856705675341503668789731 8785058513012255503184597)
                ·
                  refine ⟨205899808898724738355889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8785058513012255503184597 205899808898724738355889)
                  ·
                    rfl

theorem cell22_1804448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 1, 1, 7].length) (baseStart_1804448 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1804448 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1804448 prefixEnd_1804448 := by exact prefixLift 1804448
  have htrace : WordTrace (prefixWord ++ tailWord_1804448) baseStart_1804448 baseEnd_1804448 := by
    simpa [prefixWord, tailWord_1804448, baseEnd_1804448] using wordTrace_append hprefix tailTrace_1804448
  have hstable : (prefixWord ++ tailWord_1804448).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1804448).length < 2 ^ (prefixWord ++ tailWord_1804448).sum := by decide
  have hdescent : baseEnd_1804448 < baseStart_1804448 := by decide
  rcases family_descends (prefixWord ++ tailWord_1804448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1804452 : List Nat := [2, 3, 1, 2, 4, 1, 2, 1, 3, 3]
def baseStart_1804452 : Nat := 118140960795 + 1804452 * 2 ^ 59
def prefixEnd_1804452 : Nat := 4983230072969 + 3 ^ 40 * 1804452 * 2
def baseEnd_1804452 : Nat := 617700795977919537967655

theorem tailTrace_1804452 : CollatzResearch.WordTrace tailWord_1804452 prefixEnd_1804452 617700795977919537967655 := by
  unfold tailWord_1804452
  simp only [CollatzResearch.WordTrace]
  refine ⟨32906885629393027355787805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43875847505857369807717073 32906885629393027355787805)
  ·
    refine ⟨12340082111022385258420427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32906885629393027355787805 12340082111022385258420427)
    ·
      refine ⟨18510123166533577887630641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12340082111022385258420427 18510123166533577887630641)
      ·
        refine ⟨13882592374900183415722981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18510123166533577887630641 13882592374900183415722981)
        ·
          refine ⟨2602986070293784390448059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13882592374900183415722981 2602986070293784390448059)
          ·
            refine ⟨3904479105440676585672089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2602986070293784390448059 3904479105440676585672089)
            ·
              refine ⟨2928359329080507439254067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3904479105440676585672089 2928359329080507439254067)
              ·
                refine ⟨4392538993620761158881101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2928359329080507439254067 4392538993620761158881101)
                ·
                  refine ⟨1647202122607785434580413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4392538993620761158881101 1647202122607785434580413)
                  ·
                    refine ⟨617700795977919537967655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1647202122607785434580413 617700795977919537967655)
                    ·
                      rfl

theorem cell22_1804452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 2, 1, 3, 3].length) (baseStart_1804452 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1804452 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1804452 prefixEnd_1804452 := by exact prefixLift 1804452
  have htrace : WordTrace (prefixWord ++ tailWord_1804452) baseStart_1804452 baseEnd_1804452 := by
    simpa [prefixWord, tailWord_1804452, baseEnd_1804452] using wordTrace_append hprefix tailTrace_1804452
  have hstable : (prefixWord ++ tailWord_1804452).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1804452).length < 2 ^ (prefixWord ++ tailWord_1804452).sum := by decide
  have hdescent : baseEnd_1804452 < baseStart_1804452 := by decide
  rcases family_descends (prefixWord ++ tailWord_1804452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1804482 : List Nat := [3, 5, 1, 1, 1, 1, 1, 2, 7]
def baseStart_1804482 : Nat := 118140960795 + 1804482 * 2 ^ 59
def prefixEnd_1804482 : Nat := 4983230072969 + 3 ^ 40 * 1804482 * 2
def baseEnd_1804482 : Nat := 205903688530336486572521

theorem tailTrace_1804482 : CollatzResearch.WordTrace tailWord_1804482 prefixEnd_1804482 205903688530336486572521 := by
  unfold tailWord_1804482
  simp only [CollatzResearch.WordTrace]
  refine ⟨16453716362169342458791925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43876576965784913223445133 16453716362169342458791925)
  ·
    refine ⟨1542535908953375855511743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 16453716362169342458791925 1542535908953375855511743)
    ·
      refine ⟨2313803863430063783267615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1542535908953375855511743 2313803863430063783267615)
      ·
        refine ⟨3470705795145095674901423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2313803863430063783267615 3470705795145095674901423)
        ·
          refine ⟨5206058692717643512352135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3470705795145095674901423 5206058692717643512352135)
          ·
            refine ⟨7809088039076465268528203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5206058692717643512352135 7809088039076465268528203)
            ·
              refine ⟨11713632058614697902792305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7809088039076465268528203 11713632058614697902792305)
              ·
                refine ⟨8785224043961023427094229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11713632058614697902792305 8785224043961023427094229)
                ·
                  refine ⟨205903688530336486572521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8785224043961023427094229 205903688530336486572521)
                  ·
                    rfl

theorem cell22_1804482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 2, 7].length) (baseStart_1804482 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1804482 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1804482 prefixEnd_1804482 := by exact prefixLift 1804482
  have htrace : WordTrace (prefixWord ++ tailWord_1804482) baseStart_1804482 baseEnd_1804482 := by
    simpa [prefixWord, tailWord_1804482, baseEnd_1804482] using wordTrace_append hprefix tailTrace_1804482
  have hstable : (prefixWord ++ tailWord_1804482).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1804482).length < 2 ^ (prefixWord ++ tailWord_1804482).sum := by decide
  have hdescent : baseEnd_1804482 < baseStart_1804482 := by decide
  rcases family_descends (prefixWord ++ tailWord_1804482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1804523 : List Nat := [1, 1, 1, 1, 2, 5, 1, 2, 4, 4]
def baseStart_1804523 : Nat := 118140960795 + 1804523 * 2 ^ 59
def prefixEnd_1804523 : Nat := 4983230072969 + 3 ^ 40 * 1804523 * 2
def baseEnd_1804523 : Nat := 617725100728899019442437

theorem tailTrace_1804523 : CollatzResearch.WordTrace tailWord_1804523 prefixEnd_1804523 617725100728899019442437 := by
  unfold tailWord_1804523
  simp only [CollatzResearch.WordTrace]
  refine ⟨65816360841528833837410223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43877573894352555891606815 65816360841528833837410223)
  ·
    refine ⟨98724541262293250756115335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65816360841528833837410223 98724541262293250756115335)
    ·
      refine ⟨148086811893439876134173003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98724541262293250756115335 148086811893439876134173003)
      ·
        refine ⟨222130217840159814201259505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148086811893439876134173003 222130217840159814201259505)
        ·
          refine ⟨166597663380119860650944629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 222130217840159814201259505 166597663380119860650944629)
          ·
            refine ⟨15618530941886236936026059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 166597663380119860650944629 15618530941886236936026059)
            ·
              refine ⟨23427796412829355404039089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15618530941886236936026059 23427796412829355404039089)
              ·
                refine ⟨17570847309622016553029317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23427796412829355404039089 17570847309622016553029317)
                ·
                  refine ⟨3294533870554128103692997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17570847309622016553029317 3294533870554128103692997)
                  ·
                    refine ⟨617725100728899019442437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3294533870554128103692997 617725100728899019442437)
                    ·
                      rfl

theorem cell22_1804523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 2, 4, 4].length) (baseStart_1804523 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1804523 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1804523 prefixEnd_1804523 := by exact prefixLift 1804523
  have htrace : WordTrace (prefixWord ++ tailWord_1804523) baseStart_1804523 baseEnd_1804523 := by
    simpa [prefixWord, tailWord_1804523, baseEnd_1804523] using wordTrace_append hprefix tailTrace_1804523
  have hstable : (prefixWord ++ tailWord_1804523).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1804523).length < 2 ^ (prefixWord ++ tailWord_1804523).sum := by decide
  have hdescent : baseEnd_1804523 < baseStart_1804523 := by decide
  rcases family_descends (prefixWord ++ tailWord_1804523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1804538 : List Nat := [3, 1, 1, 1, 1, 5, 2, 8]
def baseStart_1804538 : Nat := 118140960795 + 1804538 * 2 ^ 59
def prefixEnd_1804538 : Nat := 4983230072969 + 3 ^ 40 * 1804538 * 2
def baseEnd_1804538 : Nat := 68636692837271553368599

theorem tailTrace_1804538 : CollatzResearch.WordTrace tailWord_1804538 prefixEnd_1804538 68636692837271553368599 := by
  unfold tailWord_1804538
  simp only [CollatzResearch.WordTrace]
  refine ⟨16454226984118622849801567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43877938624316327599470845 16454226984118622849801567)
  ·
    refine ⟨24681340476177934274702351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16454226984118622849801567 24681340476177934274702351)
    ·
      refine ⟨37022010714266901412053527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24681340476177934274702351 37022010714266901412053527)
      ·
        refine ⟨55533016071400352118080291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37022010714266901412053527 55533016071400352118080291)
        ·
          refine ⟨83299524107100528177120437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55533016071400352118080291 83299524107100528177120437)
          ·
            refine ⟨7809330385040674516605041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 83299524107100528177120437 7809330385040674516605041)
            ·
              refine ⟨5856997788780505887453781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7809330385040674516605041 5856997788780505887453781)
              ·
                refine ⟨68636692837271553368599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5856997788780505887453781 68636692837271553368599)
                ·
                  rfl

theorem cell22_1804538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 2, 8].length) (baseStart_1804538 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1804538 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1804538 prefixEnd_1804538 := by exact prefixLift 1804538
  have htrace : WordTrace (prefixWord ++ tailWord_1804538) baseStart_1804538 baseEnd_1804538 := by
    simpa [prefixWord, tailWord_1804538, baseEnd_1804538] using wordTrace_append hprefix tailTrace_1804538
  have hstable : (prefixWord ++ tailWord_1804538).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1804538).length < 2 ^ (prefixWord ++ tailWord_1804538).sum := by decide
  have hdescent : baseEnd_1804538 < baseStart_1804538 := by decide
  rcases family_descends (prefixWord ++ tailWord_1804538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1804540 : List Nat := [2, 2, 2, 1, 4, 1, 1, 3, 2, 4]
def baseStart_1804540 : Nat := 118140960795 + 1804540 * 2 ^ 59
def prefixEnd_1804540 : Nat := 4983230072969 + 3 ^ 40 * 1804540 * 2
def baseEnd_1804540 : Nat := 617730920176316641767385

theorem tailTrace_1804540 : CollatzResearch.WordTrace tailWord_1804540 prefixEnd_1804540 617730920176316641767385 := by
  unfold tailWord_1804540
  simp only [CollatzResearch.WordTrace]
  refine ⟨32908490441233622870389537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43877987254978163827186049 32908490441233622870389537)
  ·
    refine ⟨24681367830925217152792153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32908490441233622870389537 24681367830925217152792153)
    ·
      refine ⟨18511025873193912864594115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24681367830925217152792153 18511025873193912864594115)
      ·
        refine ⟨27766538809790869296891173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18511025873193912864594115 27766538809790869296891173)
        ·
          refine ⟨5206226026835787993167095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27766538809790869296891173 5206226026835787993167095)
          ·
            refine ⟨7809339040253681989750643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5206226026835787993167095 7809339040253681989750643)
            ·
              refine ⟨11714008560380522984625965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7809339040253681989750643 11714008560380522984625965)
              ·
                refine ⟨4392753210142696119234737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11714008560380522984625965 4392753210142696119234737)
                ·
                  refine ⟨3294564907607022089426053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4392753210142696119234737 3294564907607022089426053)
                  ·
                    refine ⟨617730920176316641767385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3294564907607022089426053 617730920176316641767385)
                    ·
                      rfl

theorem cell22_1804540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 3, 2, 4].length) (baseStart_1804540 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1804540 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1804540 prefixEnd_1804540 := by exact prefixLift 1804540
  have htrace : WordTrace (prefixWord ++ tailWord_1804540) baseStart_1804540 baseEnd_1804540 := by
    simpa [prefixWord, tailWord_1804540, baseEnd_1804540] using wordTrace_append hprefix tailTrace_1804540
  have hstable : (prefixWord ++ tailWord_1804540).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1804540).length < 2 ^ (prefixWord ++ tailWord_1804540).sum := by decide
  have hdescent : baseEnd_1804540 < baseStart_1804540 := by decide
  rcases family_descends (prefixWord ++ tailWord_1804540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1804568 : List Nat := [2, 1, 2, 3, 1, 2, 1, 1, 1, 8]
def baseStart_1804568 : Nat := 118140960795 + 1804568 * 2 ^ 59
def prefixEnd_1804568 : Nat := 4983230072969 + 3 ^ 40 * 1804568 * 2
def baseEnd_1804568 : Nat := 617740505148533902067299

theorem tailTrace_1804568 : CollatzResearch.WordTrace tailWord_1804568 prefixEnd_1804568 617740505148533902067299 := by
  unfold tailWord_1804568
  simp only [CollatzResearch.WordTrace]
  refine ⟨32909001063182903261399179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43878668084243871015198905 32909001063182903261399179)
  ·
    refine ⟨49363501594774354892098769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32909001063182903261399179 49363501594774354892098769)
    ·
      refine ⟨37022626196080766169074077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49363501594774354892098769 37022626196080766169074077)
      ·
        refine ⟨13883484823530287313402779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37022626196080766169074077 13883484823530287313402779)
        ·
          refine ⟨20825227235295430970104169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13883484823530287313402779 20825227235295430970104169)
          ·
            refine ⟨15618920426471573227578127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20825227235295430970104169 15618920426471573227578127)
            ·
              refine ⟨23428380639707359841367191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15618920426471573227578127 23428380639707359841367191)
              ·
                refine ⟨35142570959561039762050787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23428380639707359841367191 35142570959561039762050787)
                ·
                  refine ⟨52713856439341559643076181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35142570959561039762050787 52713856439341559643076181)
                  ·
                    refine ⟨617740505148533902067299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 52713856439341559643076181 617740505148533902067299)
                    ·
                      rfl

theorem cell22_1804568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 1, 1, 8].length) (baseStart_1804568 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1804568 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1804568 prefixEnd_1804568 := by exact prefixLift 1804568
  have htrace : WordTrace (prefixWord ++ tailWord_1804568) baseStart_1804568 baseEnd_1804568 := by
    simpa [prefixWord, tailWord_1804568, baseEnd_1804568] using wordTrace_append hprefix tailTrace_1804568
  have hstable : (prefixWord ++ tailWord_1804568).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1804568).length < 2 ^ (prefixWord ++ tailWord_1804568).sum := by decide
  have hdescent : baseEnd_1804568 < baseStart_1804568 := by decide
  rcases family_descends (prefixWord ++ tailWord_1804568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1804589 : List Nat := [1, 5, 3, 1, 2, 1, 3, 6]
def baseStart_1804589 : Nat := 118140960795 + 1804589 * 2 ^ 59
def prefixEnd_1804589 : Nat := 4983230072969 + 3 ^ 40 * 1804589 * 2
def baseEnd_1804589 : Nat := 68638632653077427476915

theorem tailTrace_1804589 : CollatzResearch.WordTrace tailWord_1804589 prefixEnd_1804589 68638632653077427476915 := by
  unfold tailWord_1804589
  simp only [CollatzResearch.WordTrace]
  refine ⟨65818768059289727109312821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43879178706193151406208547 65818768059289727109312821)
  ·
    refine ⟨6170509505558411916498077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 65818768059289727109312821 6170509505558411916498077)
    ·
      refine ⟨2313941064584404468686779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6170509505558411916498077 2313941064584404468686779)
      ·
        refine ⟨3470911596876606703030169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2313941064584404468686779 3470911596876606703030169)
        ·
          refine ⟨2603183697657455027272627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3470911596876606703030169 2603183697657455027272627)
          ·
            refine ⟨3904775546486182540908941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2603183697657455027272627 3904775546486182540908941)
            ·
              refine ⟨1464290829932318452840853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3904775546486182540908941 1464290829932318452840853)
              ·
                refine ⟨68638632653077427476915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1464290829932318452840853 68638632653077427476915)
                ·
                  rfl

theorem cell22_1804589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 3, 6].length) (baseStart_1804589 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1804589 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1804589 prefixEnd_1804589 := by exact prefixLift 1804589
  have htrace : WordTrace (prefixWord ++ tailWord_1804589) baseStart_1804589 baseEnd_1804589 := by
    simpa [prefixWord, tailWord_1804589, baseEnd_1804589] using wordTrace_append hprefix tailTrace_1804589
  have hstable : (prefixWord ++ tailWord_1804589).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1804589).length < 2 ^ (prefixWord ++ tailWord_1804589).sum := by decide
  have hdescent : baseEnd_1804589 < baseStart_1804589 := by decide
  rcases family_descends (prefixWord ++ tailWord_1804589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1804604 : List Nat := [2, 2, 2, 2, 1, 2, 4, 3, 1, 3]
def baseStart_1804604 : Nat := 118140960795 + 1804604 * 2 ^ 59
def prefixEnd_1804604 : Nat := 4983230072969 + 3 ^ 40 * 1804604 * 2
def baseEnd_1804604 : Nat := 617752828684241808167189

theorem tailTrace_1804604 : CollatzResearch.WordTrace tailWord_1804604 prefixEnd_1804604 617752828684241808167189 := by
  unfold tailWord_1804604
  simp only [CollatzResearch.WordTrace]
  refine ⟨32909657577117692335554433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43879543436156923114072577 32909657577117692335554433)
  ·
    refine ⟨24682243182838269251665825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32909657577117692335554433 24682243182838269251665825)
    ·
      refine ⟨18511682387128701938749369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24682243182838269251665825 18511682387128701938749369)
      ·
        refine ⟨13883761790346526454062027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18511682387128701938749369 13883761790346526454062027)
        ·
          refine ⟨20825642685519789681093041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13883761790346526454062027 20825642685519789681093041)
          ·
            refine ⟨15619232014139842260819781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20825642685519789681093041 15619232014139842260819781)
            ·
              refine ⟨2928606002651220423903709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15619232014139842260819781 2928606002651220423903709)
              ·
                refine ⟨1098227250994207658963891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2928606002651220423903709 1098227250994207658963891)
                ·
                  refine ⟨1647340876491311488445837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1098227250994207658963891 1647340876491311488445837)
                  ·
                    refine ⟨617752828684241808167189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1647340876491311488445837 617752828684241808167189)
                    ·
                      rfl

theorem cell22_1804604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 4, 3, 1, 3].length) (baseStart_1804604 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1804604 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1804604 prefixEnd_1804604 := by exact prefixLift 1804604
  have htrace : WordTrace (prefixWord ++ tailWord_1804604) baseStart_1804604 baseEnd_1804604 := by
    simpa [prefixWord, tailWord_1804604, baseEnd_1804604] using wordTrace_append hprefix tailTrace_1804604
  have hstable : (prefixWord ++ tailWord_1804604).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1804604).length < 2 ^ (prefixWord ++ tailWord_1804604).sum := by decide
  have hdescent : baseEnd_1804604 < baseStart_1804604 := by decide
  rcases family_descends (prefixWord ++ tailWord_1804604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1804645 : List Nat := [1, 3, 1, 3, 1, 3, 2, 2, 6]
def baseStart_1804645 : Nat := 118140960795 + 1804645 * 2 ^ 59
def prefixEnd_1804645 : Nat := 4983230072969 + 3 ^ 40 * 1804645 * 2
def baseEnd_1804645 : Nat := 205922287940710455964021

theorem tailTrace_1804645 : CollatzResearch.WordTrace tailWord_1804645 prefixEnd_1804645 205922287940710455964021 := by
  unfold tailWord_1804645
  simp only [CollatzResearch.WordTrace]
  refine ⟨65820810547086848673351389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43880540364724565782234259 65820810547086848673351389)
  ·
    refine ⟨24682803955157568252506771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65820810547086848673351389 24682803955157568252506771)
    ·
      refine ⟨37024205932736352378760157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24682803955157568252506771 37024205932736352378760157)
      ·
        refine ⟨13884077224776132142035059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37024205932736352378760157 13884077224776132142035059)
        ·
          refine ⟨20826115837164198213052589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13884077224776132142035059 20826115837164198213052589)
          ·
            refine ⟨7809793438936574329894721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20826115837164198213052589 7809793438936574329894721)
            ·
              refine ⟨5857345079202430747421041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7809793438936574329894721 5857345079202430747421041)
              ·
                refine ⟨4393008809401823060565781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5857345079202430747421041 4393008809401823060565781)
                ·
                  refine ⟨205922287940710455964021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4393008809401823060565781 205922287940710455964021)
                  ·
                    rfl

theorem cell22_1804645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 2, 2, 6].length) (baseStart_1804645 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1804645 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1804645 prefixEnd_1804645 := by exact prefixLift 1804645
  have htrace : WordTrace (prefixWord ++ tailWord_1804645) baseStart_1804645 baseEnd_1804645 := by
    simpa [prefixWord, tailWord_1804645, baseEnd_1804645] using wordTrace_append hprefix tailTrace_1804645
  have hstable : (prefixWord ++ tailWord_1804645).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1804645).length < 2 ^ (prefixWord ++ tailWord_1804645).sum := by decide
  have hdescent : baseEnd_1804645 < baseStart_1804645 := by decide
  rcases family_descends (prefixWord ++ tailWord_1804645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1804647 : List Nat := [1, 1, 5, 1, 3, 1, 1, 4, 1, 4]
def baseStart_1804647 : Nat := 118140960795 + 1804647 * 2 ^ 59
def prefixEnd_1804647 : Nat := 4983230072969 + 3 ^ 40 * 1804647 * 2
def baseEnd_1804647 : Nat := 617767548463004029342057

theorem tailTrace_1804647 : CollatzResearch.WordTrace tailWord_1804647 prefixEnd_1804647 617767548463004029342057 := by
  unfold tailWord_1804647
  simp only [CollatzResearch.WordTrace]
  refine ⟨65820883493079603014924195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43880588995386402009949463 65820883493079603014924195)
  ·
    refine ⟨98731325239619404522386293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65820883493079603014924195 98731325239619404522386293)
    ·
      refine ⟨9256061741214319173973715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 98731325239619404522386293 9256061741214319173973715)
      ·
        refine ⟨13884092611821478760960573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9256061741214319173973715 13884092611821478760960573)
        ·
          refine ⟨5206534729433054535360215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13884092611821478760960573 5206534729433054535360215)
          ·
            refine ⟨7809802094149581803040323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5206534729433054535360215 7809802094149581803040323)
            ·
              refine ⟨11714703141224372704560485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7809802094149581803040323 11714703141224372704560485)
              ·
                refine ⟨2196506838979569882105091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11714703141224372704560485 2196506838979569882105091)
                ·
                  refine ⟨3294760258469354823157637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2196506838979569882105091 3294760258469354823157637)
                  ·
                    refine ⟨617767548463004029342057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3294760258469354823157637 617767548463004029342057)
                    ·
                      rfl

theorem cell22_1804647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 4, 1, 4].length) (baseStart_1804647 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1804647 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1804647 prefixEnd_1804647 := by exact prefixLift 1804647
  have htrace : WordTrace (prefixWord ++ tailWord_1804647) baseStart_1804647 baseEnd_1804647 := by
    simpa [prefixWord, tailWord_1804647, baseEnd_1804647] using wordTrace_append hprefix tailTrace_1804647
  have hstable : (prefixWord ++ tailWord_1804647).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1804647).length < 2 ^ (prefixWord ++ tailWord_1804647).sum := by decide
  have hdescent : baseEnd_1804647 < baseStart_1804647 := by decide
  rcases family_descends (prefixWord ++ tailWord_1804647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1804677 : List Nat := [1, 3, 1, 1, 3, 1, 1, 6, 2, 3]
def baseStart_1804677 : Nat := 118140960795 + 1804677 * 2 ^ 59
def prefixEnd_1804677 : Nat := 4983230072969 + 3 ^ 40 * 1804677 * 2
def baseEnd_1804677 : Nat := 617777818076093951091965

theorem tailTrace_1804677 : CollatzResearch.WordTrace tailWord_1804677 prefixEnd_1804677 617777818076093951091965 := by
  unfold tailWord_1804677
  simp only [CollatzResearch.WordTrace]
  refine ⟨65821977682970918138516285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43881318455313945425677523 65821977682970918138516285)
  ·
    refine ⟨24683241631114094301943607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65821977682970918138516285 24683241631114094301943607)
    ·
      refine ⟨37024862446671141452915411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24683241631114094301943607 37024862446671141452915411)
      ·
        refine ⟨55537293670006712179373117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37024862446671141452915411 55537293670006712179373117)
        ·
          refine ⟨20826485126252517067264919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55537293670006712179373117 20826485126252517067264919)
          ·
            refine ⟨31239727689378775600897379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20826485126252517067264919 31239727689378775600897379)
            ·
              refine ⟨46859591534068163401346069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31239727689378775600897379 46859591534068163401346069)
              ·
                refine ⟨2196543353159445159438097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 46859591534068163401346069 2196543353159445159438097)
                ·
                  refine ⟨1647407514869583869578573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2196543353159445159438097 1647407514869583869578573)
                  ·
                    refine ⟨617777818076093951091965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1647407514869583869578573 617777818076093951091965)
                    ·
                      rfl

theorem cell22_1804677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 6, 2, 3].length) (baseStart_1804677 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1804677 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1804677 prefixEnd_1804677 := by exact prefixLift 1804677
  have htrace : WordTrace (prefixWord ++ tailWord_1804677) baseStart_1804677 baseEnd_1804677 := by
    simpa [prefixWord, tailWord_1804677, baseEnd_1804677] using wordTrace_append hprefix tailTrace_1804677
  have hstable : (prefixWord ++ tailWord_1804677).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1804677).length < 2 ^ (prefixWord ++ tailWord_1804677).sum := by decide
  have hdescent : baseEnd_1804677 < baseStart_1804677 := by decide
  rcases family_descends (prefixWord ++ tailWord_1804677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1804679 : List Nat := [1, 1, 4, 2, 2, 1, 5, 2, 4]
def baseStart_1804679 : Nat := 118140960795 + 1804679 * 2 ^ 59
def prefixEnd_1804679 : Nat := 4983230072969 + 3 ^ 40 * 1804679 * 2
def baseEnd_1804679 : Nat := 205926167572322204180653

theorem tailTrace_1804679 : CollatzResearch.WordTrace tailWord_1804679 prefixEnd_1804679 205926167572322204180653 := by
  unfold tailWord_1804679
  simp only [CollatzResearch.WordTrace]
  refine ⟨65822050628963672480089091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43881367085975781653392727 65822050628963672480089091)
  ·
    refine ⟨98733075943445508720133637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65822050628963672480089091 98733075943445508720133637)
    ·
      refine ⟨18512451739396032885025057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 98733075943445508720133637 18512451739396032885025057)
      ·
        refine ⟨13884338804547024663768793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18512451739396032885025057 13884338804547024663768793)
        ·
          refine ⟨10413254103410268497826595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13884338804547024663768793 10413254103410268497826595)
          ·
            refine ⟨15619881155115402746739893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10413254103410268497826595 15619881155115402746739893)
            ·
              refine ⟨1464363858292069007506865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15619881155115402746739893 1464363858292069007506865)
              ·
                refine ⟨1098272893719051755630149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1464363858292069007506865 1098272893719051755630149)
                ·
                  refine ⟨205926167572322204180653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1098272893719051755630149 205926167572322204180653)
                  ·
                    rfl

theorem cell22_1804679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 5, 2, 4].length) (baseStart_1804679 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1804679 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1804679 prefixEnd_1804679 := by exact prefixLift 1804679
  have htrace : WordTrace (prefixWord ++ tailWord_1804679) baseStart_1804679 baseEnd_1804679 := by
    simpa [prefixWord, tailWord_1804679, baseEnd_1804679] using wordTrace_append hprefix tailTrace_1804679
  have hstable : (prefixWord ++ tailWord_1804679).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1804679).length < 2 ^ (prefixWord ++ tailWord_1804679).sum := by decide
  have hdescent : baseEnd_1804679 < baseStart_1804679 := by decide
  rcases family_descends (prefixWord ++ tailWord_1804679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1804724 : List Nat := [2, 5, 2, 2, 1, 10]
def baseStart_1804724 : Nat := 118140960795 + 1804724 * 2 ^ 59
def prefixEnd_1804724 : Nat := 4983230072969 + 3 ^ 40 * 1804724 * 2
def baseEnd_1804724 : Nat := 7627085273291376483541

theorem tailTrace_1804724 : CollatzResearch.WordTrace tailWord_1804724 prefixEnd_1804724 7627085273291376483541 := by
  unfold tailWord_1804724
  simp only [CollatzResearch.WordTrace]
  refine ⟨32911845956900322582738613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43882461275867096776984817 32911845956900322582738613)
  ·
    refine ⟨3085485558459405242131745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 32911845956900322582738613 3085485558459405242131745)
    ·
      refine ⟨2314114168844553931598809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3085485558459405242131745 2314114168844553931598809)
      ·
        refine ⟨1735585626633415448699107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2314114168844553931598809 1735585626633415448699107)
        ·
          refine ⟨2603378439950123173048661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1735585626633415448699107 2603378439950123173048661)
          ·
            refine ⟨7627085273291376483541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 2603378439950123173048661 7627085273291376483541)
            ·
              rfl

theorem cell22_1804724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 10].length) (baseStart_1804724 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1804724 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1804724 prefixEnd_1804724 := by exact prefixLift 1804724
  have htrace : WordTrace (prefixWord ++ tailWord_1804724) baseStart_1804724 baseEnd_1804724 := by
    simpa [prefixWord, tailWord_1804724, baseEnd_1804724] using wordTrace_append hprefix tailTrace_1804724
  have hstable : (prefixWord ++ tailWord_1804724).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1804724).length < 2 ^ (prefixWord ++ tailWord_1804724).sum := by decide
  have hdescent : baseEnd_1804724 < baseStart_1804724 := by decide
  rcases family_descends (prefixWord ++ tailWord_1804724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1804773 : List Nat := [1, 3, 1, 5, 2, 1, 2, 3, 1, 3]
def baseStart_1804773 : Nat := 118140960795 + 1804773 * 2 ^ 59
def prefixEnd_1804773 : Nat := 4983230072969 + 3 ^ 40 * 1804773 * 2
def baseEnd_1804773 : Nat := 617810680837981700691671

theorem tailTrace_1804773 : CollatzResearch.WordTrace tailWord_1804773 prefixEnd_1804773 617810680837981700691671 := by
  unfold tailWord_1804773
  simp only [CollatzResearch.WordTrace]
  refine ⟨65825479090623126534010973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43883652727082084356007315 65825479090623126534010973)
  ·
    refine ⟨24684554658983672450254115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65825479090623126534010973 24684554658983672450254115)
    ·
      refine ⟨37026831988475508675381173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24684554658983672450254115 37026831988475508675381173)
      ·
        refine ⟨3471265498919578938316985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 37026831988475508675381173 3471265498919578938316985)
        ·
          refine ⟨2603449124189684203737739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3471265498919578938316985 2603449124189684203737739)
          ·
            refine ⟨3905173686284526305606609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2603449124189684203737739 3905173686284526305606609)
            ·
              refine ⟨2928880264713394729204957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3905173686284526305606609 2928880264713394729204957)
              ·
                refine ⟨1098330099267523023451859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2928880264713394729204957 1098330099267523023451859)
                ·
                  refine ⟨1647495148901284535177789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1098330099267523023451859 1647495148901284535177789)
                  ·
                    refine ⟨617810680837981700691671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1647495148901284535177789 617810680837981700691671)
                    ·
                      rfl

theorem cell22_1804773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 2, 3, 1, 3].length) (baseStart_1804773 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1804773 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1804773 prefixEnd_1804773 := by exact prefixLift 1804773
  have htrace : WordTrace (prefixWord ++ tailWord_1804773) baseStart_1804773 baseEnd_1804773 := by
    simpa [prefixWord, tailWord_1804773, baseEnd_1804773] using wordTrace_append hprefix tailTrace_1804773
  have hstable : (prefixWord ++ tailWord_1804773).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1804773).length < 2 ^ (prefixWord ++ tailWord_1804773).sum := by decide
  have hdescent : baseEnd_1804773 < baseStart_1804773 := by decide
  rcases family_descends (prefixWord ++ tailWord_1804773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1804780 : List Nat := [2, 2, 1, 1, 2, 1, 3, 2, 8]
def baseStart_1804780 : Nat := 118140960795 + 1804780 * 2 ^ 59
def prefixEnd_1804780 : Nat := 4983230072969 + 3 ^ 40 * 1804780 * 2
def baseEnd_1804780 : Nat := 205937692360345338588883

theorem tailTrace_1804780 : CollatzResearch.WordTrace tailWord_1804780 prefixEnd_1804780 205937692360345338588883 := by
  unfold tailWord_1804780
  simp only [CollatzResearch.WordTrace]
  refine ⟨32912867200798883364757897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43883822934398511153010529 32912867200798883364757897)
  ·
    refine ⟨24684650400599162523568423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32912867200798883364757897 24684650400599162523568423)
    ·
      refine ⟨37026975600898743785352635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24684650400599162523568423 37026975600898743785352635)
      ·
        refine ⟨55540463401348115678028953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37026975600898743785352635 55540463401348115678028953)
        ·
          refine ⟨41655347551011086758521715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55540463401348115678028953 41655347551011086758521715)
          ·
            refine ⟨62483021326516630137782573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41655347551011086758521715 62483021326516630137782573)
            ·
              refine ⟨23431132997443736301668465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62483021326516630137782573 23431132997443736301668465)
              ·
                refine ⟨17573349748082802226251349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23431132997443736301668465 17573349748082802226251349)
                ·
                  refine ⟨205937692360345338588883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 17573349748082802226251349 205937692360345338588883)
                  ·
                    rfl

theorem cell22_1804780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 8].length) (baseStart_1804780 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1804780 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1804780 prefixEnd_1804780 := by exact prefixLift 1804780
  have htrace : WordTrace (prefixWord ++ tailWord_1804780) baseStart_1804780 baseEnd_1804780 := by
    simpa [prefixWord, tailWord_1804780, baseEnd_1804780] using wordTrace_append hprefix tailTrace_1804780
  have hstable : (prefixWord ++ tailWord_1804780).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1804780).length < 2 ^ (prefixWord ++ tailWord_1804780).sum := by decide
  have hdescent : baseEnd_1804780 < baseStart_1804780 := by decide
  rcases family_descends (prefixWord ++ tailWord_1804780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1804786 : List Nat := [3, 2, 1, 4, 2, 2, 1, 2, 5]
def baseStart_1804786 : Nat := 118140960795 + 1804786 * 2 ^ 59
def prefixEnd_1804786 : Nat := 4983230072969 + 3 ^ 40 * 1804786 * 2
def baseEnd_1804786 : Nat := 205938377001218000038877

theorem tailTrace_1804786 : CollatzResearch.WordTrace tailWord_1804786 prefixEnd_1804786 205938377001218000038877 := by
  unfold tailWord_1804786
  simp only [CollatzResearch.WordTrace]
  refine ⟨16456488309894007438558553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43883968826384019836156141 16456488309894007438558553)
  ·
    refine ⟨12342366232420505578918915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16456488309894007438558553 12342366232420505578918915)
    ·
      refine ⟨18513549348630758368378373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12342366232420505578918915 18513549348630758368378373)
      ·
        refine ⟨3471290502868267194070945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18513549348630758368378373 3471290502868267194070945)
        ·
          refine ⟨2603467877151200395553209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3471290502868267194070945 2603467877151200395553209)
          ·
            refine ⟨1952600907863400296664907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2603467877151200395553209 1952600907863400296664907)
            ·
              refine ⟨2928901361795100444997361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1952600907863400296664907 2928901361795100444997361)
              ·
                refine ⟨2196676021346325333748021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2928901361795100444997361 2196676021346325333748021)
                ·
                  refine ⟨205938377001218000038877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2196676021346325333748021 205938377001218000038877)
                  ·
                    rfl

theorem cell22_1804786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 2, 1, 2, 5].length) (baseStart_1804786 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1804786 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1804786 prefixEnd_1804786 := by exact prefixLift 1804786
  have htrace : WordTrace (prefixWord ++ tailWord_1804786) baseStart_1804786 baseEnd_1804786 := by
    simpa [prefixWord, tailWord_1804786, baseEnd_1804786] using wordTrace_append hprefix tailTrace_1804786
  have hstable : (prefixWord ++ tailWord_1804786).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1804786).length < 2 ^ (prefixWord ++ tailWord_1804786).sum := by decide
  have hdescent : baseEnd_1804786 < baseStart_1804786 := by decide
  rcases family_descends (prefixWord ++ tailWord_1804786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1804797 : List Nat := [1, 4, 1, 1, 1, 3, 4, 1, 6]
def baseStart_1804797 : Nat := 118140960795 + 1804797 * 2 ^ 59
def prefixEnd_1804797 : Nat := 4983230072969 + 3 ^ 40 * 1804797 * 2
def baseEnd_1804797 : Nat := 205939632176151212697199

theorem tailTrace_1804797 : CollatzResearch.WordTrace tailWord_1804797 prefixEnd_1804797 205939632176151212697199 := by
  unfold tailWord_1804797
  simp only [CollatzResearch.WordTrace]
  refine ⟨65826354442536178632884645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43884236295024119088589763 65826354442536178632884645)
  ·
    refine ⟨12342441457975533493665871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65826354442536178632884645 12342441457975533493665871)
    ·
      refine ⟨18513662186963300240498807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12342441457975533493665871 18513662186963300240498807)
      ·
        refine ⟨27770493280444950360748211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18513662186963300240498807 27770493280444950360748211)
        ·
          refine ⟨41655739920667425541122317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27770493280444950360748211 41655739920667425541122317)
          ·
            refine ⟨15620902470250284577920869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41655739920667425541122317 15620902470250284577920869)
            ·
              refine ⟨2928919213171928358360163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15620902470250284577920869 2928919213171928358360163)
              ·
                refine ⟨4393378819757892537540245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2928919213171928358360163 4393378819757892537540245)
                ·
                  refine ⟨205939632176151212697199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4393378819757892537540245 205939632176151212697199)
                  ·
                    rfl

theorem cell22_1804797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 4, 1, 6].length) (baseStart_1804797 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1804797 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1804797 prefixEnd_1804797 := by exact prefixLift 1804797
  have htrace : WordTrace (prefixWord ++ tailWord_1804797) baseStart_1804797 baseEnd_1804797 := by
    simpa [prefixWord, tailWord_1804797, baseEnd_1804797] using wordTrace_append hprefix tailTrace_1804797
  have hstable : (prefixWord ++ tailWord_1804797).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1804797).length < 2 ^ (prefixWord ++ tailWord_1804797).sum := by decide
  have hdescent : baseEnd_1804797 < baseStart_1804797 := by decide
  rcases family_descends (prefixWord ++ tailWord_1804797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1804825 : List Nat := [1, 2, 1, 2, 1, 1, 2, 12]
def baseStart_1804825 : Nat := 118140960795 + 1804825 * 2 ^ 59
def prefixEnd_1804825 : Nat := 4983230072969 + 3 ^ 40 * 1804825 * 2
def baseEnd_1804825 : Nat := 68647609055630099821279

theorem tailTrace_1804825 : CollatzResearch.WordTrace tailWord_1804825 prefixEnd_1804825 68647609055630099821279 := by
  unfold tailWord_1804825
  simp only [CollatzResearch.WordTrace]
  refine ⟨65827375686434739414903929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43884917124289826276602619 65827375686434739414903929)
  ·
    refine ⟨49370531764826054561177947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65827375686434739414903929 49370531764826054561177947)
    ·
      refine ⟨74055797647239081841766921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49370531764826054561177947 74055797647239081841766921)
      ·
        refine ⟨55541848235429311381325191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74055797647239081841766921 55541848235429311381325191)
        ·
          refine ⟨83312772353143967071987787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55541848235429311381325191 83312772353143967071987787)
          ·
            refine ⟨124969158529715950607981681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83312772353143967071987787 124969158529715950607981681)
            ·
              refine ⟨93726868897286962955986261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 124969158529715950607981681 93726868897286962955986261)
              ·
                refine ⟨68647609055630099821279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 93726868897286962955986261 68647609055630099821279)
                ·
                  rfl

theorem cell22_1804825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 12].length) (baseStart_1804825 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1804825 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1804825 prefixEnd_1804825 := by exact prefixLift 1804825
  have htrace : WordTrace (prefixWord ++ tailWord_1804825) baseStart_1804825 baseEnd_1804825 := by
    simpa [prefixWord, tailWord_1804825, baseEnd_1804825] using wordTrace_append hprefix tailTrace_1804825
  have hstable : (prefixWord ++ tailWord_1804825).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1804825).length < 2 ^ (prefixWord ++ tailWord_1804825).sum := by decide
  have hdescent : baseEnd_1804825 < baseStart_1804825 := by decide
  rcases family_descends (prefixWord ++ tailWord_1804825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1804829 : List Nat := [1, 4, 2, 2, 1, 2, 1, 2, 4, 3]
def baseStart_1804829 : Nat := 118140960795 + 1804829 * 2 ^ 59
def prefixEnd_1804829 : Nat := 4983230072969 + 3 ^ 40 * 1804829 * 2
def baseEnd_1804829 : Nat := 617829850782416221291499

theorem tailTrace_1804829 : CollatzResearch.WordTrace tailWord_1804829 prefixEnd_1804829 617829850782416221291499 := by
  unfold tailWord_1804829
  simp only [CollatzResearch.WordTrace]
  refine ⟨65827521578420248098049541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43885014385613498732033027 65827521578420248098049541)
  ·
    refine ⟨12342660295953796518384289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65827521578420248098049541 12342660295953796518384289)
    ·
      refine ⟨9256995221965347388788217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12342660295953796518384289 9256995221965347388788217)
      ·
        refine ⟨6942746416474010541591163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9256995221965347388788217 6942746416474010541591163)
        ·
          refine ⟨10414119624711015812386745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6942746416474010541591163 10414119624711015812386745)
          ·
            refine ⟨7810589718533261859290059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10414119624711015812386745 7810589718533261859290059)
            ·
              refine ⟨11715884577799892788935089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7810589718533261859290059 11715884577799892788935089)
              ·
                refine ⟨8786913433349919591701317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11715884577799892788935089 8786913433349919591701317)
                ·
                  refine ⟨1647546268753109923443997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8786913433349919591701317 1647546268753109923443997)
                  ·
                    refine ⟨617829850782416221291499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1647546268753109923443997 617829850782416221291499)
                    ·
                      rfl

theorem cell22_1804829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 2, 4, 3].length) (baseStart_1804829 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1804829 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1804829 prefixEnd_1804829 := by exact prefixLift 1804829
  have htrace : WordTrace (prefixWord ++ tailWord_1804829) baseStart_1804829 baseEnd_1804829 := by
    simpa [prefixWord, tailWord_1804829, baseEnd_1804829] using wordTrace_append hprefix tailTrace_1804829
  have hstable : (prefixWord ++ tailWord_1804829).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1804829).length < 2 ^ (prefixWord ++ tailWord_1804829).sum := by decide
  have hdescent : baseEnd_1804829 < baseStart_1804829 := by decide
  rcases family_descends (prefixWord ++ tailWord_1804829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1804842 : List Nat := [3, 1, 4, 1, 1, 2, 10]
def baseStart_1804842 : Nat := 118140960795 + 1804842 * 2 ^ 59
def prefixEnd_1804842 : Nat := 4983230072969 + 3 ^ 40 * 1804842 * 2
def baseEnd_1804842 : Nat := 22882751886966241508017

theorem tailTrace_1804842 : CollatzResearch.WordTrace tailWord_1804842 prefixEnd_1804842 22882751886966241508017 := by
  unfold tailWord_1804842
  simp only [CollatzResearch.WordTrace]
  refine ⟨16456998931843287829568195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43885330484915434212181853 16456998931843287829568195)
  ·
    refine ⟨24685498397764931744352293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16456998931843287829568195 24685498397764931744352293)
    ·
      refine ⟨4628530949580924702066055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24685498397764931744352293 4628530949580924702066055)
      ·
        refine ⟨6942796424371387053099083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4628530949580924702066055 6942796424371387053099083)
        ·
          refine ⟨10414194636557080579648625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6942796424371387053099083 10414194636557080579648625)
          ·
            refine ⟨7810645977417810434736469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10414194636557080579648625 7810645977417810434736469)
            ·
              refine ⟨22882751886966241508017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 7810645977417810434736469 22882751886966241508017)
              ·
                rfl

theorem cell22_1804842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 10].length) (baseStart_1804842 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1804842 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1804842 prefixEnd_1804842 := by exact prefixLift 1804842
  have htrace : WordTrace (prefixWord ++ tailWord_1804842) baseStart_1804842 baseEnd_1804842 := by
    simpa [prefixWord, tailWord_1804842, baseEnd_1804842] using wordTrace_append hprefix tailTrace_1804842
  have hstable : (prefixWord ++ tailWord_1804842).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1804842).length < 2 ^ (prefixWord ++ tailWord_1804842).sum := by decide
  have hdescent : baseEnd_1804842 < baseStart_1804842 := by decide
  rcases family_descends (prefixWord ++ tailWord_1804842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1804908 : List Nat := [2, 2, 1, 1, 3, 1, 6, 2, 1, 3]
def baseStart_1804908 : Nat := 118140960795 + 1804908 * 2 ^ 59
def prefixEnd_1804908 : Nat := 4983230072969 + 3 ^ 40 * 1804908 * 2
def baseEnd_1804908 : Nat := 617856894096886348566257

theorem tailTrace_1804908 : CollatzResearch.WordTrace tailWord_1804908 prefixEnd_1804908 617856894096886348566257 := by
  unfold tailWord_1804908
  simp only [CollatzResearch.WordTrace]
  refine ⟨32915201472567022295087689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43886935296756029726783585 32915201472567022295087689)
  ·
    refine ⟨24686401104425266721315767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32915201472567022295087689 24686401104425266721315767)
    ·
      refine ⟨37029601656637900081973651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24686401104425266721315767 37029601656637900081973651)
      ·
        refine ⟨55544402484956850122960477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37029601656637900081973651 55544402484956850122960477)
        ·
          refine ⟨20829150931858818796110179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55544402484956850122960477 20829150931858818796110179)
          ·
            refine ⟨31243726397788228194165269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20829150931858818796110179 31243726397788228194165269)
            ·
              refine ⟨1464549674896323196601497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 31243726397788228194165269 1464549674896323196601497)
              ·
                refine ⟨1098412256172242397451123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1464549674896323196601497 1098412256172242397451123)
                ·
                  refine ⟨1647618384258363596176685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1098412256172242397451123 1647618384258363596176685)
                  ·
                    refine ⟨617856894096886348566257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1647618384258363596176685 617856894096886348566257)
                    ·
                      rfl

theorem cell22_1804908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 6, 2, 1, 3].length) (baseStart_1804908 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1804908 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1804908 prefixEnd_1804908 := by exact prefixLift 1804908
  have htrace : WordTrace (prefixWord ++ tailWord_1804908) baseStart_1804908 baseEnd_1804908 := by
    simpa [prefixWord, tailWord_1804908, baseEnd_1804908] using wordTrace_append hprefix tailTrace_1804908
  have hstable : (prefixWord ++ tailWord_1804908).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1804908).length < 2 ^ (prefixWord ++ tailWord_1804908).sum := by decide
  have hdescent : baseEnd_1804908 < baseStart_1804908 := by decide
  rcases family_descends (prefixWord ++ tailWord_1804908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1804981 : List Nat := [1, 3, 3, 3, 1, 1, 3, 1, 1, 5]
def baseStart_1804981 : Nat := 118140960795 + 1804981 * 2 ^ 59
def prefixEnd_1804981 : Nat := 4983230072969 + 3 ^ 40 * 1804981 * 2
def baseEnd_1804981 : Nat := 617881883488738491491033

theorem tailTrace_1804981 : CollatzResearch.WordTrace tailWord_1804981 prefixEnd_1804981 617881883488738491491033 := by
  unfold tailWord_1804981
  simp only [CollatzResearch.WordTrace]
  refine ⟨65833065473869578057582797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43888710315913052038388531 65833065473869578057582797)
  ·
    refine ⟨24687399552701091771593549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65833065473869578057582797 24687399552701091771593549)
    ·
      refine ⟨9257774832262909414347581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24687399552701091771593549 9257774832262909414347581)
      ·
        refine ⟨3471665562098591030380343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9257774832262909414347581 3471665562098591030380343)
        ·
          refine ⟨5207498343147886545570515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3471665562098591030380343 5207498343147886545570515)
          ·
            refine ⟨7811247514721829818355773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5207498343147886545570515 7811247514721829818355773)
            ·
              refine ⟨2929217818020686181883415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7811247514721829818355773 2929217818020686181883415)
              ·
                refine ⟨4393826727031029272825123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2929217818020686181883415 4393826727031029272825123)
                ·
                  refine ⟨6590740090546543909237685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4393826727031029272825123 6590740090546543909237685)
                  ·
                    refine ⟨617881883488738491491033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6590740090546543909237685 617881883488738491491033)
                    ·
                      rfl

theorem cell22_1804981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 3, 1, 1, 5].length) (baseStart_1804981 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1804981 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1804981 prefixEnd_1804981 := by exact prefixLift 1804981
  have htrace : WordTrace (prefixWord ++ tailWord_1804981) baseStart_1804981 baseEnd_1804981 := by
    simpa [prefixWord, tailWord_1804981, baseEnd_1804981] using wordTrace_append hprefix tailTrace_1804981
  have hstable : (prefixWord ++ tailWord_1804981).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1804981).length < 2 ^ (prefixWord ++ tailWord_1804981).sum := by decide
  have hdescent : baseEnd_1804981 < baseStart_1804981 := by decide
  rcases family_descends (prefixWord ++ tailWord_1804981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1805007 : List Nat := [1, 1, 2, 1, 1, 3, 1, 1, 3, 8]
def baseStart_1805007 : Nat := 118140960795 + 1805007 * 2 ^ 59
def prefixEnd_1805007 : Nat := 4983230072969 + 3 ^ 40 * 1805007 * 2
def baseEnd_1805007 : Nat := 617890783820083090340953

theorem tailTrace_1805007 : CollatzResearch.WordTrace tailWord_1805007 prefixEnd_1805007 617890783820083090340953 := by
  unfold tailWord_1805007
  simp only [CollatzResearch.WordTrace]
  refine ⟨65834013771775384498029275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43889342514516922998686183 65834013771775384498029275)
  ·
    refine ⟨98751020657663076747043913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65834013771775384498029275 98751020657663076747043913)
    ·
      refine ⟨74063265493247307560282935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98751020657663076747043913 74063265493247307560282935)
      ·
        refine ⟨111094898239870961340424403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74063265493247307560282935 111094898239870961340424403)
        ·
          refine ⟨166642347359806442010636605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111094898239870961340424403 166642347359806442010636605)
          ·
            refine ⟨62490880259927415753988727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 166642347359806442010636605 62490880259927415753988727)
            ·
              refine ⟨93736320389891123630983091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62490880259927415753988727 93736320389891123630983091)
              ·
                refine ⟨140604480584836685446474637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93736320389891123630983091 140604480584836685446474637)
                ·
                  refine ⟨52726680219313757042427989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 140604480584836685446474637 52726680219313757042427989)
                  ·
                    refine ⟨617890783820083090340953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 52726680219313757042427989 617890783820083090340953)
                    ·
                      rfl

theorem cell22_1805007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 1, 3, 8].length) (baseStart_1805007 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1805007 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1805007 prefixEnd_1805007 := by exact prefixLift 1805007
  have htrace : WordTrace (prefixWord ++ tailWord_1805007) baseStart_1805007 baseEnd_1805007 := by
    simpa [prefixWord, tailWord_1805007, baseEnd_1805007] using wordTrace_append hprefix tailTrace_1805007
  have hstable : (prefixWord ++ tailWord_1805007).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1805007).length < 2 ^ (prefixWord ++ tailWord_1805007).sum := by decide
  have hdescent : baseEnd_1805007 < baseStart_1805007 := by decide
  rcases family_descends (prefixWord ++ tailWord_1805007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1805013 : List Nat := [1, 3, 2, 5, 1, 1, 1, 2, 2, 4]
def baseStart_1805013 : Nat := 118140960795 + 1805013 * 2 ^ 59
def prefixEnd_1805013 : Nat := 4983230072969 + 3 ^ 40 * 1805013 * 2
def baseEnd_1805013 : Nat := 617892837742701074690935

theorem tailTrace_1805013 : CollatzResearch.WordTrace tailWord_1805013 prefixEnd_1805013 617892837742701074690935 := by
  unfold tailWord_1805013
  simp only [CollatzResearch.WordTrace]
  refine ⟨65834232609753647522747693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43889488406502431681831795 65834232609753647522747693)
  ·
    refine ⟨24687837228657617821030385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65834232609753647522747693 24687837228657617821030385)
    ·
      refine ⟨18515877921493213365772789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24687837228657617821030385 18515877921493213365772789)
      ·
        refine ⟨1735863555139988753041199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 18515877921493213365772789 1735863555139988753041199)
        ·
          refine ⟨2603795332709983129561799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1735863555139988753041199 2603795332709983129561799)
          ·
            refine ⟨3905692999064974694342699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2603795332709983129561799 3905692999064974694342699)
            ·
              refine ⟨5858539498597462041514049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3905692999064974694342699 5858539498597462041514049)
              ·
                refine ⟨4393904623948096531135537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5858539498597462041514049 4393904623948096531135537)
                ·
                  refine ⟨3295428467961072398351653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4393904623948096531135537 3295428467961072398351653)
                  ·
                    refine ⟨617892837742701074690935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3295428467961072398351653 617892837742701074690935)
                    ·
                      rfl

theorem cell22_1805013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 1, 2, 2, 4].length) (baseStart_1805013 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1805013 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1805013 prefixEnd_1805013 := by exact prefixLift 1805013
  have htrace : WordTrace (prefixWord ++ tailWord_1805013) baseStart_1805013 baseEnd_1805013 := by
    simpa [prefixWord, tailWord_1805013, baseEnd_1805013] using wordTrace_append hprefix tailTrace_1805013
  have hstable : (prefixWord ++ tailWord_1805013).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1805013).length < 2 ^ (prefixWord ++ tailWord_1805013).sum := by decide
  have hdescent : baseEnd_1805013 < baseStart_1805013 := by decide
  rcases family_descends (prefixWord ++ tailWord_1805013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1805032 : List Nat := [2, 1, 4, 1, 5, 1, 2, 1, 2, 3]
def baseStart_1805032 : Nat := 118140960795 + 1805032 * 2 ^ 59
def prefixEnd_1805032 : Nat := 4983230072969 + 3 ^ 40 * 1805032 * 2
def baseEnd_1805032 : Nat := 617899341830991358465877

theorem tailTrace_1805032 : CollatzResearch.WordTrace tailWord_1805032 prefixEnd_1805032 617899341830991358465877 := by
  unfold tailWord_1805032
  simp only [CollatzResearch.WordTrace]
  refine ⟨32917462798342406883844675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43889950397789875845126233 32917462798342406883844675)
  ·
    refine ⟨49376194197513610325767013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32917462798342406883844675 49376194197513610325767013)
    ·
      refine ⟨9258036412033801936081315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49376194197513610325767013 9258036412033801936081315)
      ·
        refine ⟨13887054618050702904121973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9258036412033801936081315 13887054618050702904121973)
        ·
          refine ⟨1301911370442253397261435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13887054618050702904121973 1301911370442253397261435)
          ·
            refine ⟨1952867055663380095892153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1301911370442253397261435 1952867055663380095892153)
            ·
              refine ⟨1464650291747535071919115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1952867055663380095892153 1464650291747535071919115)
              ·
                refine ⟨2196975437621302607878673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1464650291747535071919115 2196975437621302607878673)
                ·
                  refine ⟨1647731578215976955909005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2196975437621302607878673 1647731578215976955909005)
                  ·
                    refine ⟨617899341830991358465877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1647731578215976955909005 617899341830991358465877)
                    ·
                      rfl

theorem cell22_1805032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 1, 2, 1, 2, 3].length) (baseStart_1805032 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1805032 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1805032 prefixEnd_1805032 := by exact prefixLift 1805032
  have htrace : WordTrace (prefixWord ++ tailWord_1805032) baseStart_1805032 baseEnd_1805032 := by
    simpa [prefixWord, tailWord_1805032, baseEnd_1805032] using wordTrace_append hprefix tailTrace_1805032
  have hstable : (prefixWord ++ tailWord_1805032).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1805032).length < 2 ^ (prefixWord ++ tailWord_1805032).sum := by decide
  have hdescent : baseEnd_1805032 < baseStart_1805032 := by decide
  rcases family_descends (prefixWord ++ tailWord_1805032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1805099 : List Nat := [1, 1, 1, 1, 2, 1, 2, 7, 1, 5]
def baseStart_1805099 : Nat := 118140960795 + 1805099 * 2 ^ 59
def prefixEnd_1805099 : Nat := 4983230072969 + 3 ^ 40 * 1805099 * 2
def baseEnd_1805099 : Nat := 617922277300225517040671

theorem tailTrace_1805099 : CollatzResearch.WordTrace tailWord_1805099 prefixEnd_1805099 617922277300225517040671 := by
  unfold tailWord_1805099
  simp only [CollatzResearch.WordTrace]
  refine ⟨65837369287442084210378351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43891579524961389473585567 65837369287442084210378351)
  ·
    refine ⟨98756053931163126315567527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65837369287442084210378351 98756053931163126315567527)
    ·
      refine ⟨148134080896744689473351291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98756053931163126315567527 148134080896744689473351291)
      ·
        refine ⟨222201121345117034210026937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148134080896744689473351291 222201121345117034210026937)
        ·
          refine ⟨166650841008837775657520203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 222201121345117034210026937 166650841008837775657520203)
          ·
            refine ⟨249976261513256663486280305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166650841008837775657520203 249976261513256663486280305)
            ·
              refine ⟨187482196134942497614710229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 249976261513256663486280305 187482196134942497614710229)
              ·
                refine ⟨4394113971912714787844771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 187482196134942497614710229 4394113971912714787844771)
                ·
                  refine ⟨6591170957869072181767157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4394113971912714787844771 6591170957869072181767157)
                  ·
                    refine ⟨617922277300225517040671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6591170957869072181767157 617922277300225517040671)
                    ·
                      rfl

theorem cell22_1805099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 7, 1, 5].length) (baseStart_1805099 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1805099 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1805099 prefixEnd_1805099 := by exact prefixLift 1805099
  have htrace : WordTrace (prefixWord ++ tailWord_1805099) baseStart_1805099 baseEnd_1805099 := by
    simpa [prefixWord, tailWord_1805099, baseEnd_1805099] using wordTrace_append hprefix tailTrace_1805099
  have hstable : (prefixWord ++ tailWord_1805099).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1805099).length < 2 ^ (prefixWord ++ tailWord_1805099).sum := by decide
  have hdescent : baseEnd_1805099 < baseStart_1805099 := by decide
  rcases family_descends (prefixWord ++ tailWord_1805099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1805116 : List Nat := [2, 2, 2, 2, 1, 1, 1, 4, 4, 3]
def baseStart_1805116 : Nat := 118140960795 + 1805116 * 2 ^ 59
def prefixEnd_1805116 : Nat := 4983230072969 + 3 ^ 40 * 1805116 * 2
def baseEnd_1805116 : Nat := 617928096747643139365619

theorem tailTrace_1805116 : CollatzResearch.WordTrace tailWord_1805116 prefixEnd_1805116 617928096747643139365619 := by
  unfold tailWord_1805116
  simp only [CollatzResearch.WordTrace]
  refine ⟨32918994664190248056873601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43891992885586997409164801 32918994664190248056873601)
  ·
    refine ⟨24689245998142686042655201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32918994664190248056873601 24689245998142686042655201)
    ·
      refine ⟨18516934498607014531991401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24689245998142686042655201 18516934498607014531991401)
      ·
        refine ⟨13887700873955260898993551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18516934498607014531991401 13887700873955260898993551)
        ·
          refine ⟨20831551310932891348490327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13887700873955260898993551 20831551310932891348490327)
          ·
            refine ⟨31247326966399337022735491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20831551310932891348490327 31247326966399337022735491)
            ·
              refine ⟨46870990449599005534103237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31247326966399337022735491 46870990449599005534103237)
              ·
                refine ⟨8788310709299813537644357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46870990449599005534103237 8788310709299813537644357)
                ·
                  refine ⟨1647808257993715038308317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8788310709299813537644357 1647808257993715038308317)
                  ·
                    refine ⟨617928096747643139365619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1647808257993715038308317 617928096747643139365619)
                    ·
                      rfl

theorem cell22_1805116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 4, 4, 3].length) (baseStart_1805116 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1805116 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1805116 prefixEnd_1805116 := by exact prefixLift 1805116
  have htrace : WordTrace (prefixWord ++ tailWord_1805116) baseStart_1805116 baseEnd_1805116 := by
    simpa [prefixWord, tailWord_1805116, baseEnd_1805116] using wordTrace_append hprefix tailTrace_1805116
  have hstable : (prefixWord ++ tailWord_1805116).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1805116).length < 2 ^ (prefixWord ++ tailWord_1805116).sum := by decide
  have hdescent : baseEnd_1805116 < baseStart_1805116 := by decide
  rcases family_descends (prefixWord ++ tailWord_1805116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1805129 : List Nat := [1, 2, 1, 1, 2, 6, 9]
def baseStart_1805129 : Nat := 118140960795 + 1805129 * 2 ^ 59
def prefixEnd_1805129 : Nat := 4983230072969 + 3 ^ 40 * 1805129 * 2
def baseEnd_1805129 : Nat := 22886390626419090325577

theorem tailTrace_1805129 : CollatzResearch.WordTrace tailWord_1805129 prefixEnd_1805129 22886390626419090325577 := by
  unfold tailWord_1805129
  simp only [CollatzResearch.WordTrace]
  refine ⟨65838463477333399333970441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43892308984888932889313627 65838463477333399333970441)
  ·
    refine ⟨49378847608000049500477831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65838463477333399333970441 49378847608000049500477831)
    ·
      refine ⟨74068271412000074250716747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49378847608000049500477831 74068271412000074250716747)
      ·
        refine ⟨111102407118000111376075121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74068271412000074250716747 111102407118000111376075121)
        ·
          refine ⟨83326805338500083532056341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111102407118000111376075121 83326805338500083532056341)
          ·
            refine ⟨3905944000242191415565141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 83326805338500083532056341 3905944000242191415565141)
            ·
              refine ⟨22886390626419090325577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3905944000242191415565141 22886390626419090325577)
              ·
                rfl

theorem cell22_1805129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 9].length) (baseStart_1805129 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1805129 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1805129 prefixEnd_1805129 := by exact prefixLift 1805129
  have htrace : WordTrace (prefixWord ++ tailWord_1805129) baseStart_1805129 baseEnd_1805129 := by
    simpa [prefixWord, tailWord_1805129, baseEnd_1805129] using wordTrace_append hprefix tailTrace_1805129
  have hstable : (prefixWord ++ tailWord_1805129).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1805129).length < 2 ^ (prefixWord ++ tailWord_1805129).sum := by decide
  have hdescent : baseEnd_1805129 < baseStart_1805129 := by decide
  rcases family_descends (prefixWord ++ tailWord_1805129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1805191 : List Nat := [1, 1, 4, 2, 3, 1, 2, 1, 7]
def baseStart_1805191 : Nat := 118140960795 + 1805191 * 2 ^ 59
def prefixEnd_1805191 : Nat := 4983230072969 + 3 ^ 40 * 1805191 * 2
def baseEnd_1805191 : Nat := 205984590260122647913463

theorem tailTrace_1805191 : CollatzResearch.WordTrace tailWord_1805191 prefixEnd_1805191 205984590260122647913463 := by
  unfold tailWord_1805191
  simp only [CollatzResearch.WordTrace]
  refine ⟨65840724803108783922727427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43893816535405855948484951 65840724803108783922727427)
  ·
    refine ⟨98761087204663175884091141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65840724803108783922727427 98761087204663175884091141)
    ·
      refine ⟨18517703850874345478267089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 98761087204663175884091141 18517703850874345478267089)
      ·
        refine ⟨13888277888155759108700317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18517703850874345478267089 13888277888155759108700317)
        ·
          refine ⟨5208104208058409665762619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13888277888155759108700317 5208104208058409665762619)
          ·
            refine ⟨7812156312087614498643929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5208104208058409665762619 7812156312087614498643929)
            ·
              refine ⟨5859117234065710873982947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7812156312087614498643929 5859117234065710873982947)
              ·
                refine ⟨8788675851098566310974421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5859117234065710873982947 8788675851098566310974421)
                ·
                  refine ⟨205984590260122647913463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8788675851098566310974421 205984590260122647913463)
                  ·
                    rfl

theorem cell22_1805191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 2, 1, 7].length) (baseStart_1805191 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1805191 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1805191 prefixEnd_1805191 := by exact prefixLift 1805191
  have htrace : WordTrace (prefixWord ++ tailWord_1805191) baseStart_1805191 baseEnd_1805191 := by
    simpa [prefixWord, tailWord_1805191, baseEnd_1805191] using wordTrace_append hprefix tailTrace_1805191
  have hstable : (prefixWord ++ tailWord_1805191).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1805191).length < 2 ^ (prefixWord ++ tailWord_1805191).sum := by decide
  have hdescent : baseEnd_1805191 < baseStart_1805191 := by decide
  rcases family_descends (prefixWord ++ tailWord_1805191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1805268 : List Nat := [2, 4, 1, 2, 1, 2, 1, 3, 1, 5]
def baseStart_1805268 : Nat := 118140960795 + 1805268 * 2 ^ 59
def prefixEnd_1805268 : Nat := 4983230072969 + 3 ^ 40 * 1805268 * 2
def baseEnd_1805268 : Nat := 617980129453965409565153

theorem tailTrace_1805268 : CollatzResearch.WordTrace tailWord_1805268 prefixEnd_1805268 617980129453965409565153 := by
  unfold tailWord_1805268
  simp only [CollatzResearch.WordTrace]
  refine ⟨32921766611914913036640229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43895688815886550715520305 32921766611914913036640229)
  ·
    refine ⟨6172831239734046194370043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32921766611914913036640229 6172831239734046194370043)
    ·
      refine ⟨9259246859601069291555065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6172831239734046194370043 9259246859601069291555065)
      ·
        refine ⟨6944435144700801968666299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9259246859601069291555065 6944435144700801968666299)
        ·
          refine ⟨10416652717051202952999449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6944435144700801968666299 10416652717051202952999449)
          ·
            refine ⟨7812489537788402214749587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10416652717051202952999449 7812489537788402214749587)
            ·
              refine ⟨11718734306682603322124381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7812489537788402214749587 11718734306682603322124381)
              ·
                refine ⟨4394525365005976245796643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11718734306682603322124381 4394525365005976245796643)
                ·
                  refine ⟨6591788047508964368694965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4394525365005976245796643 6591788047508964368694965)
                  ·
                    refine ⟨617980129453965409565153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6591788047508964368694965 617980129453965409565153)
                    ·
                      rfl

theorem cell22_1805268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 3, 1, 5].length) (baseStart_1805268 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1805268 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1805268 prefixEnd_1805268 := by exact prefixLift 1805268
  have htrace : WordTrace (prefixWord ++ tailWord_1805268) baseStart_1805268 baseEnd_1805268 := by
    simpa [prefixWord, tailWord_1805268, baseEnd_1805268] using wordTrace_append hprefix tailTrace_1805268
  have hstable : (prefixWord ++ tailWord_1805268).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1805268).length < 2 ^ (prefixWord ++ tailWord_1805268).sum := by decide
  have hdescent : baseEnd_1805268 < baseStart_1805268 := by decide
  rcases family_descends (prefixWord ++ tailWord_1805268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1805270 : List Nat := [5, 2, 1, 1, 2, 2, 1, 2, 6]
def baseStart_1805270 : Nat := 118140960795 + 1805270 * 2 ^ 59
def prefixEnd_1805270 : Nat := 4983230072969 + 3 ^ 40 * 1805270 * 2
def baseEnd_1805270 : Nat := 205993604698279357005049

theorem tailTrace_1805270 : CollatzResearch.WordTrace tailWord_1805270 prefixEnd_1805270 205993604698279357005049 := by
  unfold tailWord_1805270
  simp only [CollatzResearch.WordTrace]
  refine ⟨4115225385613911275928329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 43895737446548386943235509 4115225385613911275928329)
  ·
    refine ⟨3086419039210433456946247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4115225385613911275928329 3086419039210433456946247)
    ·
      refine ⟨4629628558815650185419371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3086419039210433456946247 4629628558815650185419371)
      ·
        refine ⟨6944442838223475278129057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4629628558815650185419371 6944442838223475278129057)
        ·
          refine ⟨5208332128667606458596793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6944442838223475278129057 5208332128667606458596793)
          ·
            refine ⟨3906249096500704843947595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5208332128667606458596793 3906249096500704843947595)
            ·
              refine ⟨5859373644751057265921393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3906249096500704843947595 5859373644751057265921393)
              ·
                refine ⟨4394530233563292949441045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5859373644751057265921393 4394530233563292949441045)
                ·
                  refine ⟨205993604698279357005049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4394530233563292949441045 205993604698279357005049)
                  ·
                    rfl

theorem cell22_1805270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 1, 2, 6].length) (baseStart_1805270 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1805270 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1805270 prefixEnd_1805270 := by exact prefixLift 1805270
  have htrace : WordTrace (prefixWord ++ tailWord_1805270) baseStart_1805270 baseEnd_1805270 := by
    simpa [prefixWord, tailWord_1805270, baseEnd_1805270] using wordTrace_append hprefix tailTrace_1805270
  have hstable : (prefixWord ++ tailWord_1805270).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1805270).length < 2 ^ (prefixWord ++ tailWord_1805270).sum := by decide
  have hdescent : baseEnd_1805270 < baseStart_1805270 := by decide
  rcases family_descends (prefixWord ++ tailWord_1805270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1805302 : List Nat := [5, 1, 1, 1, 3, 1, 3, 2, 2, 3]
def baseStart_1805302 : Nat := 118140960795 + 1805302 * 2 ^ 59
def prefixEnd_1805302 : Nat := 4983230072969 + 3 ^ 40 * 1805302 * 2
def baseEnd_1805302 : Nat := 617991768348800654215049

theorem tailTrace_1805302 : CollatzResearch.WordTrace tailWord_1805302 prefixEnd_1805302 617991768348800654215049 := by
  unfold tailWord_1805302
  simp only [CollatzResearch.WordTrace]
  refine ⟨4115298331606665617501135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 43896515537137766586678773 4115298331606665617501135)
  ·
    refine ⟨6172947497409998426251703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4115298331606665617501135 6172947497409998426251703)
    ·
      refine ⟨9259421246114997639377555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6172947497409998426251703 9259421246114997639377555)
      ·
        refine ⟨13889131869172496459066333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9259421246114997639377555 13889131869172496459066333)
        ·
          refine ⟨5208424450939686172149875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13889131869172496459066333 5208424450939686172149875)
          ·
            refine ⟨7812636676409529258224813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5208424450939686172149875 7812636676409529258224813)
            ·
              refine ⟨2929738753653573471834305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7812636676409529258224813 2929738753653573471834305)
              ·
                refine ⟨2197304065240180103875729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2929738753653573471834305 2197304065240180103875729)
                ·
                  refine ⟨1647978048930135077906797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2197304065240180103875729 1647978048930135077906797)
                  ·
                    refine ⟨617991768348800654215049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1647978048930135077906797 617991768348800654215049)
                    ·
                      rfl

theorem cell22_1805302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 3, 2, 2, 3].length) (baseStart_1805302 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1805302 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1805302 prefixEnd_1805302 := by exact prefixLift 1805302
  have htrace : WordTrace (prefixWord ++ tailWord_1805302) baseStart_1805302 baseEnd_1805302 := by
    simpa [prefixWord, tailWord_1805302, baseEnd_1805302] using wordTrace_append hprefix tailTrace_1805302
  have hstable : (prefixWord ++ tailWord_1805302).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1805302).length < 2 ^ (prefixWord ++ tailWord_1805302).sum := by decide
  have hdescent : baseEnd_1805302 < baseStart_1805302 := by decide
  rcases family_descends (prefixWord ++ tailWord_1805302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1805347 : List Nat := [1, 1, 1, 4, 3, 2, 3, 3, 1, 3]
def baseStart_1805347 : Nat := 118140960795 + 1805347 * 2 ^ 59
def prefixEnd_1805347 : Nat := 4983230072969 + 3 ^ 40 * 1805347 * 2
def baseEnd_1805347 : Nat := 618007172768435536839911

theorem tailTrace_1805347 : CollatzResearch.WordTrace tailWord_1805347 prefixEnd_1805347 618007172768435536839911 := by
  unfold tailWord_1805347
  simp only [CollatzResearch.WordTrace]
  refine ⟨65846414590543622565406295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43897609727029081710270863 65846414590543622565406295)
  ·
    refine ⟨98769621885815433848109443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65846414590543622565406295 98769621885815433848109443)
    ·
      refine ⟨148154432828723150772164165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98769621885815433848109443 148154432828723150772164165)
      ·
        refine ⟨27778956155385590769780781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 148154432828723150772164165 27778956155385590769780781)
        ·
          refine ⟨10417108558269596538667793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27778956155385590769780781 10417108558269596538667793)
          ·
            refine ⟨7812831418702197404000845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10417108558269596538667793 7812831418702197404000845)
            ·
              refine ⟨2929811782013324026500317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7812831418702197404000845 2929811782013324026500317)
              ·
                refine ⟨1098679418254996509937619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2929811782013324026500317 1098679418254996509937619)
                ·
                  refine ⟨1648019127382494764906429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1098679418254996509937619 1648019127382494764906429)
                  ·
                    refine ⟨618007172768435536839911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1648019127382494764906429 618007172768435536839911)
                    ·
                      rfl

theorem cell22_1805347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 3, 3, 1, 3].length) (baseStart_1805347 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1805347 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1805347 prefixEnd_1805347 := by exact prefixLift 1805347
  have htrace : WordTrace (prefixWord ++ tailWord_1805347) baseStart_1805347 baseEnd_1805347 := by
    simpa [prefixWord, tailWord_1805347, baseEnd_1805347] using wordTrace_append hprefix tailTrace_1805347
  have hstable : (prefixWord ++ tailWord_1805347).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1805347).length < 2 ^ (prefixWord ++ tailWord_1805347).sum := by decide
  have hdescent : baseEnd_1805347 < baseStart_1805347 := by decide
  rcases family_descends (prefixWord ++ tailWord_1805347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1805364 : List Nat := [2, 5, 1, 2, 1, 3, 1, 1, 3, 3]
def baseStart_1805364 : Nat := 118140960795 + 1805364 * 2 ^ 59
def prefixEnd_1805364 : Nat := 4983230072969 + 3 ^ 40 * 1805364 * 2
def baseEnd_1805364 : Nat := 618012992215853159164859

theorem tailTrace_1805364 : CollatzResearch.WordTrace tailWord_1805364 prefixEnd_1805364 618012992215853159164859 := by
  unfold tailWord_1805364
  simp only [CollatzResearch.WordTrace]
  refine ⟨32923517315741017234387573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43898023087654689645850097 32923517315741017234387573)
  ·
    refine ⟨3086579748350720365723835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 32923517315741017234387573 3086579748350720365723835)
    ·
      refine ⟨4629869622526080548585753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3086579748350720365723835 4629869622526080548585753)
      ·
        refine ⟨3472402216894560411439315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4629869622526080548585753 3472402216894560411439315)
        ·
          refine ⟨5208603325341840617158973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3472402216894560411439315 5208603325341840617158973)
          ·
            refine ⟨1953226247003190231434615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5208603325341840617158973 1953226247003190231434615)
            ·
              refine ⟨2929839370504785347151923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1953226247003190231434615 2929839370504785347151923)
              ·
                refine ⟨4394759055757178020727885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2929839370504785347151923 4394759055757178020727885)
                ·
                  refine ⟨1648034645908941757772957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4394759055757178020727885 1648034645908941757772957)
                  ·
                    refine ⟨618012992215853159164859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1648034645908941757772957 618012992215853159164859)
                    ·
                      rfl

theorem cell22_1805364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 3, 1, 1, 3, 3].length) (baseStart_1805364 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1805364 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1805364 prefixEnd_1805364 := by exact prefixLift 1805364
  have htrace : WordTrace (prefixWord ++ tailWord_1805364) baseStart_1805364 baseEnd_1805364 := by
    simpa [prefixWord, tailWord_1805364, baseEnd_1805364] using wordTrace_append hprefix tailTrace_1805364
  have hstable : (prefixWord ++ tailWord_1805364).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1805364).length < 2 ^ (prefixWord ++ tailWord_1805364).sum := by decide
  have hdescent : baseEnd_1805364 < baseStart_1805364 := by decide
  rcases family_descends (prefixWord ++ tailWord_1805364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1805422 : List Nat := [4, 1, 2, 2, 1, 3, 1, 4, 4]
def baseStart_1805422 : Nat := 118140960795 + 1805422 * 2 ^ 59
def prefixEnd_1805422 : Nat := 4983230072969 + 3 ^ 40 * 1805422 * 2
def baseEnd_1805422 : Nat := 206010948933720113738227

theorem tailTrace_1805422 : CollatzResearch.WordTrace tailWord_1805422 prefixEnd_1805422 206010948933720113738227 := by
  unfold tailWord_1805422
  simp only [CollatzResearch.WordTrace]
  refine ⟨8231143758158988796798315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43899433376847940249591013 8231143758158988796798315)
  ·
    refine ⟨12346715637238483195197473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8231143758158988796798315 12346715637238483195197473)
    ·
      refine ⟨9260036727928862396398105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12346715637238483195197473 9260036727928862396398105)
      ·
        refine ⟨6945027545946646797298579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9260036727928862396398105 6945027545946646797298579)
        ·
          refine ⟨10417541318919970195947869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6945027545946646797298579 10417541318919970195947869)
          ·
            refine ⟨3906577994594988823480451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10417541318919970195947869 3906577994594988823480451)
            ·
              refine ⟨5859866991892483235220677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3906577994594988823480451 5859866991892483235220677)
              ·
                refine ⟨1098725060979840606603877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5859866991892483235220677 1098725060979840606603877)
                ·
                  refine ⟨206010948933720113738227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1098725060979840606603877 206010948933720113738227)
                  ·
                    rfl

theorem cell22_1805422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 1, 4, 4].length) (baseStart_1805422 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1805422 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1805422 prefixEnd_1805422 := by exact prefixLift 1805422
  have htrace : WordTrace (prefixWord ++ tailWord_1805422) baseStart_1805422 baseEnd_1805422 := by
    simpa [prefixWord, tailWord_1805422, baseEnd_1805422] using wordTrace_append hprefix tailTrace_1805422
  have hstable : (prefixWord ++ tailWord_1805422).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1805422).length < 2 ^ (prefixWord ++ tailWord_1805422).sum := by decide
  have hdescent : baseEnd_1805422 < baseStart_1805422 := by decide
  rcases family_descends (prefixWord ++ tailWord_1805422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1805450 : List Nat := [3, 1, 2, 3, 1, 1, 5, 6]
def baseStart_1805450 : Nat := 118140960795 + 1805450 * 2 ^ 59
def prefixEnd_1805450 : Nat := 4983230072969 + 3 ^ 40 * 1805450 * 2
def baseEnd_1805450 : Nat := 68671381308153066834955

theorem tailTrace_1805450 : CollatzResearch.WordTrace tailWord_1805450 prefixEnd_1805450 68671381308153066834955 := by
  unfold tailWord_1805450
  simp only [CollatzResearch.WordTrace]
  refine ⟨16462542827292617789101451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43900114206113647437603869 16462542827292617789101451)
  ·
    refine ⟨24693814240938926683652177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16462542827292617789101451 24693814240938926683652177)
    ·
      refine ⟨18520360680704195012739133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24693814240938926683652177 18520360680704195012739133)
      ·
        refine ⟨6945135255264073129777175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18520360680704195012739133 6945135255264073129777175)
        ·
          refine ⟨10417702882896109694665763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6945135255264073129777175 10417702882896109694665763)
          ·
            refine ⟨15626554324344164541998645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10417702882896109694665763 15626554324344164541998645)
            ·
              refine ⟨1464989467907265425812373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15626554324344164541998645 1464989467907265425812373)
              ·
                refine ⟨68671381308153066834955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1464989467907265425812373 68671381308153066834955)
                ·
                  rfl

theorem cell22_1805450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 5, 6].length) (baseStart_1805450 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1805450 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1805450 prefixEnd_1805450 := by exact prefixLift 1805450
  have htrace : WordTrace (prefixWord ++ tailWord_1805450) baseStart_1805450 baseEnd_1805450 := by
    simpa [prefixWord, tailWord_1805450, baseEnd_1805450] using wordTrace_append hprefix tailTrace_1805450
  have hstable : (prefixWord ++ tailWord_1805450).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1805450).length < 2 ^ (prefixWord ++ tailWord_1805450).sum := by decide
  have hdescent : baseEnd_1805450 < baseStart_1805450 := by decide
  rcases family_descends (prefixWord ++ tailWord_1805450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1805471 : List Nat := [1, 1, 2, 6, 3, 1, 1, 2, 2, 3]
def baseStart_1805471 : Nat := 118140960795 + 1805471 * 2 ^ 59
def prefixEnd_1805471 : Nat := 4983230072969 + 3 ^ 40 * 1805471 * 2
def baseEnd_1805471 : Nat := 618049620502540546739531

theorem tailTrace_1805471 : CollatzResearch.WordTrace tailWord_1805471 prefixEnd_1805471 618049620502540546739531 := by
  unfold tailWord_1805471
  simp only [CollatzResearch.WordTrace]
  refine ⟨65850937242094391742920267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43900624828062927828613511 65850937242094391742920267)
  ·
    refine ⟨98776405863141587614380401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65850937242094391742920267 98776405863141587614380401)
    ·
      refine ⟨74082304397356190710785301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98776405863141587614380401 74082304397356190710785301)
      ·
        refine ⟨3472608018626071439568061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 74082304397356190710785301 3472608018626071439568061)
        ·
          refine ⟨1302228006984776789838023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3472608018626071439568061 1302228006984776789838023)
          ·
            refine ⟨1953342010477165184757035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1302228006984776789838023 1953342010477165184757035)
            ·
              refine ⟨2930013015715747777135553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1953342010477165184757035 2930013015715747777135553)
              ·
                refine ⟨2197509761786810832851665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2930013015715747777135553 2197509761786810832851665)
                ·
                  refine ⟨1648132321340108124638749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2197509761786810832851665 1648132321340108124638749)
                  ·
                    refine ⟨618049620502540546739531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1648132321340108124638749 618049620502540546739531)
                    ·
                      rfl

theorem cell22_1805471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 1, 1, 2, 2, 3].length) (baseStart_1805471 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1805471 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1805471 prefixEnd_1805471 := by exact prefixLift 1805471
  have htrace : WordTrace (prefixWord ++ tailWord_1805471) baseStart_1805471 baseEnd_1805471 := by
    simpa [prefixWord, tailWord_1805471, baseEnd_1805471] using wordTrace_append hprefix tailTrace_1805471
  have hstable : (prefixWord ++ tailWord_1805471).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1805471).length < 2 ^ (prefixWord ++ tailWord_1805471).sum := by decide
  have hdescent : baseEnd_1805471 < baseStart_1805471 := by decide
  rcases family_descends (prefixWord ++ tailWord_1805471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1805533 : List Nat := [1, 4, 3, 2, 2, 1, 3, 2, 1, 3]
def baseStart_1805533 : Nat := 118140960795 + 1805533 * 2 ^ 59
def prefixEnd_1805533 : Nat := 4983230072969 + 3 ^ 40 * 1805533 * 2
def baseEnd_1805533 : Nat := 618070844369593051689341

theorem tailTrace_1805533 : CollatzResearch.WordTrace tailWord_1805533 prefixEnd_1805533 618070844369593051689341 := by
  unfold tailWord_1805533
  simp only [CollatzResearch.WordTrace]
  refine ⟨65853198567869776331677253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43902132378579850887784835 65853198567869776331677253)
  ·
    refine ⟨12347474731475583062189485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65853198567869776331677253 12347474731475583062189485)
    ·
      refine ⟨4630303024303343648321057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12347474731475583062189485 4630303024303343648321057)
      ·
        refine ⟨3472727268227507736240793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4630303024303343648321057 3472727268227507736240793)
        ·
          refine ⟨2604545451170630802180595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3472727268227507736240793 2604545451170630802180595)
          ·
            refine ⟨3906818176755946203270893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2604545451170630802180595 3906818176755946203270893)
            ·
              refine ⟨1465056816283479826226585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3906818176755946203270893 1465056816283479826226585)
              ·
                refine ⟨1098792612212609869669939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1465056816283479826226585 1098792612212609869669939)
                ·
                  refine ⟨1648188918318914804504909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1098792612212609869669939 1648188918318914804504909)
                  ·
                    refine ⟨618070844369593051689341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1648188918318914804504909 618070844369593051689341)
                    ·
                      rfl

theorem cell22_1805533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 3, 2, 1, 3].length) (baseStart_1805533 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1805533 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1805533 prefixEnd_1805533 := by exact prefixLift 1805533
  have htrace : WordTrace (prefixWord ++ tailWord_1805533) baseStart_1805533 baseEnd_1805533 := by
    simpa [prefixWord, tailWord_1805533, baseEnd_1805533] using wordTrace_append hprefix tailTrace_1805533
  have hstable : (prefixWord ++ tailWord_1805533).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1805533).length < 2 ^ (prefixWord ++ tailWord_1805533).sum := by decide
  have hdescent : baseEnd_1805533 < baseStart_1805533 := by decide
  rcases family_descends (prefixWord ++ tailWord_1805533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1805540 : List Nat := [2, 3, 1, 1, 1, 2, 5, 1, 6]
def baseStart_1805540 : Nat := 118140960795 + 1805540 * 2 ^ 59
def prefixEnd_1805540 : Nat := 4983230072969 + 3 ^ 40 * 1805540 * 2
def baseEnd_1805540 : Nat := 206024413537549122254773

theorem tailTrace_1805540 : CollatzResearch.WordTrace tailWord_1805540 prefixEnd_1805540 206024413537549122254773 := by
  unfold tailWord_1805540
  simp only [CollatzResearch.WordTrace]
  refine ⟨32926726939422208263591037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43902302585896277684788049 32926726939422208263591037)
  ·
    refine ⟨12347522602283328098846639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32926726939422208263591037 12347522602283328098846639)
    ·
      refine ⟨18521283903424992148269959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12347522602283328098846639 18521283903424992148269959)
      ·
        refine ⟨27781925855137488222404939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18521283903424992148269959 27781925855137488222404939)
        ·
          refine ⟨41672888782706232333607409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27781925855137488222404939 41672888782706232333607409)
          ·
            refine ⟨31254666587029674250205557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41672888782706232333607409 31254666587029674250205557)
            ·
              refine ⟨2930124992534031960956771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31254666587029674250205557 2930124992534031960956771)
              ·
                refine ⟨4395187488801047941435157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2930124992534031960956771 4395187488801047941435157)
                ·
                  refine ⟨206024413537549122254773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4395187488801047941435157 206024413537549122254773)
                  ·
                    rfl

theorem cell22_1805540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 5, 1, 6].length) (baseStart_1805540 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1805540 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1805540 prefixEnd_1805540 := by exact prefixLift 1805540
  have htrace : WordTrace (prefixWord ++ tailWord_1805540) baseStart_1805540 baseEnd_1805540 := by
    simpa [prefixWord, tailWord_1805540, baseEnd_1805540] using wordTrace_append hprefix tailTrace_1805540
  have hstable : (prefixWord ++ tailWord_1805540).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1805540).length < 2 ^ (prefixWord ++ tailWord_1805540).sum := by decide
  have hdescent : baseEnd_1805540 < baseStart_1805540 := by decide
  rcases family_descends (prefixWord ++ tailWord_1805540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1805572 : List Nat := [2, 3, 2, 2, 2, 2, 1, 2, 1, 5]
def baseStart_1805572 : Nat := 118140960795 + 1805572 * 2 ^ 59
def prefixEnd_1805572 : Nat := 4983230072969 + 3 ^ 40 * 1805572 * 2
def baseEnd_1805572 : Nat := 618084194866609949964221

theorem tailTrace_1805572 : CollatzResearch.WordTrace tailWord_1805572 prefixEnd_1805572 618084194866609949964221 := by
  unfold tailWord_1805572
  simp only [CollatzResearch.WordTrace]
  refine ⟨32927310507364242996173485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43903080676485657328231313 32927310507364242996173485)
  ·
    refine ⟨12347741440261591123565057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32927310507364242996173485 12347741440261591123565057)
    ·
      refine ⟨9260806080196193342673793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12347741440261591123565057 9260806080196193342673793)
      ·
        refine ⟨6945604560147145007005345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9260806080196193342673793 6945604560147145007005345)
        ·
          refine ⟨5209203420110358755254009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6945604560147145007005345 5209203420110358755254009)
          ·
            refine ⟨3906902565082769066440507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5209203420110358755254009 3906902565082769066440507)
            ·
              refine ⟨5860353847624153599660761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3906902565082769066440507 5860353847624153599660761)
              ·
                refine ⟨4395265385718115199745571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5860353847624153599660761 4395265385718115199745571)
                ·
                  refine ⟨6592898078577172799618357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4395265385718115199745571 6592898078577172799618357)
                  ·
                    refine ⟨618084194866609949964221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6592898078577172799618357 618084194866609949964221)
                    ·
                      rfl

theorem cell22_1805572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 1, 2, 1, 5].length) (baseStart_1805572 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1805572 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1805572 prefixEnd_1805572 := by exact prefixLift 1805572
  have htrace : WordTrace (prefixWord ++ tailWord_1805572) baseStart_1805572 baseEnd_1805572 := by
    simpa [prefixWord, tailWord_1805572, baseEnd_1805572] using wordTrace_append hprefix tailTrace_1805572
  have hstable : (prefixWord ++ tailWord_1805572).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1805572).length < 2 ^ (prefixWord ++ tailWord_1805572).sum := by decide
  have hdescent : baseEnd_1805572 < baseStart_1805572 := by decide
  rcases family_descends (prefixWord ++ tailWord_1805572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1805617 : List Nat := [1, 2, 2, 3, 3, 1, 1, 1, 5, 3]
def baseStart_1805617 : Nat := 118140960795 + 1805617 * 2 ^ 59
def prefixEnd_1805617 : Nat := 4983230072969 + 3 ^ 40 * 1805617 * 2
def baseEnd_1805617 : Nat := 618099599286244832589083

theorem tailTrace_1805617 : CollatzResearch.WordTrace tailWord_1805617 prefixEnd_1805617 618099599286244832589083 := by
  unfold tailWord_1805617
  simp only [CollatzResearch.WordTrace]
  refine ⟨65856262299565458677735105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43904174866376972451823403 65856262299565458677735105)
  ·
    refine ⟨49392196724674094008301329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65856262299565458677735105 49392196724674094008301329)
    ·
      refine ⟨37044147543505570506225997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49392196724674094008301329 37044147543505570506225997)
      ·
        refine ⟨13891555328814588939834749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37044147543505570506225997 13891555328814588939834749)
        ·
          refine ⟨5209333248305470852438031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13891555328814588939834749 5209333248305470852438031)
          ·
            refine ⟨7813999872458206278657047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5209333248305470852438031 7813999872458206278657047)
            ·
              refine ⟨11720999808687309417985571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7813999872458206278657047 11720999808687309417985571)
              ·
                refine ⟨17581499713030964126978357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11720999808687309417985571 17581499713030964126978357)
                ·
                  refine ⟨1648265598096652886904221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 17581499713030964126978357 1648265598096652886904221)
                  ·
                    refine ⟨618099599286244832589083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1648265598096652886904221 618099599286244832589083)
                    ·
                      rfl

theorem cell22_1805617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 1, 5, 3].length) (baseStart_1805617 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1805617 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1805617 prefixEnd_1805617 := by exact prefixLift 1805617
  have htrace : WordTrace (prefixWord ++ tailWord_1805617) baseStart_1805617 baseEnd_1805617 := by
    simpa [prefixWord, tailWord_1805617, baseEnd_1805617] using wordTrace_append hprefix tailTrace_1805617
  have hstable : (prefixWord ++ tailWord_1805617).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1805617).length < 2 ^ (prefixWord ++ tailWord_1805617).sum := by decide
  have hdescent : baseEnd_1805617 < baseStart_1805617 := by decide
  rcases family_descends (prefixWord ++ tailWord_1805617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1805664 : List Nat := [2, 1, 1, 3, 4, 2, 3, 1, 5]
def baseStart_1805664 : Nat := 118140960795 + 1805664 * 2 ^ 59
def prefixEnd_1805664 : Nat := 4983230072969 + 3 ^ 40 * 1805664 * 2
def baseEnd_1805664 : Nat := 206038562782250792221313

theorem tailTrace_1805664 : CollatzResearch.WordTrace tailWord_1805664 prefixEnd_1805664 206038562782250792221313 := by
  unfold tailWord_1805664
  simp only [CollatzResearch.WordTrace]
  refine ⟨32928988265197592852348023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43905317686930123803130697 32928988265197592852348023)
  ·
    refine ⟨49393482397796389278522035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32928988265197592852348023 49393482397796389278522035)
    ·
      refine ⟨74090223596694583917783053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49393482397796389278522035 74090223596694583917783053)
      ·
        refine ⟨27783833848760468969168645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74090223596694583917783053 27783833848760468969168645)
        ·
          refine ⟨5209468846642587931719121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27783833848760468969168645 5209468846642587931719121)
          ·
            refine ⟨3907101634981940948789341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5209468846642587931719121 3907101634981940948789341)
            ·
              refine ⟨1465163113118227855796003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3907101634981940948789341 1465163113118227855796003)
              ·
                refine ⟨2197744669677341783694005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1465163113118227855796003 2197744669677341783694005)
                ·
                  refine ⟨206038562782250792221313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2197744669677341783694005 206038562782250792221313)
                  ·
                    rfl

theorem cell22_1805664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 3, 1, 5].length) (baseStart_1805664 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1805664 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1805664 prefixEnd_1805664 := by exact prefixLift 1805664
  have htrace : WordTrace (prefixWord ++ tailWord_1805664) baseStart_1805664 baseEnd_1805664 := by
    simpa [prefixWord, tailWord_1805664, baseEnd_1805664] using wordTrace_append hprefix tailTrace_1805664
  have hstable : (prefixWord ++ tailWord_1805664).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1805664).length < 2 ^ (prefixWord ++ tailWord_1805664).sum := by decide
  have hdescent : baseEnd_1805664 < baseStart_1805664 := by decide
  rcases family_descends (prefixWord ++ tailWord_1805664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1805685 : List Nat := [1, 3, 4, 1, 4, 1, 1, 3, 1, 3]
def baseStart_1805685 : Nat := 118140960795 + 1805685 * 2 ^ 59
def prefixEnd_1805685 : Nat := 4983230072969 + 3 ^ 40 * 1805685 * 2
def baseEnd_1805685 : Nat := 618122877075915321888875

theorem tailTrace_1805685 : CollatzResearch.WordTrace tailWord_1805685 prefixEnd_1805685 618122877075915321888875 := by
  unfold tailWord_1805685
  simp only [CollatzResearch.WordTrace]
  refine ⟨65858742463319106291210509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43905828308879404194140339 65858742463319106291210509)
  ·
    refine ⟨24697028423744664859203941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65858742463319106291210509 24697028423744664859203941)
    ·
      refine ⟨4630692829452124661100739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24697028423744664859203941 4630692829452124661100739)
      ·
        refine ⟨6946039244178186991651109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4630692829452124661100739 6946039244178186991651109)
        ·
          refine ⟨1302382358283410060934583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6946039244178186991651109 1302382358283410060934583)
          ·
            refine ⟨1953573537425115091401875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1302382358283410060934583 1953573537425115091401875)
            ·
              refine ⟨2930360306137672637102813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1953573537425115091401875 2930360306137672637102813)
              ·
                refine ⟨1098885114801627238913555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2930360306137672637102813 1098885114801627238913555)
                ·
                  refine ⟨1648327672202440858370333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1098885114801627238913555 1648327672202440858370333)
                  ·
                    refine ⟨618122877075915321888875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1648327672202440858370333 618122877075915321888875)
                    ·
                      rfl

theorem cell22_1805685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 1, 1, 3, 1, 3].length) (baseStart_1805685 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1805685 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1805685 prefixEnd_1805685 := by exact prefixLift 1805685
  have htrace : WordTrace (prefixWord ++ tailWord_1805685) baseStart_1805685 baseEnd_1805685 := by
    simpa [prefixWord, tailWord_1805685, baseEnd_1805685] using wordTrace_append hprefix tailTrace_1805685
  have hstable : (prefixWord ++ tailWord_1805685).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1805685).length < 2 ^ (prefixWord ++ tailWord_1805685).sum := by decide
  have hdescent : baseEnd_1805685 < baseStart_1805685 := by decide
  rcases family_descends (prefixWord ++ tailWord_1805685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1805707 : List Nat := [1, 1, 1, 1, 4, 3, 1, 3, 4, 3]
def baseStart_1805707 : Nat := 118140960795 + 1805707 * 2 ^ 59
def prefixEnd_1805707 : Nat := 4983230072969 + 3 ^ 40 * 1805707 * 2
def baseEnd_1805707 : Nat := 618130408125514597838807

theorem tailTrace_1805707 : CollatzResearch.WordTrace tailWord_1805707 prefixEnd_1805707 618130408125514597838807 := by
  unfold tailWord_1805707
  simp only [CollatzResearch.WordTrace]
  refine ⟨65859544869239404048511375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43906363246159602699007583 65859544869239404048511375)
  ·
    refine ⟨98789317303859106072767063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65859544869239404048511375 98789317303859106072767063)
    ·
      refine ⟨148183975955788659109150595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98789317303859106072767063 148183975955788659109150595)
      ·
        refine ⟨222275963933682988663725893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148183975955788659109150595 222275963933682988663725893)
        ·
          refine ⟨41676743237565560374448605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 222275963933682988663725893 41676743237565560374448605)
          ·
            refine ⟨15628778714087085140418227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41676743237565560374448605 15628778714087085140418227)
            ·
              refine ⟨23443168071130627710627341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15628778714087085140418227 23443168071130627710627341)
              ·
                refine ⟨8791188026673985391485253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23443168071130627710627341 8791188026673985391485253)
                ·
                  refine ⟨1648347755001372260903485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8791188026673985391485253 1648347755001372260903485)
                  ·
                    refine ⟨618130408125514597838807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1648347755001372260903485 618130408125514597838807)
                    ·
                      rfl

theorem cell22_1805707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 3, 4, 3].length) (baseStart_1805707 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1805707 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1805707 prefixEnd_1805707 := by exact prefixLift 1805707
  have htrace : WordTrace (prefixWord ++ tailWord_1805707) baseStart_1805707 baseEnd_1805707 := by
    simpa [prefixWord, tailWord_1805707, baseEnd_1805707] using wordTrace_append hprefix tailTrace_1805707
  have hstable : (prefixWord ++ tailWord_1805707).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1805707).length < 2 ^ (prefixWord ++ tailWord_1805707).sum := by decide
  have hdescent : baseEnd_1805707 < baseStart_1805707 := by decide
  rcases family_descends (prefixWord ++ tailWord_1805707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1805722 : List Nat := [3, 1, 1, 4, 1, 1, 1, 2, 4, 4]
def baseStart_1805722 : Nat := 118140960795 + 1805722 * 2 ^ 59
def prefixEnd_1805722 : Nat := 4983230072969 + 3 ^ 40 * 1805722 * 2
def baseEnd_1805722 : Nat := 618135542932059558713761

theorem tailTrace_1805722 : CollatzResearch.WordTrace tailWord_1805722 prefixEnd_1805722 618135542932059558713761 := by
  unfold tailWord_1805722
  simp only [CollatzResearch.WordTrace]
  refine ⟨16465022991046265402576855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43906727976123374406871613 16465022991046265402576855)
  ·
    refine ⟨24697534486569398103865283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16465022991046265402576855 24697534486569398103865283)
    ·
      refine ⟨37046301729854097155797925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24697534486569398103865283 37046301729854097155797925)
      ·
        refine ⟨6946181574347643216712111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37046301729854097155797925 6946181574347643216712111)
        ·
          refine ⟨10419272361521464825068167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6946181574347643216712111 10419272361521464825068167)
          ·
            refine ⟨15628908542282197237602251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10419272361521464825068167 15628908542282197237602251)
            ·
              refine ⟨23443362813423295856403377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15628908542282197237602251 23443362813423295856403377)
              ·
                refine ⟨17582522110067471892302533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23443362813423295856403377 17582522110067471892302533)
                ·
                  refine ⟨3296722895637650979806725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17582522110067471892302533 3296722895637650979806725)
                  ·
                    refine ⟨618135542932059558713761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3296722895637650979806725 618135542932059558713761)
                    ·
                      rfl

theorem cell22_1805722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 2, 4, 4].length) (baseStart_1805722 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1805722 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1805722 prefixEnd_1805722 := by exact prefixLift 1805722
  have htrace : WordTrace (prefixWord ++ tailWord_1805722) baseStart_1805722 baseEnd_1805722 := by
    simpa [prefixWord, tailWord_1805722, baseEnd_1805722] using wordTrace_append hprefix tailTrace_1805722
  have hstable : (prefixWord ++ tailWord_1805722).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1805722).length < 2 ^ (prefixWord ++ tailWord_1805722).sum := by decide
  have hdescent : baseEnd_1805722 < baseStart_1805722 := by decide
  rcases family_descends (prefixWord ++ tailWord_1805722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1805814 : List Nat := [5, 1, 1, 1, 2, 2, 1, 2, 2, 5]
def baseStart_1805814 : Nat := 118140960795 + 1805814 * 2 ^ 59
def prefixEnd_1805814 : Nat := 4983230072969 + 3 ^ 40 * 1805814 * 2
def baseEnd_1805814 : Nat := 618167036412201985413479

theorem tailTrace_1805814 : CollatzResearch.WordTrace tailWord_1805814 prefixEnd_1805814 618167036412201985413479 := by
  unfold tailWord_1805814
  simp only [CollatzResearch.WordTrace]
  refine ⟨4116465467490735082666031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 43908964986567840881770997 4116465467490735082666031)
  ·
    refine ⟨6174698201236102623999047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4116465467490735082666031 6174698201236102623999047)
    ·
      refine ⟨9262047301854153935998571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6174698201236102623999047 9262047301854153935998571)
      ·
        refine ⟨13893070952781230903997857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9262047301854153935998571 13893070952781230903997857)
        ·
          refine ⟨10419803214585923177998393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13893070952781230903997857 10419803214585923177998393)
          ·
            refine ⟨7814852410939442383498795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10419803214585923177998393 7814852410939442383498795)
            ·
              refine ⟨11722278616409163575248193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7814852410939442383498795 11722278616409163575248193)
              ·
                refine ⟨8791708962306872681436145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11722278616409163575248193 8791708962306872681436145)
                ·
                  refine ⟨6593781721730154511077109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8791708962306872681436145 6593781721730154511077109)
                  ·
                    refine ⟨618167036412201985413479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6593781721730154511077109 618167036412201985413479)
                    ·
                      rfl

theorem cell22_1805814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 2, 2, 5].length) (baseStart_1805814 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1805814 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1805814 prefixEnd_1805814 := by exact prefixLift 1805814
  have htrace : WordTrace (prefixWord ++ tailWord_1805814) baseStart_1805814 baseEnd_1805814 := by
    simpa [prefixWord, tailWord_1805814, baseEnd_1805814] using wordTrace_append hprefix tailTrace_1805814
  have hstable : (prefixWord ++ tailWord_1805814).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1805814).length < 2 ^ (prefixWord ++ tailWord_1805814).sum := by decide
  have hdescent : baseEnd_1805814 < baseStart_1805814 := by decide
  rcases family_descends (prefixWord ++ tailWord_1805814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1805878 : List Nat := [5, 1, 2, 1, 3, 2, 1, 1, 6]
def baseStart_1805878 : Nat := 118140960795 + 1805878 * 2 ^ 59
def prefixEnd_1805878 : Nat := 4983230072969 + 3 ^ 40 * 1805878 * 2
def baseEnd_1805878 : Nat := 206062981640042383937761

theorem tailTrace_1805878 : CollatzResearch.WordTrace tailWord_1805878 prefixEnd_1805878 206062981640042383937761 := by
  unfold tailWord_1805878
  simp only [CollatzResearch.WordTrace]
  refine ⟨4116611359476243765811643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 43910521167746600168657525 4116611359476243765811643)
  ·
    refine ⟨6174917039214365648717465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4116611359476243765811643 6174917039214365648717465)
    ·
      refine ⟨4631187779410774236538099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6174917039214365648717465 4631187779410774236538099)
      ·
        refine ⟨6946781669116161354807149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4631187779410774236538099 6946781669116161354807149)
        ·
          refine ⟨2605043125918560508052681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6946781669116161354807149 2605043125918560508052681)
          ·
            refine ⟨1953782344438920381039511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2605043125918560508052681 1953782344438920381039511)
            ·
              refine ⟨2930673516658380571559267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1953782344438920381039511 2930673516658380571559267)
              ·
                refine ⟨4396010274987570857338901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2930673516658380571559267 4396010274987570857338901)
                ·
                  refine ⟨206062981640042383937761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4396010274987570857338901 206062981640042383937761)
                  ·
                    rfl

theorem cell22_1805878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 2, 1, 1, 6].length) (baseStart_1805878 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1805878 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1805878 prefixEnd_1805878 := by exact prefixLift 1805878
  have htrace : WordTrace (prefixWord ++ tailWord_1805878) baseStart_1805878 baseEnd_1805878 := by
    simpa [prefixWord, tailWord_1805878, baseEnd_1805878] using wordTrace_append hprefix tailTrace_1805878
  have hstable : (prefixWord ++ tailWord_1805878).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1805878).length < 2 ^ (prefixWord ++ tailWord_1805878).sum := by decide
  have hdescent : baseEnd_1805878 < baseStart_1805878 := by decide
  rcases family_descends (prefixWord ++ tailWord_1805878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1805889 : List Nat := [1, 2, 5, 1, 1, 1, 4, 7]
def baseStart_1805889 : Nat := 118140960795 + 1805889 * 2 ^ 59
def prefixEnd_1805889 : Nat := 4983230072969 + 3 ^ 40 * 1805889 * 2
def baseEnd_1805889 : Nat := 68688078938325198865361

theorem tailTrace_1805889 : CollatzResearch.WordTrace tailWord_1805889 prefixEnd_1805889 68688078938325198865361 := by
  unfold tailWord_1805889
  simp only [CollatzResearch.WordTrace]
  refine ⟨65866182954580049131636721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43910788636386699421091147 65866182954580049131636721)
  ·
    refine ⟨49399637215935036848727541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65866182954580049131636721 49399637215935036848727541)
    ·
      refine ⟨4631215988993909704568207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 49399637215935036848727541 4631215988993909704568207)
      ·
        refine ⟨6946823983490864556852311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4631215988993909704568207 6946823983490864556852311)
        ·
          refine ⟨10420235975236296835278467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6946823983490864556852311 10420235975236296835278467)
          ·
            refine ⟨15630353962854445252917701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10420235975236296835278467 15630353962854445252917701)
            ·
              refine ⟨2930691368035208484922069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15630353962854445252917701 2930691368035208484922069)
              ·
                refine ⟨68688078938325198865361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2930691368035208484922069 68688078938325198865361)
                ·
                  rfl

theorem cell22_1805889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 4, 7].length) (baseStart_1805889 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1805889 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1805889 prefixEnd_1805889 := by exact prefixLift 1805889
  have htrace : WordTrace (prefixWord ++ tailWord_1805889) baseStart_1805889 baseEnd_1805889 := by
    simpa [prefixWord, tailWord_1805889, baseEnd_1805889] using wordTrace_append hprefix tailTrace_1805889
  have hstable : (prefixWord ++ tailWord_1805889).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1805889).length < 2 ^ (prefixWord ++ tailWord_1805889).sum := by decide
  have hdescent : baseEnd_1805889 < baseStart_1805889 := by decide
  rcases family_descends (prefixWord ++ tailWord_1805889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1805904 : List Nat := [2, 1, 1, 1, 1, 3, 4, 1, 5, 3]
def baseStart_1805904 : Nat := 118140960795 + 1805904 * 2 ^ 59
def prefixEnd_1805904 : Nat := 4983230072969 + 3 ^ 40 * 1805904 * 2
def baseEnd_1805904 : Nat := 618197845251471750663203

theorem tailTrace_1805904 : CollatzResearch.WordTrace tailWord_1805904 prefixEnd_1805904 618197845251471750663203 := by
  unfold tailWord_1805904
  simp only [CollatzResearch.WordTrace]
  refine ⟨32933365024762853346716383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43911153366350471128955177 32933365024762853346716383)
  ·
    refine ⟨49400047537144280020074575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32933365024762853346716383 49400047537144280020074575)
    ·
      refine ⟨74100071305716420030111863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49400047537144280020074575 74100071305716420030111863)
      ·
        refine ⟨111150106958574630045167795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74100071305716420030111863 111150106958574630045167795)
        ·
          refine ⟨166725160437861945067751693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111150106958574630045167795 166725160437861945067751693)
          ·
            refine ⟨62521935164198229400406885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 166725160437861945067751693 62521935164198229400406885)
            ·
              refine ⟨11722862843287168012576291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62521935164198229400406885 11722862843287168012576291)
              ·
                refine ⟨17584294264930752018864437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11722862843287168012576291 17584294264930752018864437)
                ·
                  refine ⟨1648527587337258001768541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 17584294264930752018864437 1648527587337258001768541)
                  ·
                    refine ⟨618197845251471750663203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1648527587337258001768541 618197845251471750663203)
                    ·
                      rfl

theorem cell22_1805904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 1, 5, 3].length) (baseStart_1805904 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1805904 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1805904 prefixEnd_1805904 := by exact prefixLift 1805904
  have htrace : WordTrace (prefixWord ++ tailWord_1805904) baseStart_1805904 baseEnd_1805904 := by
    simpa [prefixWord, tailWord_1805904, baseEnd_1805904] using wordTrace_append hprefix tailTrace_1805904
  have hstable : (prefixWord ++ tailWord_1805904).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1805904).length < 2 ^ (prefixWord ++ tailWord_1805904).sum := by decide
  have hdescent : baseEnd_1805904 < baseStart_1805904 := by decide
  rcases family_descends (prefixWord ++ tailWord_1805904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1805910 : List Nat := [5, 2, 2, 2, 1, 1, 1, 2, 1, 5]
def baseStart_1805910 : Nat := 118140960795 + 1805910 * 2 ^ 59
def prefixEnd_1805910 : Nat := 4983230072969 + 3 ^ 40 * 1805910 * 2
def baseEnd_1805910 : Nat := 618199899174089735013185

theorem tailTrace_1805910 : CollatzResearch.WordTrace tailWord_1805910 prefixEnd_1805910 618199899174089735013185 := by
  unfold tailWord_1805910
  simp only [CollatzResearch.WordTrace]
  refine ⟨4116684305468998107384449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 43911299258335979812100789 4116684305468998107384449)
  ·
    refine ⟨3087513229101748580538337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4116684305468998107384449 3087513229101748580538337)
    ·
      refine ⟨2315634921826311435403753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3087513229101748580538337 2315634921826311435403753)
      ·
        refine ⟨1736726191369733576552815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2315634921826311435403753 1736726191369733576552815)
        ·
          refine ⟨2605089287054600364829223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1736726191369733576552815 2605089287054600364829223)
          ·
            refine ⟨3907633930581900547243835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2605089287054600364829223 3907633930581900547243835)
            ·
              refine ⟨5861450895872850820865753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3907633930581900547243835 5861450895872850820865753)
              ·
                refine ⟨4396088171904638115649315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5861450895872850820865753 4396088171904638115649315)
                ·
                  refine ⟨6594132257856957173473973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4396088171904638115649315 6594132257856957173473973)
                  ·
                    refine ⟨618199899174089735013185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6594132257856957173473973 618199899174089735013185)
                    ·
                      rfl

theorem cell22_1805910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 1, 2, 1, 5].length) (baseStart_1805910 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1805910 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1805910 prefixEnd_1805910 := by exact prefixLift 1805910
  have htrace : WordTrace (prefixWord ++ tailWord_1805910) baseStart_1805910 baseEnd_1805910 := by
    simpa [prefixWord, tailWord_1805910, baseEnd_1805910] using wordTrace_append hprefix tailTrace_1805910
  have hstable : (prefixWord ++ tailWord_1805910).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1805910).length < 2 ^ (prefixWord ++ tailWord_1805910).sum := by decide
  have hdescent : baseEnd_1805910 < baseStart_1805910 := by decide
  rcases family_descends (prefixWord ++ tailWord_1805910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1805949 : List Nat := [1, 4, 1, 1, 4, 1, 1, 1, 1, 7]
def baseStart_1805949 : Nat := 118140960795 + 1805949 * 2 ^ 59
def prefixEnd_1805949 : Nat := 4983230072969 + 3 ^ 40 * 1805949 * 2
def baseEnd_1805949 : Nat := 618213249671106633288065

theorem tailTrace_1805949 : CollatzResearch.WordTrace tailWord_1805949 prefixEnd_1805949 618213249671106633288065 := by
  unfold tailWord_1805949
  simp only [CollatzResearch.WordTrace]
  refine ⟨65868371334362679378820901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43912247556241786252547267 65868371334362679378820901)
  ·
    refine ⟨12350319625193002383528919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65868371334362679378820901 12350319625193002383528919)
    ·
      refine ⟨18525479437789503575293379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12350319625193002383528919 18525479437789503575293379)
      ·
        refine ⟨27788219156684255362940069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18525479437789503575293379 27788219156684255362940069)
        ·
          refine ⟨5210291091878297880551263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27788219156684255362940069 5210291091878297880551263)
          ·
            refine ⟨7815436637817446820826895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5210291091878297880551263 7815436637817446820826895)
            ·
              refine ⟨11723154956726170231240343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7815436637817446820826895 11723154956726170231240343)
              ·
                refine ⟨17584732435089255346860515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11723154956726170231240343 17584732435089255346860515)
                ·
                  refine ⟨26377098652633883020290773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17584732435089255346860515 26377098652633883020290773)
                  ·
                    refine ⟨618213249671106633288065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 26377098652633883020290773 618213249671106633288065)
                    ·
                      rfl

theorem cell22_1805949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 1, 1, 7].length) (baseStart_1805949 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1805949 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1805949 prefixEnd_1805949 := by exact prefixLift 1805949
  have htrace : WordTrace (prefixWord ++ tailWord_1805949) baseStart_1805949 baseEnd_1805949 := by
    simpa [prefixWord, tailWord_1805949, baseEnd_1805949] using wordTrace_append hprefix tailTrace_1805949
  have hstable : (prefixWord ++ tailWord_1805949).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1805949).length < 2 ^ (prefixWord ++ tailWord_1805949).sum := by decide
  have hdescent : baseEnd_1805949 < baseStart_1805949 := by decide
  rcases family_descends (prefixWord ++ tailWord_1805949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1805964 : List Nat := [2, 2, 1, 2, 1, 1, 3, 3, 3, 4]
def baseStart_1805964 : Nat := 118140960795 + 1805964 * 2 ^ 59
def prefixEnd_1805964 : Nat := 4983230072969 + 3 ^ 40 * 1805964 * 2
def baseEnd_1805964 : Nat := 618218384477651594163019

theorem tailTrace_1805964 : CollatzResearch.WordTrace tailWord_1805964 prefixEnd_1805964 618218384477651594163019 := by
  unfold tailWord_1805964
  simp only [CollatzResearch.WordTrace]
  refine ⟨32934459214654168470308473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43912612286205557960411297 32934459214654168470308473)
  ·
    refine ⟨24700844410990626352731355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32934459214654168470308473 24700844410990626352731355)
    ·
      refine ⟨37051266616485939529097033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24700844410990626352731355 37051266616485939529097033)
      ·
        refine ⟨27788449962364454646822775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37051266616485939529097033 27788449962364454646822775)
        ·
          refine ⟨41682674943546681970234163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27788449962364454646822775 41682674943546681970234163)
          ·
            refine ⟨62524012415320022955351245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41682674943546681970234163 62524012415320022955351245)
            ·
              refine ⟨23446504655745008608256717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62524012415320022955351245 23446504655745008608256717)
              ·
                refine ⟨8792439245904378228096269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23446504655745008608256717 8792439245904378228096269)
                ·
                  refine ⟨3297164717214141835536101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8792439245904378228096269 3297164717214141835536101)
                  ·
                    refine ⟨618218384477651594163019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3297164717214141835536101 618218384477651594163019)
                    ·
                      rfl

theorem cell22_1805964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 3, 3, 4].length) (baseStart_1805964 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1805964 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1805964 prefixEnd_1805964 := by exact prefixLift 1805964
  have htrace : WordTrace (prefixWord ++ tailWord_1805964) baseStart_1805964 baseEnd_1805964 := by
    simpa [prefixWord, tailWord_1805964, baseEnd_1805964] using wordTrace_append hprefix tailTrace_1805964
  have hstable : (prefixWord ++ tailWord_1805964).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1805964).length < 2 ^ (prefixWord ++ tailWord_1805964).sum := by decide
  have hdescent : baseEnd_1805964 < baseStart_1805964 := by decide
  rcases family_descends (prefixWord ++ tailWord_1805964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1805972 : List Nat := [2, 4, 2, 2, 2, 1, 2, 3, 1, 3]
def baseStart_1805972 : Nat := 118140960795 + 1805972 * 2 ^ 59
def prefixEnd_1805972 : Nat := 4983230072969 + 3 ^ 40 * 1805972 * 2
def baseEnd_1805972 : Nat := 618221123041142239962995

theorem tailTrace_1805972 : CollatzResearch.WordTrace tailWord_1805972 prefixEnd_1805972 618221123041142239962995 := by
  unfold tailWord_1805972
  simp only [CollatzResearch.WordTrace]
  refine ⟨32934605106639677153454085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43912806808852902871272113 32934605106639677153454085)
  ·
    refine ⟨6175238457494939466272641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32934605106639677153454085 6175238457494939466272641)
    ·
      refine ⟨4631428843121204599704481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6175238457494939466272641 4631428843121204599704481)
      ·
        refine ⟨3473571632340903449778361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4631428843121204599704481 3473571632340903449778361)
        ·
          refine ⟨2605178724255677587333771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3473571632340903449778361 2605178724255677587333771)
          ·
            refine ⟨3907768086383516381000657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2605178724255677587333771 3907768086383516381000657)
            ·
              refine ⟨2930826064787637285750493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3907768086383516381000657 2930826064787637285750493)
              ·
                refine ⟨1099059774295363982156435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2930826064787637285750493 1099059774295363982156435)
                ·
                  refine ⟨1648589661443045973234653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1099059774295363982156435 1648589661443045973234653)
                  ·
                    refine ⟨618221123041142239962995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1648589661443045973234653 618221123041142239962995)
                    ·
                      rfl

theorem cell22_1805972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 2, 3, 1, 3].length) (baseStart_1805972 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1805972 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1805972 prefixEnd_1805972 := by exact prefixLift 1805972
  have htrace : WordTrace (prefixWord ++ tailWord_1805972) baseStart_1805972 baseEnd_1805972 := by
    simpa [prefixWord, tailWord_1805972, baseEnd_1805972] using wordTrace_append hprefix tailTrace_1805972
  have hstable : (prefixWord ++ tailWord_1805972).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1805972).length < 2 ^ (prefixWord ++ tailWord_1805972).sum := by decide
  have hdescent : baseEnd_1805972 < baseStart_1805972 := by decide
  rcases family_descends (prefixWord ++ tailWord_1805972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1806009 : List Nat := [1, 2, 1, 4, 1, 1, 3, 2, 1, 6]
def baseStart_1806009 : Nat := 118140960795 + 1806009 * 2 ^ 59
def prefixEnd_1806009 : Nat := 4983230072969 + 3 ^ 40 * 1806009 * 2
def baseEnd_1806009 : Nat := 618233788897286476787881

theorem tailTrace_1806009 : CollatzResearch.WordTrace tailWord_1806009 prefixEnd_1806009 618233788897286476787881 := by
  unfold tailWord_1806009
  simp only [CollatzResearch.WordTrace]
  refine ⟨65870559714145309626005081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43913706476096873084003387 65870559714145309626005081)
  ·
    refine ⟨49402919785608982219503811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65870559714145309626005081 49402919785608982219503811)
    ·
      refine ⟨74104379678413473329255717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49402919785608982219503811 74104379678413473329255717)
      ·
        refine ⟨13894571189702526249235447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74104379678413473329255717 13894571189702526249235447)
        ·
          refine ⟨20841856784553789373853171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13894571189702526249235447 20841856784553789373853171)
          ·
            refine ⟨31262785176830684060779757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20841856784553789373853171 31262785176830684060779757)
            ·
              refine ⟨11723544441311506522792409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31262785176830684060779757 11723544441311506522792409)
              ·
                refine ⟨8792658330983629892094307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11723544441311506522792409 8792658330983629892094307)
                ·
                  refine ⟨13188987496475444838141461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8792658330983629892094307 13188987496475444838141461)
                  ·
                    refine ⟨618233788897286476787881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13188987496475444838141461 618233788897286476787881)
                    ·
                      rfl

theorem cell22_1806009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 2, 1, 6].length) (baseStart_1806009 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1806009 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1806009 prefixEnd_1806009 := by exact prefixLift 1806009
  have htrace : WordTrace (prefixWord ++ tailWord_1806009) baseStart_1806009 baseEnd_1806009 := by
    simpa [prefixWord, tailWord_1806009, baseEnd_1806009] using wordTrace_append hprefix tailTrace_1806009
  have hstable : (prefixWord ++ tailWord_1806009).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1806009).length < 2 ^ (prefixWord ++ tailWord_1806009).sum := by decide
  have hdescent : baseEnd_1806009 < baseStart_1806009 := by decide
  rcases family_descends (prefixWord ++ tailWord_1806009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1806011 : List Nat := [1, 1, 1, 1, 1, 2, 3, 7, 2, 3]
def baseStart_1806011 : Nat := 118140960795 + 1806011 * 2 ^ 59
def prefixEnd_1806011 : Nat := 4983230072969 + 3 ^ 40 * 1806011 * 2
def baseEnd_1806011 : Nat := 618234473538159138237875

theorem tailTrace_1806011 : CollatzResearch.WordTrace tailWord_1806011 prefixEnd_1806011 618234473538159138237875 := by
  unfold tailWord_1806011
  simp only [CollatzResearch.WordTrace]
  refine ⟨65870632660138063967577887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43913755106758709311718591 65870632660138063967577887)
  ·
    refine ⟨98805948990207095951366831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65870632660138063967577887 98805948990207095951366831)
    ·
      refine ⟨148208923485310643927050247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98805948990207095951366831 148208923485310643927050247)
      ·
        refine ⟨222313385227965965890575371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148208923485310643927050247 222313385227965965890575371)
        ·
          refine ⟨333470077841948948835863057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 222313385227965965890575371 333470077841948948835863057)
          ·
            refine ⟨250102558381461711626897293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 333470077841948948835863057 250102558381461711626897293)
            ·
              refine ⟨93788459393048141860086485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 250102558381461711626897293 93788459393048141860086485)
              ·
                refine ⟨2198167017024565824845777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 93788459393048141860086485 2198167017024565824845777)
                ·
                  refine ⟨1648625262768424368634333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2198167017024565824845777 1648625262768424368634333)
                  ·
                    refine ⟨618234473538159138237875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1648625262768424368634333 618234473538159138237875)
                    ·
                      rfl

theorem cell22_1806011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 7, 2, 3].length) (baseStart_1806011 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1806011 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1806011 prefixEnd_1806011 := by exact prefixLift 1806011
  have htrace : WordTrace (prefixWord ++ tailWord_1806011) baseStart_1806011 baseEnd_1806011 := by
    simpa [prefixWord, tailWord_1806011, baseEnd_1806011] using wordTrace_append hprefix tailTrace_1806011
  have hstable : (prefixWord ++ tailWord_1806011).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1806011).length < 2 ^ (prefixWord ++ tailWord_1806011).sum := by decide
  have hdescent : baseEnd_1806011 < baseStart_1806011 := by decide
  rcases family_descends (prefixWord ++ tailWord_1806011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1806024 : List Nat := [2, 1, 3, 1, 2, 2, 3, 8]
def baseStart_1806024 : Nat := 118140960795 + 1806024 * 2 ^ 59
def prefixEnd_1806024 : Nat := 4983230072969 + 3 ^ 40 * 1806024 * 2
def baseEnd_1806024 : Nat := 68693213744870159740315

theorem tailTrace_1806024 : CollatzResearch.WordTrace tailWord_1806024 prefixEnd_1806024 68693213744870159740315 := by
  unfold tailWord_1806024
  simp only [CollatzResearch.WordTrace]
  refine ⟨32935553404545483593900563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43914071206060644791867417 32935553404545483593900563)
  ·
    refine ⟨49403330106818225390850845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32935553404545483593900563 49403330106818225390850845)
    ·
      refine ⟨18526248790056834521569067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49403330106818225390850845 18526248790056834521569067)
      ·
        refine ⟨27789373185085251782353601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18526248790056834521569067 27789373185085251782353601)
        ·
          refine ⟨20842029888813938836765201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27789373185085251782353601 20842029888813938836765201)
          ·
            refine ⟨15631522416610454127573901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20842029888813938836765201 15631522416610454127573901)
            ·
              refine ⟨5861820906228920297840213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15631522416610454127573901 5861820906228920297840213)
              ·
                refine ⟨68693213744870159740315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5861820906228920297840213 68693213744870159740315)
                ·
                  rfl

theorem cell22_1806024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 3, 8].length) (baseStart_1806024 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1806024 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1806024 prefixEnd_1806024 := by exact prefixLift 1806024
  have htrace : WordTrace (prefixWord ++ tailWord_1806024) baseStart_1806024 baseEnd_1806024 := by
    simpa [prefixWord, tailWord_1806024, baseEnd_1806024] using wordTrace_append hprefix tailTrace_1806024
  have hstable : (prefixWord ++ tailWord_1806024).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1806024).length < 2 ^ (prefixWord ++ tailWord_1806024).sum := by decide
  have hdescent : baseEnd_1806024 < baseStart_1806024 := by decide
  rcases family_descends (prefixWord ++ tailWord_1806024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1806103 : List Nat := [1, 1, 3, 4, 2, 2, 2, 2, 5]
def baseStart_1806103 : Nat := 118140960795 + 1806103 * 2 ^ 59
def prefixEnd_1806103 : Nat := 4983230072969 + 3 ^ 40 * 1806103 * 2
def baseEnd_1806103 : Nat := 206088655672767188312531

theorem tailTrace_1806103 : CollatzResearch.WordTrace tailWord_1806103 prefixEnd_1806103 206088655672767188312531 := by
  unfold tailWord_1806103
  simp only [CollatzResearch.WordTrace]
  refine ⟨65873988175804763679926963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43915992117203175786617975 65873988175804763679926963)
  ·
    refine ⟨98810982263707145519890445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65873988175804763679926963 98810982263707145519890445)
    ·
      refine ⟨37054118348890179569958917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98810982263707145519890445 37054118348890179569958917)
      ·
        refine ⟨6947647190416908669367297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37054118348890179569958917 6947647190416908669367297)
        ·
          refine ⟨5210735392812681502025473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6947647190416908669367297 5210735392812681502025473)
          ·
            refine ⟨3908051544609511126519105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5210735392812681502025473 3908051544609511126519105)
            ·
              refine ⟨2931038658457133344889329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3908051544609511126519105 2931038658457133344889329)
              ·
                refine ⟨2198278993842850008666997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2931038658457133344889329 2198278993842850008666997)
                ·
                  refine ⟨206088655672767188312531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2198278993842850008666997 206088655672767188312531)
                  ·
                    rfl

theorem cell22_1806103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 2, 2, 5].length) (baseStart_1806103 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1806103 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1806103 prefixEnd_1806103 := by exact prefixLift 1806103
  have htrace : WordTrace (prefixWord ++ tailWord_1806103) baseStart_1806103 baseEnd_1806103 := by
    simpa [prefixWord, tailWord_1806103, baseEnd_1806103] using wordTrace_append hprefix tailTrace_1806103
  have hstable : (prefixWord ++ tailWord_1806103).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1806103).length < 2 ^ (prefixWord ++ tailWord_1806103).sum := by decide
  have hdescent : baseEnd_1806103 < baseStart_1806103 := by decide
  rcases family_descends (prefixWord ++ tailWord_1806103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1806178 : List Nat := [3, 3, 2, 1, 2, 1, 1, 2, 1, 6]
def baseStart_1806178 : Nat := 118140960795 + 1806178 * 2 ^ 59
def prefixEnd_1806178 : Nat := 4983230072969 + 3 ^ 40 * 1806178 * 2
def baseEnd_1806178 : Nat := 618291641051026369312363

theorem tailTrace_1806178 : CollatzResearch.WordTrace tailWord_1806178 prefixEnd_1806178 618291641051026369312363 := by
  unfold tailWord_1806178
  simp only [CollatzResearch.WordTrace]
  refine ⟨16469180912633262872226797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43917815767022034325938125 16469180912633262872226797)
  ·
    refine ⟨6175942842237473577085049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16469180912633262872226797 6175942842237473577085049)
    ·
      refine ⟨4631957131678105182813787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6175942842237473577085049 4631957131678105182813787)
      ·
        refine ⟨6947935697517157774220681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4631957131678105182813787 6947935697517157774220681)
        ·
          refine ⟨5210951773137868330665511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6947935697517157774220681 5210951773137868330665511)
          ·
            refine ⟨7816427659706802495998267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5210951773137868330665511 7816427659706802495998267)
            ·
              refine ⟨11724641489560203743997401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7816427659706802495998267 11724641489560203743997401)
              ·
                refine ⟨8793481117170152807998051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11724641489560203743997401 8793481117170152807998051)
                ·
                  refine ⟨13190221675755229211997077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8793481117170152807998051 13190221675755229211997077)
                  ·
                    refine ⟨618291641051026369312363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13190221675755229211997077 618291641051026369312363)
                    ·
                      rfl

theorem cell22_1806178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 2, 1, 6].length) (baseStart_1806178 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1806178 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1806178 prefixEnd_1806178 := by exact prefixLift 1806178
  have htrace : WordTrace (prefixWord ++ tailWord_1806178) baseStart_1806178 baseEnd_1806178 := by
    simpa [prefixWord, tailWord_1806178, baseEnd_1806178] using wordTrace_append hprefix tailTrace_1806178
  have hstable : (prefixWord ++ tailWord_1806178).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1806178).length < 2 ^ (prefixWord ++ tailWord_1806178).sum := by decide
  have hdescent : baseEnd_1806178 < baseStart_1806178 := by decide
  rcases family_descends (prefixWord ++ tailWord_1806178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1806180 : List Nat := [2, 3, 1, 1, 5, 2, 1, 1, 1, 5]
def baseStart_1806180 : Nat := 118140960795 + 1806180 * 2 ^ 59
def prefixEnd_1806180 : Nat := 4983230072969 + 3 ^ 40 * 1806180 * 2
def baseEnd_1806180 : Nat := 618292325691899030762357

theorem tailTrace_1806180 : CollatzResearch.WordTrace tailWord_1806180 prefixEnd_1806180 618292325691899030762357 := by
  unfold tailWord_1806180
  simp only [CollatzResearch.WordTrace]
  refine ⟨32938398298262902915239997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43917864397683870553653329 32938398298262902915239997)
  ·
    refine ⟨12351899361848588593214999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32938398298262902915239997 12351899361848588593214999)
    ·
      refine ⟨18527849042772882889822499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12351899361848588593214999 18527849042772882889822499)
      ·
        refine ⟨27791773564159324334733749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18527849042772882889822499 27791773564159324334733749)
        ·
          refine ⟨2605478771639936656381289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 27791773564159324334733749 2605478771639936656381289)
          ·
            refine ⟨1954109078729952492285967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2605478771639936656381289 1954109078729952492285967)
            ·
              refine ⟨2931163618094928738428951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1954109078729952492285967 2931163618094928738428951)
              ·
                refine ⟨4396745427142393107643427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2931163618094928738428951 4396745427142393107643427)
                ·
                  refine ⟨6595118140713589661465141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4396745427142393107643427 6595118140713589661465141)
                  ·
                    refine ⟨618292325691899030762357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6595118140713589661465141 618292325691899030762357)
                    ·
                      rfl

theorem cell22_1806180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 2, 1, 1, 1, 5].length) (baseStart_1806180 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1806180 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1806180 prefixEnd_1806180 := by exact prefixLift 1806180
  have htrace : WordTrace (prefixWord ++ tailWord_1806180) baseStart_1806180 baseEnd_1806180 := by
    simpa [prefixWord, tailWord_1806180, baseEnd_1806180] using wordTrace_append hprefix tailTrace_1806180
  have hstable : (prefixWord ++ tailWord_1806180).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1806180).length < 2 ^ (prefixWord ++ tailWord_1806180).sum := by decide
  have hdescent : baseEnd_1806180 < baseStart_1806180 := by decide
  rcases family_descends (prefixWord ++ tailWord_1806180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1806225 : List Nat := [1, 2, 2, 1, 1, 1, 4, 6, 1, 3]
def baseStart_1806225 : Nat := 118140960795 + 1806225 * 2 ^ 59
def prefixEnd_1806225 : Nat := 4983230072969 + 3 ^ 40 * 1806225 * 2
def baseEnd_1806225 : Nat := 618307730111533913387219

theorem tailTrace_1806225 : CollatzResearch.WordTrace tailWord_1806225 prefixEnd_1806225 618307730111533913387219 := by
  unfold tailWord_1806225
  simp only [CollatzResearch.WordTrace]
  refine ⟨65878437881362778515868129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43918958587575185677245419 65878437881362778515868129)
  ·
    refine ⟨49408828411022083886901097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65878437881362778515868129 49408828411022083886901097)
    ·
      refine ⟨37056621308266562915175823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49408828411022083886901097 37056621308266562915175823)
      ·
        refine ⟨55584931962399844372763735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37056621308266562915175823 55584931962399844372763735)
        ·
          refine ⟨83377397943599766559145603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55584931962399844372763735 83377397943599766559145603)
          ·
            refine ⟨125066096915399649838718405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83377397943599766559145603 125066096915399649838718405)
            ·
              refine ⟨23449893171637434344759701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 125066096915399649838718405 23449893171637434344759701)
              ·
                refine ⟨1099213742420504734910611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 23449893171637434344759701 1099213742420504734910611)
                ·
                  refine ⟨1648820613630757102365917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1099213742420504734910611 1648820613630757102365917)
                  ·
                    refine ⟨618307730111533913387219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1648820613630757102365917 618307730111533913387219)
                    ·
                      rfl

theorem cell22_1806225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 6, 1, 3].length) (baseStart_1806225 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1806225 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1806225 prefixEnd_1806225 := by exact prefixLift 1806225
  have htrace : WordTrace (prefixWord ++ tailWord_1806225) baseStart_1806225 baseEnd_1806225 := by
    simpa [prefixWord, tailWord_1806225, baseEnd_1806225] using wordTrace_append hprefix tailTrace_1806225
  have hstable : (prefixWord ++ tailWord_1806225).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1806225).length < 2 ^ (prefixWord ++ tailWord_1806225).sum := by decide
  have hdescent : baseEnd_1806225 < baseStart_1806225 := by decide
  rcases family_descends (prefixWord ++ tailWord_1806225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1806266 : List Nat := [3, 1, 1, 1, 2, 1, 2, 1, 10]
def baseStart_1806266 : Nat := 118140960795 + 1806266 * 2 ^ 59
def prefixEnd_1806266 : Nat := 4983230072969 + 3 ^ 40 * 1806266 * 2
def baseEnd_1806266 : Nat := 206107255083141157704031

theorem tailTrace_1806266 : CollatzResearch.WordTrace tailWord_1806266 prefixEnd_1806266 206107255083141157704031 := by
  unfold tailWord_1806266
  simp only [CollatzResearch.WordTrace]
  refine ⟨16469983318553560629527663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43919955516142828345407101 16469983318553560629527663)
  ·
    refine ⟨24704974977830340944291495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16469983318553560629527663 24704974977830340944291495)
    ·
      refine ⟨37057462466745511416437243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24704974977830340944291495 37057462466745511416437243)
      ·
        refine ⟨55586193700118267124655865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37057462466745511416437243 55586193700118267124655865)
        ·
          refine ⟨41689645275088700343491899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55586193700118267124655865 41689645275088700343491899)
          ·
            refine ⟨62534467912633050515237849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41689645275088700343491899 62534467912633050515237849)
            ·
              refine ⟨46900850934474787886428387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62534467912633050515237849 46900850934474787886428387)
              ·
                refine ⟨70351276401712181829642581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46900850934474787886428387 70351276401712181829642581)
                ·
                  refine ⟨206107255083141157704031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 70351276401712181829642581 206107255083141157704031)
                  ·
                    rfl

theorem cell22_1806266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 1, 10].length) (baseStart_1806266 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1806266 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1806266 prefixEnd_1806266 := by exact prefixLift 1806266
  have htrace : WordTrace (prefixWord ++ tailWord_1806266) baseStart_1806266 baseEnd_1806266 := by
    simpa [prefixWord, tailWord_1806266, baseEnd_1806266] using wordTrace_append hprefix tailTrace_1806266
  have hstable : (prefixWord ++ tailWord_1806266).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1806266).length < 2 ^ (prefixWord ++ tailWord_1806266).sum := by decide
  have hdescent : baseEnd_1806266 < baseStart_1806266 := by decide
  rcases family_descends (prefixWord ++ tailWord_1806266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1806360 : List Nat := [2, 1, 2, 3, 2, 1, 1, 4, 3, 3]
def baseStart_1806360 : Nat := 118140960795 + 1806360 * 2 ^ 59
def prefixEnd_1806360 : Nat := 4983230072969 + 3 ^ 40 * 1806360 * 2
def baseEnd_1806360 : Nat := 618353943370438561261805

theorem tailTrace_1806360 : CollatzResearch.WordTrace tailWord_1806360 prefixEnd_1806360 618353943370438561261805 := by
  unfold tailWord_1806360
  simp only [CollatzResearch.WordTrace]
  refine ⟨32941680867936848286016267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43922241157249131048021689 32941680867936848286016267)
  ·
    refine ⟨49412521301905272429024401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32941680867936848286016267 49412521301905272429024401)
    ·
      refine ⟨37059390976428954321768301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49412521301905272429024401 37059390976428954321768301)
      ·
        refine ⟨13897271616160857870663113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37059390976428954321768301 13897271616160857870663113)
        ·
          refine ⟨10422953712120643402997335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13897271616160857870663113 10422953712120643402997335)
          ·
            refine ⟨15634430568180965104496003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10422953712120643402997335 15634430568180965104496003)
            ·
              refine ⟨23451645852271447656744005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15634430568180965104496003 23451645852271447656744005)
              ·
                refine ⟨4397183597300896435639501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23451645852271447656744005 4397183597300896435639501)
                ·
                  refine ⟨1648943848987836163364813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4397183597300896435639501 1648943848987836163364813)
                  ·
                    refine ⟨618353943370438561261805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1648943848987836163364813 618353943370438561261805)
                    ·
                      rfl

theorem cell22_1806360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 4, 3, 3].length) (baseStart_1806360 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1806360 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1806360 prefixEnd_1806360 := by exact prefixLift 1806360
  have htrace : WordTrace (prefixWord ++ tailWord_1806360) baseStart_1806360 baseEnd_1806360 := by
    simpa [prefixWord, tailWord_1806360, baseEnd_1806360] using wordTrace_append hprefix tailTrace_1806360
  have hstable : (prefixWord ++ tailWord_1806360).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1806360).length < 2 ^ (prefixWord ++ tailWord_1806360).sum := by decide
  have hdescent : baseEnd_1806360 < baseStart_1806360 := by decide
  rcases family_descends (prefixWord ++ tailWord_1806360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1806373 : List Nat := [1, 3, 1, 2, 2, 3, 1, 2, 7]
def baseStart_1806373 : Nat := 118140960795 + 1806373 * 2 ^ 59
def prefixEnd_1806373 : Nat := 4983230072969 + 3 ^ 40 * 1806373 * 2
def baseEnd_1806373 : Nat := 206119464512036953562255

theorem tailTrace_1806373 : CollatzResearch.WordTrace tailWord_1806373 prefixEnd_1806373 206119464512036953562255 := by
  unfold tailWord_1806373
  simp only [CollatzResearch.WordTrace]
  refine ⟨65883835884826599792255773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43922557256551066528170515 65883835884826599792255773)
  ·
    refine ⟨24706438456809974922095915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65883835884826599792255773 24706438456809974922095915)
    ·
      refine ⟨37059657685214962383143873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24706438456809974922095915 37059657685214962383143873)
      ·
        refine ⟨27794743263911221787357905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37059657685214962383143873 27794743263911221787357905)
        ·
          refine ⟨20846057447933416340518429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27794743263911221787357905 20846057447933416340518429)
          ·
            refine ⟨7817271542975031127694411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20846057447933416340518429 7817271542975031127694411)
            ·
              refine ⟨11725907314462546691541617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7817271542975031127694411 11725907314462546691541617)
              ·
                refine ⟨8794430485846910018656213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11725907314462546691541617 8794430485846910018656213)
                ·
                  refine ⟨206119464512036953562255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8794430485846910018656213 206119464512036953562255)
                  ·
                    rfl

theorem cell22_1806373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 2, 7].length) (baseStart_1806373 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1806373 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1806373 prefixEnd_1806373 := by exact prefixLift 1806373
  have htrace : WordTrace (prefixWord ++ tailWord_1806373) baseStart_1806373 baseEnd_1806373 := by
    simpa [prefixWord, tailWord_1806373, baseEnd_1806373] using wordTrace_append hprefix tailTrace_1806373
  have hstable : (prefixWord ++ tailWord_1806373).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1806373).length < 2 ^ (prefixWord ++ tailWord_1806373).sum := by decide
  have hdescent : baseEnd_1806373 < baseStart_1806373 := by decide
  rcases family_descends (prefixWord ++ tailWord_1806373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1806390 : List Nat := [5, 1, 2, 1, 1, 1, 1, 3, 7]
def baseStart_1806390 : Nat := 118140960795 + 1806390 * 2 ^ 59
def prefixEnd_1806390 : Nat := 4983230072969 + 3 ^ 40 * 1806390 * 2
def baseEnd_1806390 : Nat := 206121404327842827670571

theorem tailTrace_1806390 : CollatzResearch.WordTrace tailWord_1806390 prefixEnd_1806390 206121404327842827670571 := by
  unfold tailWord_1806390
  simp only [CollatzResearch.WordTrace]
  refine ⟨4117778495360313230976539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 43922970617176674463749749 4117778495360313230976539)
  ·
    refine ⟨6176667743040469846464809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4117778495360313230976539 6176667743040469846464809)
    ·
      refine ⟨4632500807280352384848607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6176667743040469846464809 4632500807280352384848607)
      ·
        refine ⟨6948751210920528577272911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4632500807280352384848607 6948751210920528577272911)
        ·
          refine ⟨10423126816380792865909367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6948751210920528577272911 10423126816380792865909367)
          ·
            refine ⟨15634690224571189298864051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10423126816380792865909367 15634690224571189298864051)
            ·
              refine ⟨23452035336856783948296077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15634690224571189298864051 23452035336856783948296077)
              ·
                refine ⟨8794513251321293980611029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23452035336856783948296077 8794513251321293980611029)
                ·
                  refine ⟨206121404327842827670571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8794513251321293980611029 206121404327842827670571)
                  ·
                    rfl

theorem cell22_1806390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 3, 7].length) (baseStart_1806390 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1806390 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1806390 prefixEnd_1806390 := by exact prefixLift 1806390
  have htrace : WordTrace (prefixWord ++ tailWord_1806390) baseStart_1806390 baseEnd_1806390 := by
    simpa [prefixWord, tailWord_1806390, baseEnd_1806390] using wordTrace_append hprefix tailTrace_1806390
  have hstable : (prefixWord ++ tailWord_1806390).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1806390).length < 2 ^ (prefixWord ++ tailWord_1806390).sum := by decide
  have hdescent : baseEnd_1806390 < baseStart_1806390 := by decide
  rcases family_descends (prefixWord ++ tailWord_1806390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1806467 : List Nat := [1, 1, 1, 3, 3, 3, 2, 3, 2, 3]
def baseStart_1806467 : Nat := 118140960795 + 1806467 * 2 ^ 59
def prefixEnd_1806467 : Nat := 4983230072969 + 3 ^ 40 * 1806467 * 2
def baseEnd_1806467 : Nat := 618390571657125948836477

theorem tailTrace_1806467 : CollatzResearch.WordTrace tailWord_1806467 prefixEnd_1806467 618390571657125948836477 := by
  unfold tailWord_1806467
  simp only [CollatzResearch.WordTrace]
  refine ⟨65887264346486053846177655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43924842897657369230785103 65887264346486053846177655)
  ·
    refine ⟨98830896519729080769266483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65887264346486053846177655 98830896519729080769266483)
    ·
      refine ⟨148246344779593621153899725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98830896519729080769266483 148246344779593621153899725)
      ·
        refine ⟨55592379292347607932712397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 148246344779593621153899725 55592379292347607932712397)
        ·
          refine ⟨20847142234630352974767149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55592379292347607932712397 20847142234630352974767149)
          ·
            refine ⟨7817678337986382365537681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20847142234630352974767149 7817678337986382365537681)
            ·
              refine ⟨5863258753489786774153261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7817678337986382365537681 5863258753489786774153261)
              ·
                refine ⟨2198722032558670040307473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5863258753489786774153261 2198722032558670040307473)
                ·
                  refine ⟨1649041524419002530230605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2198722032558670040307473 1649041524419002530230605)
                  ·
                    refine ⟨618390571657125948836477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1649041524419002530230605 618390571657125948836477)
                    ·
                      rfl

theorem cell22_1806467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 2, 3, 2, 3].length) (baseStart_1806467 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1806467 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1806467 prefixEnd_1806467 := by exact prefixLift 1806467
  have htrace : WordTrace (prefixWord ++ tailWord_1806467) baseStart_1806467 baseEnd_1806467 := by
    simpa [prefixWord, tailWord_1806467, baseEnd_1806467] using wordTrace_append hprefix tailTrace_1806467
  have hstable : (prefixWord ++ tailWord_1806467).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1806467).length < 2 ^ (prefixWord ++ tailWord_1806467).sum := by decide
  have hdescent : baseEnd_1806467 < baseStart_1806467 := by decide
  rcases family_descends (prefixWord ++ tailWord_1806467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1806480 : List Nat := [2, 1, 1, 1, 1, 1, 9, 6]
def baseStart_1806480 : Nat := 118140960795 + 1806480 * 2 ^ 59
def prefixEnd_1806480 : Nat := 4983230072969 + 3 ^ 40 * 1806480 * 2
def baseEnd_1806480 : Nat := 68710557980310916473493

theorem tailTrace_1806480 : CollatzResearch.WordTrace tailWord_1806480 prefixEnd_1806480 68710557980310916473493 := by
  unfold tailWord_1806480
  simp only [CollatzResearch.WordTrace]
  refine ⟨32943869247719478533200447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43925158996959304710933929 32943869247719478533200447)
  ·
    refine ⟨49415803871579217799800671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32943869247719478533200447 49415803871579217799800671)
    ·
      refine ⟨74123705807368826699701007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49415803871579217799800671 74123705807368826699701007)
      ·
        refine ⟨111185558711053240049551511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74123705807368826699701007 111185558711053240049551511)
        ·
          refine ⟨166778338066579860074327267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111185558711053240049551511 166778338066579860074327267)
          ·
            refine ⟨250167507099869790111490901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166778338066579860074327267 250167507099869790111490901)
            ·
              refine ⟨1465825236913299551434517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 250167507099869790111490901 1465825236913299551434517)
              ·
                refine ⟨68710557980310916473493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1465825236913299551434517 68710557980310916473493)
                ·
                  rfl

theorem cell22_1806480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 9, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 9, 6].length) (baseStart_1806480 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1806480 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1806480 prefixEnd_1806480 := by exact prefixLift 1806480
  have htrace : WordTrace (prefixWord ++ tailWord_1806480) baseStart_1806480 baseEnd_1806480 := by
    simpa [prefixWord, tailWord_1806480, baseEnd_1806480] using wordTrace_append hprefix tailTrace_1806480
  have hstable : (prefixWord ++ tailWord_1806480).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1806480).length < 2 ^ (prefixWord ++ tailWord_1806480).sum := by decide
  have hdescent : baseEnd_1806480 < baseStart_1806480 := by decide
  rcases family_descends (prefixWord ++ tailWord_1806480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1806546 : List Nat := [3, 2, 2, 2, 1, 2, 3, 3, 1, 3]
def baseStart_1806546 : Nat := 118140960795 + 1806546 * 2 ^ 59
def prefixEnd_1806546 : Nat := 4983230072969 + 3 ^ 40 * 1806546 * 2
def baseEnd_1806546 : Nat := 618417614971596076111235

theorem tailTrace_1806546 : CollatzResearch.WordTrace tailWord_1806546 prefixEnd_1806546 618417614971596076111235 := by
  unfold tailWord_1806546
  simp only [CollatzResearch.WordTrace]
  refine ⟨16472536428299962584575873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43926763808799900225535661 16472536428299962584575873)
  ·
    refine ⟨12354402321224971938431905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16472536428299962584575873 12354402321224971938431905)
    ·
      refine ⟨9265801740918728953823929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12354402321224971938431905 9265801740918728953823929)
      ·
        refine ⟨6949351305689046715367947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9265801740918728953823929 6949351305689046715367947)
        ·
          refine ⟨10424026958533570073051921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6949351305689046715367947 10424026958533570073051921)
          ·
            refine ⟨7818020218900177554788941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10424026958533570073051921 7818020218900177554788941)
            ·
              refine ⟨2931757582087566583045853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7818020218900177554788941 2931757582087566583045853)
              ·
                refine ⟨1099409093282837468642195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2931757582087566583045853 1099409093282837468642195)
                ·
                  refine ⟨1649113639924256202963293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1099409093282837468642195 1649113639924256202963293)
                  ·
                    refine ⟨618417614971596076111235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1649113639924256202963293 618417614971596076111235)
                    ·
                      rfl

theorem cell22_1806546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 3, 3, 1, 3].length) (baseStart_1806546 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1806546 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1806546 prefixEnd_1806546 := by exact prefixLift 1806546
  have htrace : WordTrace (prefixWord ++ tailWord_1806546) baseStart_1806546 baseEnd_1806546 := by
    simpa [prefixWord, tailWord_1806546, baseEnd_1806546] using wordTrace_append hprefix tailTrace_1806546
  have hstable : (prefixWord ++ tailWord_1806546).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1806546).length < 2 ^ (prefixWord ++ tailWord_1806546).sum := by decide
  have hdescent : baseEnd_1806546 < baseStart_1806546 := by decide
  rcases family_descends (prefixWord ++ tailWord_1806546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1806563 : List Nat := [1, 1, 1, 8, 2, 1, 1, 1, 3, 3]
def baseStart_1806563 : Nat := 118140960795 + 1806563 * 2 ^ 59
def prefixEnd_1806563 : Nat := 4983230072969 + 3 ^ 40 * 1806563 * 2
def baseEnd_1806563 : Nat := 618423434419013698436183

theorem tailTrace_1806563 : CollatzResearch.WordTrace tailWord_1806563 prefixEnd_1806563 618423434419013698436183 := by
  unfold tailWord_1806563
  simp only [CollatzResearch.WordTrace]
  refine ⟨65890765754138262241672343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43927177169425508161114895 65890765754138262241672343)
  ·
    refine ⟨98836148631207393362508515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65890765754138262241672343 98836148631207393362508515)
    ·
      refine ⟨148254222946811090043762773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98836148631207393362508515 148254222946811090043762773)
      ·
        refine ⟨1737354175157942461450345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 148254222946811090043762773 1737354175157942461450345)
        ·
          refine ⟨1303015631368456846087759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1737354175157942461450345 1303015631368456846087759)
          ·
            refine ⟨1954523447052685269131639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1303015631368456846087759 1954523447052685269131639)
            ·
              refine ⟨2931785170579027903697459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1954523447052685269131639 2931785170579027903697459)
              ·
                refine ⟨4397677755868541855546189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2931785170579027903697459 4397677755868541855546189)
                ·
                  refine ⟨1649129158450703195829821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4397677755868541855546189 1649129158450703195829821)
                  ·
                    refine ⟨618423434419013698436183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1649129158450703195829821 618423434419013698436183)
                    ·
                      rfl

theorem cell22_1806563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 1, 1, 1, 3, 3].length) (baseStart_1806563 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1806563 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1806563 prefixEnd_1806563 := by exact prefixLift 1806563
  have htrace : WordTrace (prefixWord ++ tailWord_1806563) baseStart_1806563 baseEnd_1806563 := by
    simpa [prefixWord, tailWord_1806563, baseEnd_1806563] using wordTrace_append hprefix tailTrace_1806563
  have hstable : (prefixWord ++ tailWord_1806563).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1806563).length < 2 ^ (prefixWord ++ tailWord_1806563).sum := by decide
  have hdescent : baseEnd_1806563 < baseStart_1806563 := by decide
  rcases family_descends (prefixWord ++ tailWord_1806563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1806602 : List Nat := [3, 1, 2, 2, 1, 1, 2, 1, 6, 3]
def baseStart_1806602 : Nat := 118140960795 + 1806602 * 2 ^ 59
def prefixEnd_1806602 : Nat := 4983230072969 + 3 ^ 40 * 1806602 * 2
def baseEnd_1806602 : Nat := 618436784916030596711063

theorem tailTrace_1806602 : CollatzResearch.WordTrace tailWord_1806602 prefixEnd_1806602 618436784916030596711063 := by
  unfold tailWord_1806602
  simp only [CollatzResearch.WordTrace]
  refine ⟨16473047050249242975585515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43928125467331314601561373 16473047050249242975585515)
  ·
    refine ⟨24709570575373864463378273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16473047050249242975585515 24709570575373864463378273)
    ·
      refine ⟨18532177931530398347533705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24709570575373864463378273 18532177931530398347533705)
      ·
        refine ⟨13899133448647798760650279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18532177931530398347533705 13899133448647798760650279)
        ·
          refine ⟨20848700172971698140975419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13899133448647798760650279 20848700172971698140975419)
          ·
            refine ⟨31273050259457547211463129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20848700172971698140975419 31273050259457547211463129)
            ·
              refine ⟨23454787694593160408597347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31273050259457547211463129 23454787694593160408597347)
              ·
                refine ⟨35182181541889740612896021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23454787694593160408597347 35182181541889740612896021)
                ·
                  refine ⟨1649164759776081591229501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 35182181541889740612896021 1649164759776081591229501)
                  ·
                    refine ⟨618436784916030596711063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1649164759776081591229501 618436784916030596711063)
                    ·
                      rfl

theorem cell22_1806602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 1, 6, 3].length) (baseStart_1806602 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1806602 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1806602 prefixEnd_1806602 := by exact prefixLift 1806602
  have htrace : WordTrace (prefixWord ++ tailWord_1806602) baseStart_1806602 baseEnd_1806602 := by
    simpa [prefixWord, tailWord_1806602, baseEnd_1806602] using wordTrace_append hprefix tailTrace_1806602
  have hstable : (prefixWord ++ tailWord_1806602).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1806602).length < 2 ^ (prefixWord ++ tailWord_1806602).sum := by decide
  have hdescent : baseEnd_1806602 < baseStart_1806602 := by decide
  rcases family_descends (prefixWord ++ tailWord_1806602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1806615 : List Nat := [1, 1, 3, 4, 1, 12]
def baseStart_1806615 : Nat := 118140960795 + 1806615 * 2 ^ 59
def prefixEnd_1806615 : Nat := 4983230072969 + 3 ^ 40 * 1806615 * 2
def baseEnd_1806615 : Nat := 7635076976317319705383

theorem tailTrace_1806615 : CollatzResearch.WordTrace tailWord_1806615 prefixEnd_1806615 7635076976317319705383 := by
  unfold tailWord_1806615
  simp only [CollatzResearch.WordTrace]
  refine ⟨65892662349949875122565299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43928441566633250081710199 65892662349949875122565299)
  ·
    refine ⟨98838993524924812683847949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65892662349949875122565299 98838993524924812683847949)
    ·
      refine ⟨37064622571846804756442981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98838993524924812683847949 37064622571846804756442981)
      ·
        refine ⟨6949616732221275891833059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37064622571846804756442981 6949616732221275891833059)
        ·
          refine ⟨10424425098331913837749589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6949616732221275891833059 10424425098331913837749589)
          ·
            refine ⟨7635076976317319705383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 10424425098331913837749589 7635076976317319705383)
            ·
              rfl

theorem cell22_1806615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 12].length) (baseStart_1806615 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1806615 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1806615 prefixEnd_1806615 := by exact prefixLift 1806615
  have htrace : WordTrace (prefixWord ++ tailWord_1806615) baseStart_1806615 baseEnd_1806615 := by
    simpa [prefixWord, tailWord_1806615, baseEnd_1806615] using wordTrace_append hprefix tailTrace_1806615
  have hstable : (prefixWord ++ tailWord_1806615).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1806615).length < 2 ^ (prefixWord ++ tailWord_1806615).sum := by decide
  have hdescent : baseEnd_1806615 < baseStart_1806615 := by decide
  rcases family_descends (prefixWord ++ tailWord_1806615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1806621 : List Nat := [1, 4, 2, 3, 2, 1, 1, 4, 4]
def baseStart_1806621 : Nat := 118140960795 + 1806621 * 2 ^ 59
def prefixEnd_1806621 : Nat := 4983230072969 + 3 ^ 40 * 1806621 * 2
def baseEnd_1806621 : Nat := 206147763001440293495335

theorem tailTrace_1806621 : CollatzResearch.WordTrace tailWord_1806621 prefixEnd_1806621 206147763001440293495335 := by
  unfold tailWord_1806621
  simp only [CollatzResearch.WordTrace]
  refine ⟨65892881187928138147283717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43928587458618758764855811 65892881187928138147283717)
  ·
    refine ⟨12354915222736525902615697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65892881187928138147283717 12354915222736525902615697)
    ·
      refine ⟨9266186417052394426961773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12354915222736525902615697 9266186417052394426961773)
      ·
        refine ⟨3474819906394647910110665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9266186417052394426961773 3474819906394647910110665)
        ·
          refine ⟨2606114929795985932582999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3474819906394647910110665 2606114929795985932582999)
          ·
            refine ⟨3909172394693978898874499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2606114929795985932582999 3909172394693978898874499)
            ·
              refine ⟨5863758592040968348311749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3909172394693978898874499 5863758592040968348311749)
              ·
                refine ⟨1099454736007681565308453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5863758592040968348311749 1099454736007681565308453)
                ·
                  refine ⟨206147763001440293495335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1099454736007681565308453 206147763001440293495335)
                  ·
                    rfl

theorem cell22_1806621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 1, 4, 4].length) (baseStart_1806621 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1806621 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1806621 prefixEnd_1806621 := by exact prefixLift 1806621
  have htrace : WordTrace (prefixWord ++ tailWord_1806621) baseStart_1806621 baseEnd_1806621 := by
    simpa [prefixWord, tailWord_1806621, baseEnd_1806621] using wordTrace_append hprefix tailTrace_1806621
  have hstable : (prefixWord ++ tailWord_1806621).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1806621).length < 2 ^ (prefixWord ++ tailWord_1806621).sum := by decide
  have hdescent : baseEnd_1806621 < baseStart_1806621 := by decide
  rcases family_descends (prefixWord ++ tailWord_1806621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1806649 : List Nat := [1, 2, 1, 6, 1, 2, 3, 6]
def baseStart_1806649 : Nat := 118140960795 + 1806649 * 2 ^ 59
def prefixEnd_1806649 : Nat := 4983230072969 + 3 ^ 40 * 1806649 * 2
def baseEnd_1806649 : Nat := 68716985997393126753991

theorem tailTrace_1806649 : CollatzResearch.WordTrace tailWord_1806649 prefixEnd_1806649 68716985997393126753991 := by
  unfold tailWord_1806649
  simp only [CollatzResearch.WordTrace]
  refine ⟨65893902431826698929303001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43929268287884465952868667 65893902431826698929303001)
  ·
    refine ⟨49420426823870024196977251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65893902431826698929303001 49420426823870024196977251)
    ·
      refine ⟨74130640235805036295465877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49420426823870024196977251 74130640235805036295465877)
      ·
        refine ⟨3474873761053361076349963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 74130640235805036295465877 3474873761053361076349963)
        ·
          refine ⟨5212310641580041614524945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3474873761053361076349963 5212310641580041614524945)
          ·
            refine ⟨3909232981185031210893709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5212310641580041614524945 3909232981185031210893709)
            ·
              refine ⟨1465962367944386704085141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3909232981185031210893709 1465962367944386704085141)
              ·
                refine ⟨68716985997393126753991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1465962367944386704085141 68716985997393126753991)
                ·
                  rfl

theorem cell22_1806649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 3, 6].length) (baseStart_1806649 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1806649 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1806649 prefixEnd_1806649 := by exact prefixLift 1806649
  have htrace : WordTrace (prefixWord ++ tailWord_1806649) baseStart_1806649 baseEnd_1806649 := by
    simpa [prefixWord, tailWord_1806649, baseEnd_1806649] using wordTrace_append hprefix tailTrace_1806649
  have hstable : (prefixWord ++ tailWord_1806649).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1806649).length < 2 ^ (prefixWord ++ tailWord_1806649).sum := by decide
  have hdescent : baseEnd_1806649 < baseStart_1806649 := by decide
  rcases family_descends (prefixWord ++ tailWord_1806649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1806692 : List Nat := [2, 3, 1, 1, 3, 1, 1, 3, 2, 5]
def baseStart_1806692 : Nat := 118140960795 + 1806692 * 2 ^ 59
def prefixEnd_1806692 : Nat := 4983230072969 + 3 ^ 40 * 1806692 * 2
def baseEnd_1806692 : Nat := 618467593755300361960787

theorem tailTrace_1806692 : CollatzResearch.WordTrace tailWord_1806692 prefixEnd_1806692 618467593755300361960787 := by
  unfold tailWord_1806692
  simp only [CollatzResearch.WordTrace]
  refine ⟨32947735385335458636559165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43930313847113944848745553 32947735385335458636559165)
  ·
    refine ⟨12355400769500796988709687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32947735385335458636559165 12355400769500796988709687)
    ·
      refine ⟨18533101154251195483064531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12355400769500796988709687 18533101154251195483064531)
      ·
        refine ⟨27799651731376793224596797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18533101154251195483064531 27799651731376793224596797)
        ·
          refine ⟨10424869399266297459223799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27799651731376793224596797 10424869399266297459223799)
          ·
            refine ⟨15637304098899446188835699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10424869399266297459223799 15637304098899446188835699)
            ·
              refine ⟨23455956148349169283253549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15637304098899446188835699 23455956148349169283253549)
              ·
                refine ⟨8795983555630938481220081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23455956148349169283253549 8795983555630938481220081)
                ·
                  refine ⟨6596987666723203860915061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8795983555630938481220081 6596987666723203860915061)
                  ·
                    refine ⟨618467593755300361960787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6596987666723203860915061 618467593755300361960787)
                    ·
                      rfl

theorem cell22_1806692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 3, 2, 5].length) (baseStart_1806692 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1806692 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1806692 prefixEnd_1806692 := by exact prefixLift 1806692
  have htrace : WordTrace (prefixWord ++ tailWord_1806692) baseStart_1806692 baseEnd_1806692 := by
    simpa [prefixWord, tailWord_1806692, baseEnd_1806692] using wordTrace_append hprefix tailTrace_1806692
  have hstable : (prefixWord ++ tailWord_1806692).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1806692).length < 2 ^ (prefixWord ++ tailWord_1806692).sum := by decide
  have hdescent : baseEnd_1806692 < baseStart_1806692 := by decide
  rcases family_descends (prefixWord ++ tailWord_1806692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1806724 : List Nat := [2, 3, 2, 1, 1, 2, 1, 5, 1, 4]
def baseStart_1806724 : Nat := 118140960795 + 1806724 * 2 ^ 59
def prefixEnd_1806724 : Nat := 4983230072969 + 3 ^ 40 * 1806724 * 2
def baseEnd_1806724 : Nat := 618478548009262945160689

theorem tailTrace_1806724 : CollatzResearch.WordTrace tailWord_1806724 prefixEnd_1806724 618478548009262945160689 := by
  unfold tailWord_1806724
  simp only [CollatzResearch.WordTrace]
  refine ⟨32948318953277493369141613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43931091937703324492188817 32948318953277493369141613)
  ·
    refine ⟨12355619607479060013428105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32948318953277493369141613 12355619607479060013428105)
    ·
      refine ⟨9266714705609295010071079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12355619607479060013428105 9266714705609295010071079)
      ·
        refine ⟨13900072058413942515106619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9266714705609295010071079 13900072058413942515106619)
        ·
          refine ⟨20850108087620913772659929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13900072058413942515106619 20850108087620913772659929)
          ·
            refine ⟨15637581065715685329494947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20850108087620913772659929 15637581065715685329494947)
            ·
              refine ⟨23456371598573527994242421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15637581065715685329494947 23456371598573527994242421)
              ·
                refine ⟨2199034837366268249460227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23456371598573527994242421 2199034837366268249460227)
                ·
                  refine ⟨3298552256049402374190341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2199034837366268249460227 3298552256049402374190341)
                  ·
                    refine ⟨618478548009262945160689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3298552256049402374190341 618478548009262945160689)
                    ·
                      rfl

theorem cell22_1806724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 5, 1, 4].length) (baseStart_1806724 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1806724 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1806724 prefixEnd_1806724 := by exact prefixLift 1806724
  have htrace : WordTrace (prefixWord ++ tailWord_1806724) baseStart_1806724 baseEnd_1806724 := by
    simpa [prefixWord, tailWord_1806724, baseEnd_1806724] using wordTrace_append hprefix tailTrace_1806724
  have hstable : (prefixWord ++ tailWord_1806724).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1806724).length < 2 ^ (prefixWord ++ tailWord_1806724).sum := by decide
  have hdescent : baseEnd_1806724 < baseStart_1806724 := by decide
  rcases family_descends (prefixWord ++ tailWord_1806724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1806754 : List Nat := [3, 3, 1, 2, 1, 1, 2, 3, 1, 5]
def baseStart_1806754 : Nat := 118140960795 + 1806754 * 2 ^ 59
def prefixEnd_1806754 : Nat := 4983230072969 + 3 ^ 40 * 1806754 * 2
def baseEnd_1806754 : Nat := 618488817622352866910597

theorem tailTrace_1806754 : CollatzResearch.WordTrace tailWord_1806754 prefixEnd_1806754 618488817622352866910597 := by
  unfold tailWord_1806754
  simp only [CollatzResearch.WordTrace]
  refine ⟨16474433024111575465468829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43931821397630867907916877 16474433024111575465468829)
  ·
    refine ⟨6177912384041840799550811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16474433024111575465468829 6177912384041840799550811)
    ·
      refine ⟨9266868576062761199326217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6177912384041840799550811 9266868576062761199326217)
      ·
        refine ⟨6950151432047070899494663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9266868576062761199326217 6950151432047070899494663)
        ·
          refine ⟨10425227148070606349241995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6950151432047070899494663 10425227148070606349241995)
          ·
            refine ⟨15637840722105909523862993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10425227148070606349241995 15637840722105909523862993)
            ·
              refine ⟨11728380541579432142897245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15637840722105909523862993 11728380541579432142897245)
              ·
                refine ⟨4398142703092287053586467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11728380541579432142897245 4398142703092287053586467)
                ·
                  refine ⟨6597214054638430580379701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4398142703092287053586467 6597214054638430580379701)
                  ·
                    refine ⟨618488817622352866910597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6597214054638430580379701 618488817622352866910597)
                    ·
                      rfl

theorem cell22_1806754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 3, 1, 5].length) (baseStart_1806754 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1806754 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1806754 prefixEnd_1806754 := by exact prefixLift 1806754
  have htrace : WordTrace (prefixWord ++ tailWord_1806754) baseStart_1806754 baseEnd_1806754 := by
    simpa [prefixWord, tailWord_1806754, baseEnd_1806754] using wordTrace_append hprefix tailTrace_1806754
  have hstable : (prefixWord ++ tailWord_1806754).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1806754).length < 2 ^ (prefixWord ++ tailWord_1806754).sum := by decide
  have hdescent : baseEnd_1806754 < baseStart_1806754 := by decide
  rcases family_descends (prefixWord ++ tailWord_1806754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1806769 : List Nat := [1, 2, 2, 4, 1, 2, 1, 3, 2, 4]
def baseStart_1806769 : Nat := 118140960795 + 1806769 * 2 ^ 59
def prefixEnd_1806769 : Nat := 4983230072969 + 3 ^ 40 * 1806769 * 2
def baseEnd_1806769 : Nat := 618493952428897827785551

theorem tailTrace_1806769 : CollatzResearch.WordTrace tailWord_1806769 prefixEnd_1806769 618493952428897827785551 := by
  unfold tailWord_1806769
  simp only [CollatzResearch.WordTrace]
  refine ⟨65898279191391959423671361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43932186127594639615780907 65898279191391959423671361)
  ·
    refine ⟨49423709393543969567753521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65898279191391959423671361 49423709393543969567753521)
    ·
      refine ⟨37067782045157977175815141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49423709393543969567753521 37067782045157977175815141)
      ·
        refine ⟨6950209133467120720465339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37067782045157977175815141 6950209133467120720465339)
        ·
          refine ⟨10425313700200681080698009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6950209133467120720465339 10425313700200681080698009)
          ·
            refine ⟨7818985275150510810523507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10425313700200681080698009 7818985275150510810523507)
            ·
              refine ⟨11728477912725766215785261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7818985275150510810523507 11728477912725766215785261)
              ·
                refine ⟨4398179217272162330919473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11728477912725766215785261 4398179217272162330919473)
                ·
                  refine ⟨3298634412954121748189605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4398179217272162330919473 3298634412954121748189605)
                  ·
                    refine ⟨618493952428897827785551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3298634412954121748189605 618493952428897827785551)
                    ·
                      rfl

theorem cell22_1806769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 3, 2, 4].length) (baseStart_1806769 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1806769 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1806769 prefixEnd_1806769 := by exact prefixLift 1806769
  have htrace : WordTrace (prefixWord ++ tailWord_1806769) baseStart_1806769 baseEnd_1806769 := by
    simpa [prefixWord, tailWord_1806769, baseEnd_1806769] using wordTrace_append hprefix tailTrace_1806769
  have hstable : (prefixWord ++ tailWord_1806769).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1806769).length < 2 ^ (prefixWord ++ tailWord_1806769).sum := by decide
  have hdescent : baseEnd_1806769 < baseStart_1806769 := by decide
  rcases family_descends (prefixWord ++ tailWord_1806769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1806799 : List Nat := [1, 1, 2, 1, 1, 4, 1, 5, 3, 3]
def baseStart_1806799 : Nat := 118140960795 + 1806799 * 2 ^ 59
def prefixEnd_1806799 : Nat := 4983230072969 + 3 ^ 40 * 1806799 * 2
def baseEnd_1806799 : Nat := 618504222041987749535459

theorem tailTrace_1806799 : CollatzResearch.WordTrace tailWord_1806799 prefixEnd_1806799 618504222041987749535459 := by
  unfold tailWord_1806799
  simp only [CollatzResearch.WordTrace]
  refine ⟨65899373381283274547263451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43932915587522183031508967 65899373381283274547263451)
  ·
    refine ⟨98849060071924911820895177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65899373381283274547263451 98849060071924911820895177)
    ·
      refine ⟨74136795053943683865671383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98849060071924911820895177 74136795053943683865671383)
      ·
        refine ⟨111205192580915525798507075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74136795053943683865671383 111205192580915525798507075)
        ·
          refine ⟨166807788871373288697760613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111205192580915525798507075 166807788871373288697760613)
          ·
            refine ⟨31276460413382491630830115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 166807788871373288697760613 31276460413382491630830115)
            ·
              refine ⟨46914690620073737446245173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31276460413382491630830115 46914690620073737446245173)
              ·
                refine ⟨4398252245631912885585485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46914690620073737446245173 4398252245631912885585485)
                ·
                  refine ⟨1649344592111967332094557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4398252245631912885585485 1649344592111967332094557)
                  ·
                    refine ⟨618504222041987749535459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1649344592111967332094557 618504222041987749535459)
                    ·
                      rfl

theorem cell22_1806799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 5, 3, 3].length) (baseStart_1806799 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1806799 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1806799 prefixEnd_1806799 := by exact prefixLift 1806799
  have htrace : WordTrace (prefixWord ++ tailWord_1806799) baseStart_1806799 baseEnd_1806799 := by
    simpa [prefixWord, tailWord_1806799, baseEnd_1806799] using wordTrace_append hprefix tailTrace_1806799
  have hstable : (prefixWord ++ tailWord_1806799).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1806799).length < 2 ^ (prefixWord ++ tailWord_1806799).sum := by decide
  have hdescent : baseEnd_1806799 < baseStart_1806799 := by decide
  rcases family_descends (prefixWord ++ tailWord_1806799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1806827 : List Nat := [1, 1, 1, 1, 2, 3, 3, 2, 1, 7]
def baseStart_1806827 : Nat := 118140960795 + 1806827 * 2 ^ 59
def prefixEnd_1806827 : Nat := 4983230072969 + 3 ^ 40 * 1806827 * 2
def baseEnd_1806827 : Nat := 618513807014205009835373

theorem tailTrace_1806827 : CollatzResearch.WordTrace tailWord_1806827 prefixEnd_1806827 618513807014205009835373 := by
  unfold tailWord_1806827
  simp only [CollatzResearch.WordTrace]
  refine ⟨65900394625181835329282735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43933596416787890219521823 65900394625181835329282735)
  ·
    refine ⟨98850591937772752993924103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65900394625181835329282735 98850591937772752993924103)
    ·
      refine ⟨148275887906659129490886155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98850591937772752993924103 148275887906659129490886155)
      ·
        refine ⟨222413831859988694236329233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148275887906659129490886155 222413831859988694236329233)
        ·
          refine ⟨166810373894991520677246925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 222413831859988694236329233 166810373894991520677246925)
          ·
            refine ⟨62553890210621820253967597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 166810373894991520677246925 62553890210621820253967597)
            ·
              refine ⟨23457708828983182595237849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62553890210621820253967597 23457708828983182595237849)
              ·
                refine ⟨17593281621737386946428387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23457708828983182595237849 17593281621737386946428387)
                ·
                  refine ⟨26389922432606080419642581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17593281621737386946428387 26389922432606080419642581)
                  ·
                    refine ⟨618513807014205009835373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 26389922432606080419642581 618513807014205009835373)
                    ·
                      rfl

theorem cell22_1806827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 2, 1, 7].length) (baseStart_1806827 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1806827 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1806827 prefixEnd_1806827 := by exact prefixLift 1806827
  have htrace : WordTrace (prefixWord ++ tailWord_1806827) baseStart_1806827 baseEnd_1806827 := by
    simpa [prefixWord, tailWord_1806827, baseEnd_1806827] using wordTrace_append hprefix tailTrace_1806827
  have hstable : (prefixWord ++ tailWord_1806827).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1806827).length < 2 ^ (prefixWord ++ tailWord_1806827).sum := by decide
  have hdescent : baseEnd_1806827 < baseStart_1806827 := by decide
  rcases family_descends (prefixWord ++ tailWord_1806827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1806833 : List Nat := [1, 2, 2, 2, 3, 1, 4, 3, 1, 3]
def baseStart_1806833 : Nat := 118140960795 + 1806833 * 2 ^ 59
def prefixEnd_1806833 : Nat := 4983230072969 + 3 ^ 40 * 1806833 * 2
def baseEnd_1806833 : Nat := 618515860936822994185355

theorem tailTrace_1806833 : CollatzResearch.WordTrace tailWord_1806833 prefixEnd_1806833 618515860936822994185355 := by
  unfold tailWord_1806833
  simp only [CollatzResearch.WordTrace]
  refine ⟨65900613463160098354001153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43933742308773398902667435 65900613463160098354001153)
  ·
    refine ⟨49425460097370073765500865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65900613463160098354001153 49425460097370073765500865)
    ·
      refine ⟨37069095073027555324125649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49425460097370073765500865 37069095073027555324125649)
      ·
        refine ⟨27801821304770666493094237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37069095073027555324125649 27801821304770666493094237)
        ·
          refine ⟨10425682989288999934910339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27801821304770666493094237 10425682989288999934910339)
          ·
            refine ⟨15638524483933499902365509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10425682989288999934910339 15638524483933499902365509)
            ·
              refine ⟨2932223340737531231693533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15638524483933499902365509 2932223340737531231693533)
              ·
                refine ⟨1099583752776574211885075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2932223340737531231693533 1099583752776574211885075)
                ·
                  refine ⟨1649375629164861317827613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1099583752776574211885075 1649375629164861317827613)
                  ·
                    refine ⟨618515860936822994185355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1649375629164861317827613 618515860936822994185355)
                    ·
                      rfl

theorem cell22_1806833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 4, 3, 1, 3].length) (baseStart_1806833 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1806833 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1806833 prefixEnd_1806833 := by exact prefixLift 1806833
  have htrace : WordTrace (prefixWord ++ tailWord_1806833) baseStart_1806833 baseEnd_1806833 := by
    simpa [prefixWord, tailWord_1806833, baseEnd_1806833] using wordTrace_append hprefix tailTrace_1806833
  have hstable : (prefixWord ++ tailWord_1806833).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1806833).length < 2 ^ (prefixWord ++ tailWord_1806833).sum := by decide
  have hdescent : baseEnd_1806833 < baseStart_1806833 := by decide
  rcases family_descends (prefixWord ++ tailWord_1806833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1806850 : List Nat := [3, 4, 1, 2, 2, 1, 2, 1, 3, 3]
def baseStart_1806850 : Nat := 118140960795 + 1806850 * 2 ^ 59
def prefixEnd_1806850 : Nat := 4983230072969 + 3 ^ 40 * 1806850 * 2
def baseEnd_1806850 : Nat := 618521680384240616510303

theorem tailTrace_1806850 : CollatzResearch.WordTrace tailWord_1806850 prefixEnd_1806850 618521680384240616510303 := by
  unfold tailWord_1806850
  simp only [CollatzResearch.WordTrace]
  refine ⟨16475308376024627564342501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43934155669399006838246669 16475308376024627564342501)
  ·
    refine ⟨3089120320504617668314219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16475308376024627564342501 3089120320504617668314219)
    ·
      refine ⟨4633680480756926502471329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3089120320504617668314219 4633680480756926502471329)
      ·
        refine ⟨3475260360567694876853497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4633680480756926502471329 3475260360567694876853497)
        ·
          refine ⟨2606445270425771157640123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3475260360567694876853497 2606445270425771157640123)
          ·
            refine ⟨3909667905638656736460185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2606445270425771157640123 3909667905638656736460185)
            ·
              refine ⟨2932250929228992552345139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3909667905638656736460185 2932250929228992552345139)
              ·
                refine ⟨4398376393843488828517709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2932250929228992552345139 4398376393843488828517709)
                ·
                  refine ⟨1649391147691308310694141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4398376393843488828517709 1649391147691308310694141)
                  ·
                    refine ⟨618521680384240616510303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1649391147691308310694141 618521680384240616510303)
                    ·
                      rfl

theorem cell22_1806850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 2, 1, 3, 3].length) (baseStart_1806850 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1806850 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1806850 prefixEnd_1806850 := by exact prefixLift 1806850
  have htrace : WordTrace (prefixWord ++ tailWord_1806850) baseStart_1806850 baseEnd_1806850 := by
    simpa [prefixWord, tailWord_1806850, baseEnd_1806850] using wordTrace_append hprefix tailTrace_1806850
  have hstable : (prefixWord ++ tailWord_1806850).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1806850).length < 2 ^ (prefixWord ++ tailWord_1806850).sum := by decide
  have hdescent : baseEnd_1806850 < baseStart_1806850 := by decide
  rcases family_descends (prefixWord ++ tailWord_1806850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1806874 : List Nat := [3, 1, 1, 3, 1, 1, 4, 2, 6]
def baseStart_1806874 : Nat := 118140960795 + 1806874 * 2 ^ 59
def prefixEnd_1806874 : Nat := 4983230072969 + 3 ^ 40 * 1806874 * 2
def baseEnd_1806874 : Nat := 206176632024904184636743

theorem tailTrace_1806874 : CollatzResearch.WordTrace tailWord_1806874 prefixEnd_1806874 206176632024904184636743 := by
  unfold tailWord_1806874
  simp only [CollatzResearch.WordTrace]
  refine ⟨16475527214002890589060919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43934739237341041570829117 16475527214002890589060919)
  ·
    refine ⟨24713290821004335883591379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16475527214002890589060919 24713290821004335883591379)
    ·
      refine ⟨37069936231506503825387069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24713290821004335883591379 37069936231506503825387069)
      ·
        refine ⟨13901226086814938934520151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37069936231506503825387069 13901226086814938934520151)
        ·
          refine ⟨20851839130222408401780227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13901226086814938934520151 20851839130222408401780227)
          ·
            refine ⟨31277758695333612602670341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20851839130222408401780227 31277758695333612602670341)
            ·
              refine ⟨5864579755375052363000689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31277758695333612602670341 5864579755375052363000689)
              ·
                refine ⟨4398434816531289272250517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5864579755375052363000689 4398434816531289272250517)
                ·
                  refine ⟨206176632024904184636743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4398434816531289272250517 206176632024904184636743)
                  ·
                    rfl

theorem cell22_1806874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 4, 2, 6].length) (baseStart_1806874 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1806874 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1806874 prefixEnd_1806874 := by exact prefixLift 1806874
  have htrace : WordTrace (prefixWord ++ tailWord_1806874) baseStart_1806874 baseEnd_1806874 := by
    simpa [prefixWord, tailWord_1806874, baseEnd_1806874] using wordTrace_append hprefix tailTrace_1806874
  have hstable : (prefixWord ++ tailWord_1806874).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1806874).length < 2 ^ (prefixWord ++ tailWord_1806874).sum := by decide
  have hdescent : baseEnd_1806874 < baseStart_1806874 := by decide
  rcases family_descends (prefixWord ++ tailWord_1806874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1806876 : List Nat := [2, 2, 3, 1, 2, 2, 1, 4, 1, 4]
def baseStart_1806876 : Nat := 118140960795 + 1806876 * 2 ^ 59
def prefixEnd_1806876 : Nat := 4983230072969 + 3 ^ 40 * 1806876 * 2
def baseEnd_1806876 : Nat := 618530580715585215360223

theorem tailTrace_1806876 : CollatzResearch.WordTrace tailWord_1806876 prefixEnd_1806876 618530580715585215360223 := by
  unfold tailWord_1806876
  simp only [CollatzResearch.WordTrace]
  refine ⟨32951090901002158348908241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43934787868002877798544321 32951090901002158348908241)
  ·
    refine ⟨24713318175751618761681181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32951090901002158348908241 24713318175751618761681181)
    ·
      refine ⟨9267494315906857035630443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24713318175751618761681181 9267494315906857035630443)
      ·
        refine ⟨13901241473860285553445665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9267494315906857035630443 13901241473860285553445665)
        ·
          refine ⟨10425931105395214165084249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13901241473860285553445665 10425931105395214165084249)
          ·
            refine ⟨7819448329046410623813187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10425931105395214165084249 7819448329046410623813187)
            ·
              refine ⟨11729172493569615935719781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7819448329046410623813187 11729172493569615935719781)
              ·
                refine ⟨2199219842544302987947459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11729172493569615935719781 2199219842544302987947459)
                ·
                  refine ⟨3298829763816454481921189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2199219842544302987947459 3298829763816454481921189)
                  ·
                    refine ⟨618530580715585215360223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3298829763816454481921189 618530580715585215360223)
                    ·
                      rfl

theorem cell22_1806876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 4, 1, 4].length) (baseStart_1806876 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1806876 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1806876 prefixEnd_1806876 := by exact prefixLift 1806876
  have htrace : WordTrace (prefixWord ++ tailWord_1806876) baseStart_1806876 baseEnd_1806876 := by
    simpa [prefixWord, tailWord_1806876, baseEnd_1806876] using wordTrace_append hprefix tailTrace_1806876
  have hstable : (prefixWord ++ tailWord_1806876).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1806876).length < 2 ^ (prefixWord ++ tailWord_1806876).sum := by decide
  have hdescent : baseEnd_1806876 < baseStart_1806876 := by decide
  rcases family_descends (prefixWord ++ tailWord_1806876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1806884 : List Nat := [2, 3, 1, 5, 2, 1, 1, 3, 1, 3]
def baseStart_1806884 : Nat := 118140960795 + 1806884 * 2 ^ 59
def prefixEnd_1806884 : Nat := 4983230072969 + 3 ^ 40 * 1806884 * 2
def baseEnd_1806884 : Nat := 618533319279075861160199

theorem tailTrace_1806884 : CollatzResearch.WordTrace tailWord_1806884 prefixEnd_1806884 618533319279075861160199 := by
  unfold tailWord_1806884
  simp only [CollatzResearch.WordTrace]
  refine ⟨32951236792987667032053853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43934982390650222709405137 32951236792987667032053853)
  ·
    refine ⟨12356713797370375137020195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32951236792987667032053853 12356713797370375137020195)
    ·
      refine ⟨18535070696055562705530293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12356713797370375137020195 18535070696055562705530293)
      ·
        refine ⟨1737662877755209003643465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 18535070696055562705530293 1737662877755209003643465)
        ·
          refine ⟨1303247158316406752732599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1737662877755209003643465 1303247158316406752732599)
          ·
            refine ⟨1954870737474610129098899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1303247158316406752732599 1954870737474610129098899)
            ·
              refine ⟨2932306106211915193648349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1954870737474610129098899 2932306106211915193648349)
              ·
                refine ⟨1099614789829468197618131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2932306106211915193648349 1099614789829468197618131)
                ·
                  refine ⟨1649422184744202296427197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1099614789829468197618131 1649422184744202296427197)
                  ·
                    refine ⟨618533319279075861160199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1649422184744202296427197 618533319279075861160199)
                    ·
                      rfl

theorem cell22_1806884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 1, 1, 3, 1, 3].length) (baseStart_1806884 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1806884 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1806884 prefixEnd_1806884 := by exact prefixLift 1806884
  have htrace : WordTrace (prefixWord ++ tailWord_1806884) baseStart_1806884 baseEnd_1806884 := by
    simpa [prefixWord, tailWord_1806884, baseEnd_1806884] using wordTrace_append hprefix tailTrace_1806884
  have hstable : (prefixWord ++ tailWord_1806884).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1806884).length < 2 ^ (prefixWord ++ tailWord_1806884).sum := by decide
  have hdescent : baseEnd_1806884 < baseStart_1806884 := by decide
  rcases family_descends (prefixWord ++ tailWord_1806884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1806906 : List Nat := [3, 1, 1, 1, 3, 3, 2, 1, 4, 3]
def baseStart_1806906 : Nat := 118140960795 + 1806906 * 2 ^ 59
def prefixEnd_1806906 : Nat := 4983230072969 + 3 ^ 40 * 1806906 * 2
def baseEnd_1806906 : Nat := 618540850328675137110131

theorem tailTrace_1806906 : CollatzResearch.WordTrace tailWord_1806906 prefixEnd_1806906 618540850328675137110131 := by
  unfold tailWord_1806906
  simp only [CollatzResearch.WordTrace]
  refine ⟨16475818997973907955352143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43935517327930421214272381 16475818997973907955352143)
  ·
    refine ⟨24713728496960861933028215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16475818997973907955352143 24713728496960861933028215)
    ·
      refine ⟨37070592745441292899542323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24713728496960861933028215 37070592745441292899542323)
      ·
        refine ⟨55605889118161939349313485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37070592745441292899542323 55605889118161939349313485)
        ·
          refine ⟨20852208419310727255992557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55605889118161939349313485 20852208419310727255992557)
          ·
            refine ⟨7819578157241522720997209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20852208419310727255992557 7819578157241522720997209)
            ·
              refine ⟨5864683617931142040747907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7819578157241522720997209 5864683617931142040747907)
              ·
                refine ⟨8797025426896713061121861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5864683617931142040747907 8797025426896713061121861)
                ·
                  refine ⟨1649442267543133698960349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8797025426896713061121861 1649442267543133698960349)
                  ·
                    refine ⟨618540850328675137110131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1649442267543133698960349 618540850328675137110131)
                    ·
                      rfl

theorem cell22_1806906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 2, 1, 4, 3].length) (baseStart_1806906 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1806906 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1806906 prefixEnd_1806906 := by exact prefixLift 1806906
  have htrace : WordTrace (prefixWord ++ tailWord_1806906) baseStart_1806906 baseEnd_1806906 := by
    simpa [prefixWord, tailWord_1806906, baseEnd_1806906] using wordTrace_append hprefix tailTrace_1806906
  have hstable : (prefixWord ++ tailWord_1806906).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1806906).length < 2 ^ (prefixWord ++ tailWord_1806906).sum := by decide
  have hdescent : baseEnd_1806906 < baseStart_1806906 := by decide
  rcases family_descends (prefixWord ++ tailWord_1806906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1806919 : List Nat := [1, 1, 4, 1, 4, 1, 1, 9]
def baseStart_1806919 : Nat := 118140960795 + 1806919 * 2 ^ 59
def prefixEnd_1806919 : Nat := 4983230072969 + 3 ^ 40 * 1806919 * 2
def baseEnd_1806919 : Nat := 68727255610483048503899

theorem tailTrace_1806919 : CollatzResearch.WordTrace tailWord_1806919 prefixEnd_1806919 68727255610483048503899 := by
  unfold tailWord_1806919
  simp only [CollatzResearch.WordTrace]
  refine ⟨65903750140848535041631811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43935833427232356694421207 65903750140848535041631811)
  ·
    refine ⟨98855625211272802562447717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65903750140848535041631811 98855625211272802562447717)
    ·
      refine ⟨18535429727113650480458947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 98855625211272802562447717 18535429727113650480458947)
      ·
        refine ⟨27803144590670475720688421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18535429727113650480458947 27803144590670475720688421)
        ·
          refine ⟨5213089610750714197629079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27803144590670475720688421 5213089610750714197629079)
          ·
            refine ⟨7819634416126071296443619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5213089610750714197629079 7819634416126071296443619)
            ·
              refine ⟨11729451624189106944665429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7819634416126071296443619 11729451624189106944665429)
              ·
                refine ⟨68727255610483048503899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 11729451624189106944665429 68727255610483048503899)
                ·
                  rfl

theorem cell22_1806919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 9].length) (baseStart_1806919 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1806919 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1806919 prefixEnd_1806919 := by exact prefixLift 1806919
  have htrace : WordTrace (prefixWord ++ tailWord_1806919) baseStart_1806919 baseEnd_1806919 := by
    simpa [prefixWord, tailWord_1806919, baseEnd_1806919] using wordTrace_append hprefix tailTrace_1806919
  have hstable : (prefixWord ++ tailWord_1806919).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1806919).length < 2 ^ (prefixWord ++ tailWord_1806919).sum := by decide
  have hdescent : baseEnd_1806919 < baseStart_1806919 := by decide
  rcases family_descends (prefixWord ++ tailWord_1806919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1806923 : List Nat := [1, 1, 1, 1, 3, 1, 8, 1, 2, 3]
def baseStart_1806923 : Nat := 118140960795 + 1806923 * 2 ^ 59
def prefixEnd_1806923 : Nat := 4983230072969 + 3 ^ 40 * 1806923 * 2
def baseEnd_1806923 : Nat := 618546669776092759435079

theorem tailTrace_1806923 : CollatzResearch.WordTrace tailWord_1806923 prefixEnd_1806923 618546669776092759435079 := by
  unfold tailWord_1806923
  simp only [CollatzResearch.WordTrace]
  refine ⟨65903896032834043724777423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43935930688556029149851615 65903896032834043724777423)
  ·
    refine ⟨98855844049251065587166135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65903896032834043724777423 98855844049251065587166135)
    ·
      refine ⟨148283766073876598380749203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98855844049251065587166135 148283766073876598380749203)
      ·
        refine ⟨222425649110814897571123805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148283766073876598380749203 222425649110814897571123805)
        ·
          refine ⟨83409618416555586589171427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 222425649110814897571123805 83409618416555586589171427)
          ·
            refine ⟨125114427624833379883757141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83409618416555586589171427 125114427624833379883757141)
            ·
              refine ⟨1466184698728516170512779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 125114427624833379883757141 1466184698728516170512779)
              ·
                refine ⟨2199277048092774255769169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1466184698728516170512779 2199277048092774255769169)
                ·
                  refine ⟨1649457786069580691826877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2199277048092774255769169 1649457786069580691826877)
                  ·
                    refine ⟨618546669776092759435079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1649457786069580691826877 618546669776092759435079)
                    ·
                      rfl

theorem cell22_1806923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 8, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 8, 1, 2, 3].length) (baseStart_1806923 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1806923 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1806923 prefixEnd_1806923 := by exact prefixLift 1806923
  have htrace : WordTrace (prefixWord ++ tailWord_1806923) baseStart_1806923 baseEnd_1806923 := by
    simpa [prefixWord, tailWord_1806923, baseEnd_1806923] using wordTrace_append hprefix tailTrace_1806923
  have hstable : (prefixWord ++ tailWord_1806923).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1806923).length < 2 ^ (prefixWord ++ tailWord_1806923).sum := by decide
  have hdescent : baseEnd_1806923 < baseStart_1806923 := by decide
  rcases family_descends (prefixWord ++ tailWord_1806923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1806968 : List Nat := [2, 1, 2, 1, 1, 1, 2, 8, 1, 3]
def baseStart_1806968 : Nat := 118140960795 + 1806968 * 2 ^ 59
def prefixEnd_1806968 : Nat := 4983230072969 + 3 ^ 40 * 1806968 * 2
def baseEnd_1806968 : Nat := 618562074195727642059941

theorem tailTrace_1806968 : CollatzResearch.WordTrace tailWord_1806968 prefixEnd_1806968 618562074195727642059941 := by
  unfold tailWord_1806968
  simp only [CollatzResearch.WordTrace]
  refine ⟨32952768658835508205082779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43937024878447344273443705 32952768658835508205082779)
  ·
    refine ⟨49429152988253262307624169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32952768658835508205082779 49429152988253262307624169)
    ·
      refine ⟨37071864741189946730718127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49429152988253262307624169 37071864741189946730718127)
      ·
        refine ⟨55607797111784920096077191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37071864741189946730718127 55607797111784920096077191)
        ·
          refine ⟨83411695667677380144115787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55607797111784920096077191 83411695667677380144115787)
          ·
            refine ⟨125117543501516070216173681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83411695667677380144115787 125117543501516070216173681)
            ·
              refine ⟨93838157626137052662130261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125117543501516070216173681 93838157626137052662130261)
              ·
                refine ⟨1099665909681293585884339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 93838157626137052662130261 1099665909681293585884339)
                ·
                  refine ⟨1649498864521940378826509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1099665909681293585884339 1649498864521940378826509)
                  ·
                    refine ⟨618562074195727642059941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1649498864521940378826509 618562074195727642059941)
                    ·
                      rfl

theorem cell22_1806968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 8, 1, 3].length) (baseStart_1806968 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1806968 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1806968 prefixEnd_1806968 := by exact prefixLift 1806968
  have htrace : WordTrace (prefixWord ++ tailWord_1806968) baseStart_1806968 baseEnd_1806968 := by
    simpa [prefixWord, tailWord_1806968, baseEnd_1806968] using wordTrace_append hprefix tailTrace_1806968
  have hstable : (prefixWord ++ tailWord_1806968).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1806968).length < 2 ^ (prefixWord ++ tailWord_1806968).sum := by decide
  have hdescent : baseEnd_1806968 < baseStart_1806968 := by decide
  rcases family_descends (prefixWord ++ tailWord_1806968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1806979 : List Nat := [1, 1, 1, 3, 3, 1, 3, 1, 1, 7]
def baseStart_1806979 : Nat := 118140960795 + 1806979 * 2 ^ 59
def prefixEnd_1806979 : Nat := 4983230072969 + 3 ^ 40 * 1806979 * 2
def baseEnd_1806979 : Nat := 618565839720527280034907

theorem tailTrace_1806979 : CollatzResearch.WordTrace tailWord_1806979 prefixEnd_1806979 618565839720527280034907 := by
  unfold tailWord_1806979
  simp only [CollatzResearch.WordTrace]
  refine ⟨65905938520631165288815991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43937292347087443525877327 65905938520631165288815991)
  ·
    refine ⟨98858907780946747933223987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65905938520631165288815991 98858907780946747933223987)
    ·
      refine ⟨148288361671420121899835981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98858907780946747933223987 148288361671420121899835981)
      ·
        refine ⟨55608135626782545712438493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 148288361671420121899835981 55608135626782545712438493)
        ·
          refine ⟨20853050860043454642164435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55608135626782545712438493 20853050860043454642164435)
          ·
            refine ⟨31279576290065181963246653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20853050860043454642164435 31279576290065181963246653)
            ·
              refine ⟨11729841108774443236217495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31279576290065181963246653 11729841108774443236217495)
              ·
                refine ⟨17594761663161664854326243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11729841108774443236217495 17594761663161664854326243)
                ·
                  refine ⟨26392142494742497281489365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17594761663161664854326243 26392142494742497281489365)
                  ·
                    refine ⟨618565839720527280034907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 26392142494742497281489365 618565839720527280034907)
                    ·
                      rfl

theorem cell22_1806979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 1, 1, 7].length) (baseStart_1806979 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1806979 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1806979 prefixEnd_1806979 := by exact prefixLift 1806979
  have htrace : WordTrace (prefixWord ++ tailWord_1806979) baseStart_1806979 baseEnd_1806979 := by
    simpa [prefixWord, tailWord_1806979, baseEnd_1806979] using wordTrace_append hprefix tailTrace_1806979
  have hstable : (prefixWord ++ tailWord_1806979).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1806979).length < 2 ^ (prefixWord ++ tailWord_1806979).sum := by decide
  have hdescent : baseEnd_1806979 < baseStart_1806979 := by decide
  rcases family_descends (prefixWord ++ tailWord_1806979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1806981 : List Nat := [1, 3, 1, 1, 4, 2, 2, 3, 5]
def baseStart_1806981 : Nat := 118140960795 + 1806981 * 2 ^ 59
def prefixEnd_1806981 : Nat := 4983230072969 + 3 ^ 40 * 1806981 * 2
def baseEnd_1806981 : Nat := 206188841453799980494967

theorem tailTrace_1806981 : CollatzResearch.WordTrace tailWord_1806981 prefixEnd_1806981 206188841453799980494967 := by
  unfold tailWord_1806981
  simp only [CollatzResearch.WordTrace]
  refine ⟨65906011466623919630388797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43937340977749279753592531 65906011466623919630388797)
  ·
    refine ⟨24714754299983969861395799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65906011466623919630388797 24714754299983969861395799)
    ·
      refine ⟨37072131449975954792093699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24714754299983969861395799 37072131449975954792093699)
      ·
        refine ⟨55608197174963932188140549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37072131449975954792093699 55608197174963932188140549)
        ·
          refine ⟨10426536970305737285276353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55608197174963932188140549 10426536970305737285276353)
          ·
            refine ⟨7819902727729302963957265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10426536970305737285276353 7819902727729302963957265)
            ·
              refine ⟨5864927045796977222967949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7819902727729302963957265 5864927045796977222967949)
              ·
                refine ⟨2199347642173866458612981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5864927045796977222967949 2199347642173866458612981)
                ·
                  refine ⟨206188841453799980494967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2199347642173866458612981 206188841453799980494967)
                  ·
                    rfl

theorem cell22_1806981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 2, 3, 5].length) (baseStart_1806981 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1806981 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1806981 prefixEnd_1806981 := by exact prefixLift 1806981
  have htrace : WordTrace (prefixWord ++ tailWord_1806981) baseStart_1806981 baseEnd_1806981 := by
    simpa [prefixWord, tailWord_1806981, baseEnd_1806981] using wordTrace_append hprefix tailTrace_1806981
  have hstable : (prefixWord ++ tailWord_1806981).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1806981).length < 2 ^ (prefixWord ++ tailWord_1806981).sum := by decide
  have hdescent : baseEnd_1806981 < baseStart_1806981 := by decide
  rcases family_descends (prefixWord ++ tailWord_1806981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1807071 : List Nat := [1, 1, 2, 3, 2, 5, 8]
def baseStart_1807071 : Nat := 118140960795 + 1807071 * 2 ^ 59
def prefixEnd_1807071 : Nat := 4983230072969 + 3 ^ 40 * 1807071 * 2
def baseEnd_1807071 : Nat := 22911012340765544693875

theorem tailTrace_1807071 : CollatzResearch.WordTrace tailWord_1807071 prefixEnd_1807071 22911012340765544693875 := by
  unfold tailWord_1807071
  simp only [CollatzResearch.WordTrace]
  refine ⟨65909294036297865001165067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43939529357531910000776711 65909294036297865001165067)
  ·
    refine ⟨98863941054446797501747601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65909294036297865001165067 98863941054446797501747601)
    ·
      refine ⟨74147955790835098126310701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98863941054446797501747601 74147955790835098126310701)
      ·
        refine ⟨27805483421563161797366513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74147955790835098126310701 27805483421563161797366513)
        ·
          refine ⟨20854112566172371348024885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27805483421563161797366513 20854112566172371348024885)
          ·
            refine ⟨1955073053078659813877333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 20854112566172371348024885 1955073053078659813877333)
            ·
              refine ⟨22911012340765544693875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1955073053078659813877333 22911012340765544693875)
              ·
                rfl

theorem cell22_1807071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 5, 8].length) (baseStart_1807071 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1807071 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1807071 prefixEnd_1807071 := by exact prefixLift 1807071
  have htrace : WordTrace (prefixWord ++ tailWord_1807071) baseStart_1807071 baseEnd_1807071 := by
    simpa [prefixWord, tailWord_1807071, baseEnd_1807071] using wordTrace_append hprefix tailTrace_1807071
  have hstable : (prefixWord ++ tailWord_1807071).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1807071).length < 2 ^ (prefixWord ++ tailWord_1807071).sum := by decide
  have hdescent : baseEnd_1807071 < baseStart_1807071 := by decide
  rcases family_descends (prefixWord ++ tailWord_1807071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1807073 : List Nat := [1, 2, 3, 1, 4, 2, 1, 2, 2, 4]
def baseStart_1807073 : Nat := 118140960795 + 1807073 * 2 ^ 59
def prefixEnd_1807073 : Nat := 4983230072969 + 3 ^ 40 * 1807073 * 2
def baseEnd_1807073 : Nat := 618598017841542368184619

theorem tailTrace_1807073 : CollatzResearch.WordTrace tailWord_1807073 prefixEnd_1807073 618598017841542368184619 := by
  unfold tailWord_1807073
  simp only [CollatzResearch.WordTrace]
  refine ⟨65909366982290619342737873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43939577988193746228491915 65909366982290619342737873)
  ·
    refine ⟨49432025236717964507053405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65909366982290619342737873 49432025236717964507053405)
    ·
      refine ⟨18537009463769236690145027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49432025236717964507053405 18537009463769236690145027)
      ·
        refine ⟨27805514195653855035217541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18537009463769236690145027 27805514195653855035217541)
        ·
          refine ⟨5213533911685097819103289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27805514195653855035217541 5213533911685097819103289)
          ·
            refine ⟨3910150433763823364327467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5213533911685097819103289 3910150433763823364327467)
            ·
              refine ⟨5865225650645735046491201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3910150433763823364327467 5865225650645735046491201)
              ·
                refine ⟨4398919237984301284868401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5865225650645735046491201 4398919237984301284868401)
                ·
                  refine ⟨3299189428488225963651301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4398919237984301284868401 3299189428488225963651301)
                  ·
                    refine ⟨618598017841542368184619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3299189428488225963651301 618598017841542368184619)
                    ·
                      rfl

theorem cell22_1807073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 1, 2, 2, 4].length) (baseStart_1807073 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1807073 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1807073 prefixEnd_1807073 := by exact prefixLift 1807073
  have htrace : WordTrace (prefixWord ++ tailWord_1807073) baseStart_1807073 baseEnd_1807073 := by
    simpa [prefixWord, tailWord_1807073, baseEnd_1807073] using wordTrace_append hprefix tailTrace_1807073
  have hstable : (prefixWord ++ tailWord_1807073).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1807073).length < 2 ^ (prefixWord ++ tailWord_1807073).sum := by decide
  have hdescent : baseEnd_1807073 < baseStart_1807073 := by decide
  rcases family_descends (prefixWord ++ tailWord_1807073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1807150 : List Nat := [4, 1, 3, 2, 1, 1, 2, 3, 5]
def baseStart_1807150 : Nat := 118140960795 + 1807150 * 2 ^ 59
def prefixEnd_1807150 : Nat := 4983230072969 + 3 ^ 40 * 1807150 * 2
def baseEnd_1807150 : Nat := 206208125505046611336461

theorem tailTrace_1807150 : CollatzResearch.WordTrace tailWord_1807150 prefixEnd_1807150 206208125505046611336461 := by
  unfold tailWord_1807150
  simp only [CollatzResearch.WordTrace]
  refine ⟨8239021925376457686661363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43941450268674440995527269 8239021925376457686661363)
  ·
    refine ⟨12358532888064686529992045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8239021925376457686661363 12358532888064686529992045)
    ·
      refine ⟨4634449833024257448747017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12358532888064686529992045 4634449833024257448747017)
      ·
        refine ⟨3475837374768193086560263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4634449833024257448747017 3475837374768193086560263)
        ·
          refine ⟨5213756062152289629840395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3475837374768193086560263 5213756062152289629840395)
          ·
            refine ⟨7820634093228434444760593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5213756062152289629840395 7820634093228434444760593)
            ·
              refine ⟨5865475569921325833570445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7820634093228434444760593 5865475569921325833570445)
              ·
                refine ⟨2199553338720497187588917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5865475569921325833570445 2199553338720497187588917)
                ·
                  refine ⟨206208125505046611336461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2199553338720497187588917 206208125505046611336461)
                  ·
                    rfl

theorem cell22_1807150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 2, 3, 5].length) (baseStart_1807150 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1807150 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1807150 prefixEnd_1807150 := by exact prefixLift 1807150
  have htrace : WordTrace (prefixWord ++ tailWord_1807150) baseStart_1807150 baseEnd_1807150 := by
    simpa [prefixWord, tailWord_1807150, baseEnd_1807150] using wordTrace_append hprefix tailTrace_1807150
  have hstable : (prefixWord ++ tailWord_1807150).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1807150).length < 2 ^ (prefixWord ++ tailWord_1807150).sum := by decide
  have hdescent : baseEnd_1807150 < baseStart_1807150 := by decide
  rcases family_descends (prefixWord ++ tailWord_1807150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1807180 : List Nat := [2, 2, 1, 3, 3, 2, 1, 3, 1, 4]
def baseStart_1807180 : Nat := 118140960795 + 1807180 * 2 ^ 59
def prefixEnd_1807180 : Nat := 4983230072969 + 3 ^ 40 * 1807180 * 2
def baseEnd_1807180 : Nat := 618634646128229755759291

theorem tailTrace_1807180 : CollatzResearch.WordTrace tailWord_1807180 prefixEnd_1807180 618634646128229755759291 := by
  unfold tailWord_1807180
  simp only [CollatzResearch.WordTrace]
  refine ⟨32956634796451488308441497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43942179728601984411255329 32956634796451488308441497)
  ·
    refine ⟨24717476097338616231331123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32956634796451488308441497 24717476097338616231331123)
    ·
      refine ⟨37076214146007924346996685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24717476097338616231331123 37076214146007924346996685)
      ·
        refine ⟨13903580304752971630123757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37076214146007924346996685 13903580304752971630123757)
        ·
          refine ⟨5213842614282364361296409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13903580304752971630123757 5213842614282364361296409)
          ·
            refine ⟨3910381960711773270972307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5213842614282364361296409 3910381960711773270972307)
            ·
              refine ⟨5865572941067659906458461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3910381960711773270972307 5865572941067659906458461)
              ·
                refine ⟨2199589852900372464921923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5865572941067659906458461 2199589852900372464921923)
                ·
                  refine ⟨3299384779350558697382885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2199589852900372464921923 3299384779350558697382885)
                  ·
                    refine ⟨618634646128229755759291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3299384779350558697382885 618634646128229755759291)
                    ·
                      rfl

theorem cell22_1807180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 1, 3, 1, 4].length) (baseStart_1807180 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1807180 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1807180 prefixEnd_1807180 := by exact prefixLift 1807180
  have htrace : WordTrace (prefixWord ++ tailWord_1807180) baseStart_1807180 baseEnd_1807180 := by
    simpa [prefixWord, tailWord_1807180, baseEnd_1807180] using wordTrace_append hprefix tailTrace_1807180
  have hstable : (prefixWord ++ tailWord_1807180).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1807180).length < 2 ^ (prefixWord ++ tailWord_1807180).sum := by decide
  have hdescent : baseEnd_1807180 < baseStart_1807180 := by decide
  rcases family_descends (prefixWord ++ tailWord_1807180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1807208 : List Nat := [2, 1, 4, 2, 1, 2, 1, 2, 1, 6]
def baseStart_1807208 : Nat := 118140960795 + 1807208 * 2 ^ 59
def prefixEnd_1807208 : Nat := 4983230072969 + 3 ^ 40 * 1807208 * 2
def baseEnd_1807208 : Nat := 618644231100447016059205

theorem tailTrace_1807208 : CollatzResearch.WordTrace tailWord_1807208 prefixEnd_1807208 618644231100447016059205 := by
  unfold tailWord_1807208
  simp only [CollatzResearch.WordTrace]
  refine ⟨32957145418400768699451139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43942860557867691599268185 32957145418400768699451139)
  ·
    refine ⟨49435718127601153049176709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32957145418400768699451139 49435718127601153049176709)
    ·
      refine ⟨9269197148925216196720633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49435718127601153049176709 9269197148925216196720633)
      ·
        refine ⟨6951897861693912147540475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9269197148925216196720633 6951897861693912147540475)
        ·
          refine ⟨10427846792540868221310713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6951897861693912147540475 10427846792540868221310713)
          ·
            refine ⟨7820885094405651165983035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10427846792540868221310713 7820885094405651165983035)
            ·
              refine ⟨11731327641608476748974553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7820885094405651165983035 11731327641608476748974553)
              ·
                refine ⟨8798495731206357561730915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11731327641608476748974553 8798495731206357561730915)
                ·
                  refine ⟨13197743596809536342596373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8798495731206357561730915 13197743596809536342596373)
                  ·
                    refine ⟨618644231100447016059205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13197743596809536342596373 618644231100447016059205)
                    ·
                      rfl

theorem cell22_1807208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 2, 1, 6].length) (baseStart_1807208 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1807208 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1807208 prefixEnd_1807208 := by exact prefixLift 1807208
  have htrace : WordTrace (prefixWord ++ tailWord_1807208) baseStart_1807208 baseEnd_1807208 := by
    simpa [prefixWord, tailWord_1807208, baseEnd_1807208] using wordTrace_append hprefix tailTrace_1807208
  have hstable : (prefixWord ++ tailWord_1807208).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1807208).length < 2 ^ (prefixWord ++ tailWord_1807208).sum := by decide
  have hdescent : baseEnd_1807208 < baseStart_1807208 := by decide
  rcases family_descends (prefixWord ++ tailWord_1807208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1807313 : List Nat := [1, 2, 2, 1, 2, 1, 4, 3, 6]
def baseStart_1807313 : Nat := 118140960795 + 1807313 * 2 ^ 59
def prefixEnd_1807313 : Nat := 4983230072969 + 3 ^ 40 * 1807313 * 2
def baseEnd_1807313 : Nat := 206226724915420580727961

theorem tailTrace_1807313 : CollatzResearch.WordTrace tailWord_1807313 prefixEnd_1807313 206226724915420580727961 := by
  unfold tailWord_1807313
  simp only [CollatzResearch.WordTrace]
  refine ⟨65918120501421140331474593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43945413667614093554316395 65918120501421140331474593)
  ·
    refine ⟨49438590376065855248605945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65918120501421140331474593 49438590376065855248605945)
    ·
      refine ⟨37078942782049391436454459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49438590376065855248605945 37078942782049391436454459)
      ·
        refine ⟨55618414173074087154681689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37078942782049391436454459 55618414173074087154681689)
        ·
          refine ⟨41713810629805565366011267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55618414173074087154681689 41713810629805565366011267)
          ·
            refine ⟨62570715944708348049016901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41713810629805565366011267 62570715944708348049016901)
            ·
              refine ⟨11732009239632815259190669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62570715944708348049016901 11732009239632815259190669)
              ·
                refine ⟨4399503464862305722196501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11732009239632815259190669 4399503464862305722196501)
                ·
                  refine ⟨206226724915420580727961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4399503464862305722196501 206226724915420580727961)
                  ·
                    rfl

theorem cell22_1807313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 3, 6].length) (baseStart_1807313 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1807313 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1807313 prefixEnd_1807313 := by exact prefixLift 1807313
  have htrace : WordTrace (prefixWord ++ tailWord_1807313) baseStart_1807313 baseEnd_1807313 := by
    simpa [prefixWord, tailWord_1807313, baseEnd_1807313] using wordTrace_append hprefix tailTrace_1807313
  have hstable : (prefixWord ++ tailWord_1807313).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1807313).length < 2 ^ (prefixWord ++ tailWord_1807313).sum := by decide
  have hdescent : baseEnd_1807313 < baseStart_1807313 := by decide
  rcases family_descends (prefixWord ++ tailWord_1807313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1807345 : List Nat := [1, 2, 2, 2, 4, 1, 2, 2, 1, 5]
def baseStart_1807345 : Nat := 118140960795 + 1807345 * 2 ^ 59
def prefixEnd_1807345 : Nat := 4983230072969 + 3 ^ 40 * 1807345 * 2
def baseEnd_1807345 : Nat := 618691129000224325383785

theorem tailTrace_1807345 : CollatzResearch.WordTrace tailWord_1807345 prefixEnd_1807345 618691129000224325383785 := by
  unfold tailWord_1807345
  simp only [CollatzResearch.WordTrace]
  refine ⟨65919287637305209796639489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43946191758203473197759659 65919287637305209796639489)
  ·
    refine ⟨49439465727978907347479617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65919287637305209796639489 49439465727978907347479617)
    ·
      refine ⟨37079599295984180510609713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49439465727978907347479617 37079599295984180510609713)
      ·
        refine ⟨27809699471988135382957285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37079599295984180510609713 27809699471988135382957285)
        ·
          refine ⟨5214318650997775384304491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27809699471988135382957285 5214318650997775384304491)
          ·
            refine ⟨7821477976496663076456737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5214318650997775384304491 7821477976496663076456737)
            ·
              refine ⟨5866108482372497307342553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7821477976496663076456737 5866108482372497307342553)
              ·
                refine ⟨4399581361779372980506915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5866108482372497307342553 4399581361779372980506915)
                ·
                  refine ⟨6599372042669059470760373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4399581361779372980506915 6599372042669059470760373)
                  ·
                    refine ⟨618691129000224325383785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6599372042669059470760373 618691129000224325383785)
                    ·
                      rfl

theorem cell22_1807345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 2, 2, 1, 5].length) (baseStart_1807345 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1807345 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1807345 prefixEnd_1807345 := by exact prefixLift 1807345
  have htrace : WordTrace (prefixWord ++ tailWord_1807345) baseStart_1807345 baseEnd_1807345 := by
    simpa [prefixWord, tailWord_1807345, baseEnd_1807345] using wordTrace_append hprefix tailTrace_1807345
  have hstable : (prefixWord ++ tailWord_1807345).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1807345).length < 2 ^ (prefixWord ++ tailWord_1807345).sum := by decide
  have hdescent : baseEnd_1807345 < baseStart_1807345 := by decide
  rcases family_descends (prefixWord ++ tailWord_1807345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1807392 : List Nat := [2, 1, 1, 7, 1, 1, 1, 8]
def baseStart_1807392 : Nat := 118140960795 + 1807392 * 2 ^ 59
def prefixEnd_1807392 : Nat := 4983230072969 + 3 ^ 40 * 1807392 * 2
def baseEnd_1807392 : Nat := 68745246451192429939849

theorem tailTrace_1807392 : CollatzResearch.WordTrace tailWord_1807392 prefixEnd_1807392 68745246451192429939849 := by
  unfold tailWord_1807392
  simp only [CollatzResearch.WordTrace]
  refine ⟨32960500934067468411800215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43947334578756624549066953 32960500934067468411800215)
  ·
    refine ⟨49440751401101202617700323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32960500934067468411800215 49440751401101202617700323)
    ·
      refine ⟨74161127101651803926550485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49440751401101202617700323 74161127101651803926550485)
      ·
        refine ⟨1738151416444964154528527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 74161127101651803926550485 1738151416444964154528527)
        ·
          refine ⟨2607227124667446231792791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1738151416444964154528527 2607227124667446231792791)
          ·
            refine ⟨3910840687001169347689187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2607227124667446231792791 3910840687001169347689187)
            ·
              refine ⟨5866261030501754021533781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3910840687001169347689187 5866261030501754021533781)
              ·
                refine ⟨68745246451192429939849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5866261030501754021533781 68745246451192429939849)
                ·
                  rfl

theorem cell22_1807392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 1, 8].length) (baseStart_1807392 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1807392 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1807392 prefixEnd_1807392 := by exact prefixLift 1807392
  have htrace : WordTrace (prefixWord ++ tailWord_1807392) baseStart_1807392 baseEnd_1807392 := by
    simpa [prefixWord, tailWord_1807392, baseEnd_1807392] using wordTrace_append hprefix tailTrace_1807392
  have hstable : (prefixWord ++ tailWord_1807392).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1807392).length < 2 ^ (prefixWord ++ tailWord_1807392).sum := by decide
  have hdescent : baseEnd_1807392 < baseStart_1807392 := by decide
  rcases family_descends (prefixWord ++ tailWord_1807392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1807403 : List Nat := [1, 1, 1, 1, 2, 1, 5, 1, 9]
def baseStart_1807403 : Nat := 118140960795 + 1807403 * 2 ^ 59
def prefixEnd_1807403 : Nat := 4983230072969 + 3 ^ 40 * 1807403 * 2
def baseEnd_1807403 : Nat := 206236994528510502477869

theorem tailTrace_1807403 : CollatzResearch.WordTrace tailWord_1807403 prefixEnd_1807403 206236994528510502477869 := by
  unfold tailWord_1807403
  simp only [CollatzResearch.WordTrace]
  refine ⟨65921403071095085702250863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43947602047396723801500575 65921403071095085702250863)
  ·
    refine ⟨98882104606642628553376295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65921403071095085702250863 98882104606642628553376295)
    ·
      refine ⟨148323156909963942830064443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98882104606642628553376295 148323156909963942830064443)
      ·
        refine ⟨222484735364945914245096665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148323156909963942830064443 222484735364945914245096665)
        ·
          refine ⟨166863551523709435683822499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 222484735364945914245096665 166863551523709435683822499)
          ·
            refine ⟨250295327285564153525733749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166863551523709435683822499 250295327285564153525733749)
            ·
              refine ⟨23465186933021639393037539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 250295327285564153525733749 23465186933021639393037539)
              ·
                refine ⟨35197780399532459089556309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23465186933021639393037539 35197780399532459089556309)
                ·
                  refine ⟨206236994528510502477869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 35197780399532459089556309 206236994528510502477869)
                  ·
                    rfl

theorem cell22_1807403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 1, 9].length) (baseStart_1807403 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1807403 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1807403 prefixEnd_1807403 := by exact prefixLift 1807403
  have htrace : WordTrace (prefixWord ++ tailWord_1807403) baseStart_1807403 baseEnd_1807403 := by
    simpa [prefixWord, tailWord_1807403, baseEnd_1807403] using wordTrace_append hprefix tailTrace_1807403
  have hstable : (prefixWord ++ tailWord_1807403).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1807403).length < 2 ^ (prefixWord ++ tailWord_1807403).sum := by decide
  have hdescent : baseEnd_1807403 < baseStart_1807403 := by decide
  rcases family_descends (prefixWord ++ tailWord_1807403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1807420 : List Nat := [2, 2, 2, 2, 2, 2, 2, 1, 7]
def baseStart_1807420 : Nat := 118140960795 + 1807420 * 2 ^ 59
def prefixEnd_1807420 : Nat := 4983230072969 + 3 ^ 40 * 1807420 * 2
def baseEnd_1807420 : Nat := 206238934344316376586185

theorem tailTrace_1807420 : CollatzResearch.WordTrace tailWord_1807420 prefixEnd_1807420 206238934344316376586185 := by
  unfold tailWord_1807420
  simp only [CollatzResearch.WordTrace]
  refine ⟨32961011556016748802809857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43948015408022331737079809 32961011556016748802809857)
  ·
    refine ⟨24720758667012561602107393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32961011556016748802809857 24720758667012561602107393)
    ·
      refine ⟨18540569000259421201580545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24720758667012561602107393 18540569000259421201580545)
      ·
        refine ⟨13905426750194565901185409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18540569000259421201580545 13905426750194565901185409)
        ·
          refine ⟨10429070062645924425889057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13905426750194565901185409 10429070062645924425889057)
          ·
            refine ⟨7821802546984443319416793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10429070062645924425889057 7821802546984443319416793)
            ·
              refine ⟨5866351910238332489562595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7821802546984443319416793 5866351910238332489562595)
              ·
                refine ⟨8799527865357498734343893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5866351910238332489562595 8799527865357498734343893)
                ·
                  refine ⟨206238934344316376586185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8799527865357498734343893 206238934344316376586185)
                  ·
                    rfl

theorem cell22_1807420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 2, 1, 7].length) (baseStart_1807420 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1807420 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1807420 prefixEnd_1807420 := by exact prefixLift 1807420
  have htrace : WordTrace (prefixWord ++ tailWord_1807420) baseStart_1807420 baseEnd_1807420 := by
    simpa [prefixWord, tailWord_1807420, baseEnd_1807420] using wordTrace_append hprefix tailTrace_1807420
  have hstable : (prefixWord ++ tailWord_1807420).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1807420).length < 2 ^ (prefixWord ++ tailWord_1807420).sum := by decide
  have hdescent : baseEnd_1807420 < baseStart_1807420 := by decide
  rcases family_descends (prefixWord ++ tailWord_1807420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1807495 : List Nat := [1, 1, 4, 2, 1, 1, 1, 4, 1, 6]
def baseStart_1807495 : Nat := 118140960795 + 1807495 * 2 ^ 59
def prefixEnd_1807495 : Nat := 4983230072969 + 3 ^ 40 * 1807495 * 2
def baseEnd_1807495 : Nat := 618742477065673934133325

theorem tailTrace_1807495 : CollatzResearch.WordTrace tailWord_1807495 prefixEnd_1807495 618742477065673934133325 := by
  unfold tailWord_1807495
  simp only [CollatzResearch.WordTrace]
  refine ⟨65924758586761785414599939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43949839057841190276399959 65924758586761785414599939)
  ·
    refine ⟨98887137880142678121899909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65924758586761785414599939 98887137880142678121899909)
    ·
      refine ⟨18541338352526752147856233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 98887137880142678121899909 18541338352526752147856233)
      ·
        refine ⟨13906003764395064110892175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18541338352526752147856233 13906003764395064110892175)
        ·
          refine ⟨20859005646592596166338263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13906003764395064110892175 20859005646592596166338263)
          ·
            refine ⟨31288508469888894249507395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20859005646592596166338263 31288508469888894249507395)
            ·
              refine ⟨46932762704833341374261093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31288508469888894249507395 46932762704833341374261093)
              ·
                refine ⟨8799893007156251507673955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46932762704833341374261093 8799893007156251507673955)
                ·
                  refine ⟨13199839510734377261510933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8799893007156251507673955 13199839510734377261510933)
                  ·
                    refine ⟨618742477065673934133325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13199839510734377261510933 618742477065673934133325)
                    ·
                      rfl

theorem cell22_1807495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 4, 1, 6].length) (baseStart_1807495 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1807495 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1807495 prefixEnd_1807495 := by exact prefixLift 1807495
  have htrace : WordTrace (prefixWord ++ tailWord_1807495) baseStart_1807495 baseEnd_1807495 := by
    simpa [prefixWord, tailWord_1807495, baseEnd_1807495] using wordTrace_append hprefix tailTrace_1807495
  have hstable : (prefixWord ++ tailWord_1807495).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1807495).length < 2 ^ (prefixWord ++ tailWord_1807495).sum := by decide
  have hdescent : baseEnd_1807495 < baseStart_1807495 := by decide
  rcases family_descends (prefixWord ++ tailWord_1807495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1807497 : List Nat := [1, 2, 1, 1, 4, 4, 2, 1, 1, 5]
def baseStart_1807497 : Nat := 118140960795 + 1807497 * 2 ^ 59
def prefixEnd_1807497 : Nat := 4983230072969 + 3 ^ 40 * 1807497 * 2
def baseEnd_1807497 : Nat := 618743161706546595583319

theorem tailTrace_1807497 : CollatzResearch.WordTrace tailWord_1807497 prefixEnd_1807497 618743161706546595583319 := by
  unfold tailWord_1807497
  simp only [CollatzResearch.WordTrace]
  refine ⟨65924831532754539756172745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43949887688503026504115163 65924831532754539756172745)
  ·
    refine ⟨49443623649565904817129559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65924831532754539756172745 49443623649565904817129559)
    ·
      refine ⟨74165435474348857225694339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49443623649565904817129559 74165435474348857225694339)
      ·
        refine ⟨111248153211523285838541509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74165435474348857225694339 111248153211523285838541509)
        ·
          refine ⟨20859028727160616094726533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 111248153211523285838541509 20859028727160616094726533)
          ·
            refine ⟨3911067886342615517761225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20859028727160616094726533 3911067886342615517761225)
            ·
              refine ⟨2933300914756961638320919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3911067886342615517761225 2933300914756961638320919)
              ·
                refine ⟨4399951372135442457481379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2933300914756961638320919 4399951372135442457481379)
                ·
                  refine ⟨6599927058203163686222069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4399951372135442457481379 6599927058203163686222069)
                  ·
                    refine ⟨618743161706546595583319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6599927058203163686222069 618743161706546595583319)
                    ·
                      rfl

theorem cell22_1807497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 2, 1, 1, 5].length) (baseStart_1807497 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1807497 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1807497 prefixEnd_1807497 := by exact prefixLift 1807497
  have htrace : WordTrace (prefixWord ++ tailWord_1807497) baseStart_1807497 baseEnd_1807497 := by
    simpa [prefixWord, tailWord_1807497, baseEnd_1807497] using wordTrace_append hprefix tailTrace_1807497
  have hstable : (prefixWord ++ tailWord_1807497).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1807497).length < 2 ^ (prefixWord ++ tailWord_1807497).sum := by decide
  have hdescent : baseEnd_1807497 < baseStart_1807497 := by decide
  rcases family_descends (prefixWord ++ tailWord_1807497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1807512 : List Nat := [2, 1, 2, 4, 2, 2, 1, 1, 1, 6]
def baseStart_1807512 : Nat := 118140960795 + 1807512 * 2 ^ 59
def prefixEnd_1807512 : Nat := 4983230072969 + 3 ^ 40 * 1807512 * 2
def baseEnd_1807512 : Nat := 618748296513091556458273

theorem tailTrace_1807512 : CollatzResearch.WordTrace tailWord_1807512 prefixEnd_1807512 618748296513091556458273 := by
  unfold tailWord_1807512
  simp only [CollatzResearch.WordTrace]
  refine ⟨32962689313850098658984395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43950252418466798211979193 32962689313850098658984395)
  ·
    refine ⟨49444033970775147988476593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32962689313850098658984395 49444033970775147988476593)
    ·
      refine ⟨37083025478081360991357445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49444033970775147988476593 37083025478081360991357445)
      ·
        refine ⟨6953067277140255185879521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37083025478081360991357445 6953067277140255185879521)
        ·
          refine ⟨5214800457855191389409641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6953067277140255185879521 5214800457855191389409641)
          ·
            refine ⟨3911100343391393542057231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5214800457855191389409641 3911100343391393542057231)
            ·
              refine ⟨5866650515087090313085847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3911100343391393542057231 5866650515087090313085847)
              ·
                refine ⟨8799975772630635469628771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5866650515087090313085847 8799975772630635469628771)
                ·
                  refine ⟨13199963658945953204443157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8799975772630635469628771 13199963658945953204443157)
                  ·
                    refine ⟨618748296513091556458273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13199963658945953204443157 618748296513091556458273)
                    ·
                      rfl

theorem cell22_1807512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 1, 1, 1, 6].length) (baseStart_1807512 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1807512 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1807512 prefixEnd_1807512 := by exact prefixLift 1807512
  have htrace : WordTrace (prefixWord ++ tailWord_1807512) baseStart_1807512 baseEnd_1807512 := by
    simpa [prefixWord, tailWord_1807512, baseEnd_1807512] using wordTrace_append hprefix tailTrace_1807512
  have hstable : (prefixWord ++ tailWord_1807512).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1807512).length < 2 ^ (prefixWord ++ tailWord_1807512).sum := by decide
  have hdescent : baseEnd_1807512 < baseStart_1807512 := by decide
  rcases family_descends (prefixWord ++ tailWord_1807512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1807518 : List Nat := [4, 3, 1, 1, 2, 3, 2, 1, 1, 4]
def baseStart_1807518 : Nat := 118140960795 + 1807518 * 2 ^ 59
def prefixEnd_1807518 : Nat := 4983230072969 + 3 ^ 40 * 1807518 * 2
def baseEnd_1807518 : Nat := 618750350435709540808255

theorem tailTrace_1807518 : CollatzResearch.WordTrace tailWord_1807518 prefixEnd_1807518 618750350435709540808255 := by
  unfold tailWord_1807518
  simp only [CollatzResearch.WordTrace]
  refine ⟨8240699683209807542835901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43950398310452306895124805 8240699683209807542835901)
  ·
    refine ⟨3090262381203677828563463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8240699683209807542835901 3090262381203677828563463)
    ·
      refine ⟨4635393571805516742845195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3090262381203677828563463 4635393571805516742845195)
      ·
        refine ⟨6953090357708275114267793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4635393571805516742845195 6953090357708275114267793)
        ·
          refine ⟨5214817768281206335700845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6953090357708275114267793 5214817768281206335700845)
          ·
            refine ⟨1955556663105452375887817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5214817768281206335700845 1955556663105452375887817)
            ·
              refine ⟨1466667497329089281915863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1955556663105452375887817 1466667497329089281915863)
              ·
                refine ⟨2200001245993633922873795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1466667497329089281915863 2200001245993633922873795)
                ·
                  refine ⟨3300001868990450884310693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2200001245993633922873795 3300001868990450884310693)
                  ·
                    refine ⟨618750350435709540808255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3300001868990450884310693 618750350435709540808255)
                    ·
                      rfl

theorem cell22_1807518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 3, 2, 1, 1, 4].length) (baseStart_1807518 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1807518 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1807518 prefixEnd_1807518 := by exact prefixLift 1807518
  have htrace : WordTrace (prefixWord ++ tailWord_1807518) baseStart_1807518 baseEnd_1807518 := by
    simpa [prefixWord, tailWord_1807518, baseEnd_1807518] using wordTrace_append hprefix tailTrace_1807518
  have hstable : (prefixWord ++ tailWord_1807518).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1807518).length < 2 ^ (prefixWord ++ tailWord_1807518).sum := by decide
  have hdescent : baseEnd_1807518 < baseStart_1807518 := by decide
  rcases family_descends (prefixWord ++ tailWord_1807518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1807527 : List Nat := [1, 1, 6, 2, 1, 2, 9]
def baseStart_1807527 : Nat := 118140960795 + 1807527 * 2 ^ 59
def prefixEnd_1807527 : Nat := 4983230072969 + 3 ^ 40 * 1807527 * 2
def baseEnd_1807527 : Nat := 22916793752579130271601

theorem tailTrace_1807527 : CollatzResearch.WordTrace tailWord_1807527 prefixEnd_1807527 22916793752579130271601 := by
  unfold tailWord_1807527
  simp only [CollatzResearch.WordTrace]
  refine ⟨65925925722645854879764835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43950617148430569919843223 65925925722645854879764835)
  ·
    refine ⟨98888888583968782319647253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65925925722645854879764835 98888888583968782319647253)
    ·
      refine ⟨4635416652373536671233465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 98888888583968782319647253 4635416652373536671233465)
      ·
        refine ⟨3476562489280152503425099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4635416652373536671233465 3476562489280152503425099)
        ·
          refine ⟨5214843733920228755137649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3476562489280152503425099 5214843733920228755137649)
          ·
            refine ⟨3911132800440171566353237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5214843733920228755137649 3911132800440171566353237)
            ·
              refine ⟨22916793752579130271601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3911132800440171566353237 22916793752579130271601)
              ·
                rfl

theorem cell22_1807527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 9].length) (baseStart_1807527 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1807527 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1807527 prefixEnd_1807527 := by exact prefixLift 1807527
  have htrace : WordTrace (prefixWord ++ tailWord_1807527) baseStart_1807527 baseEnd_1807527 := by
    simpa [prefixWord, tailWord_1807527, baseEnd_1807527] using wordTrace_append hprefix tailTrace_1807527
  have hstable : (prefixWord ++ tailWord_1807527).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1807527).length < 2 ^ (prefixWord ++ tailWord_1807527).sum := by decide
  have hdescent : baseEnd_1807527 < baseStart_1807527 := by decide
  rcases family_descends (prefixWord ++ tailWord_1807527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1807619 : List Nat := [1, 1, 1, 3, 2, 4, 3, 2, 1, 4]
def baseStart_1807619 : Nat := 118140960795 + 1807619 * 2 ^ 59
def prefixEnd_1807619 : Nat := 4983230072969 + 3 ^ 40 * 1807619 * 2
def baseEnd_1807619 : Nat := 618784924799778944032945

theorem tailTrace_1807619 : CollatzResearch.WordTrace tailWord_1807619 prefixEnd_1807619 618784924799778944032945 := by
  unfold tailWord_1807619
  simp only [CollatzResearch.WordTrace]
  refine ⟨65929281238312554592113911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43952854158875036394742607 65929281238312554592113911)
  ·
    refine ⟨98893921857468831888170867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65929281238312554592113911 98893921857468831888170867)
    ·
      refine ⟨148340882786203247832256301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98893921857468831888170867 148340882786203247832256301)
      ·
        refine ⟨55627831044826217937096113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 148340882786203247832256301 55627831044826217937096113)
        ·
          refine ⟨41720873283619663452822085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55627831044826217937096113 41720873283619663452822085)
          ·
            refine ⟨7822663740678686897404141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41720873283619663452822085 7822663740678686897404141)
            ·
              refine ⟨2933498902754507586526553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7822663740678686897404141 2933498902754507586526553)
              ·
                refine ⟨2200124177065880689894915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2933498902754507586526553 2200124177065880689894915)
                ·
                  refine ⟨3300186265598821034842373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2200124177065880689894915 3300186265598821034842373)
                  ·
                    refine ⟨618784924799778944032945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3300186265598821034842373 618784924799778944032945)
                    ·
                      rfl

theorem cell22_1807619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 3, 2, 1, 4].length) (baseStart_1807619 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1807619 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1807619 prefixEnd_1807619 := by exact prefixLift 1807619
  have htrace : WordTrace (prefixWord ++ tailWord_1807619) baseStart_1807619 baseEnd_1807619 := by
    simpa [prefixWord, tailWord_1807619, baseEnd_1807619] using wordTrace_append hprefix tailTrace_1807619
  have hstable : (prefixWord ++ tailWord_1807619).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1807619).length < 2 ^ (prefixWord ++ tailWord_1807619).sum := by decide
  have hdescent : baseEnd_1807619 < baseStart_1807619 := by decide
  rcases family_descends (prefixWord ++ tailWord_1807619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1807651 : List Nat := [1, 1, 1, 4, 2, 3, 4, 2, 4]
def baseStart_1807651 : Nat := 118140960795 + 1807651 * 2 ^ 59
def prefixEnd_1807651 : Nat := 4983230072969 + 3 ^ 40 * 1807651 * 2
def baseEnd_1807651 : Nat := 206265293017913842410949

theorem tailTrace_1807651 : CollatzResearch.WordTrace tailWord_1807651 prefixEnd_1807651 206265293017913842410949 := by
  unfold tailWord_1807651
  simp only [CollatzResearch.WordTrace]
  refine ⟨65930448374196624057278807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43953632249464416038185871 65930448374196624057278807)
  ·
    refine ⟨98895672561294936085918211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65930448374196624057278807 98895672561294936085918211)
    ·
      refine ⟨148343508841942404128877317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98895672561294936085918211 148343508841942404128877317)
      ·
        refine ⟨27814407907864200774164497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 148343508841942404128877317 27814407907864200774164497)
        ·
          refine ⟨20860805930898150580623373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27814407907864200774164497 20860805930898150580623373)
          ·
            refine ⟨7822802224086806467733765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20860805930898150580623373 7822802224086806467733765)
            ·
              refine ⟨1466775417016276212700081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7822802224086806467733765 1466775417016276212700081)
              ·
                refine ⟨1100081562762207159525061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1466775417016276212700081 1100081562762207159525061)
                ·
                  refine ⟨206265293017913842410949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1100081562762207159525061 206265293017913842410949)
                  ·
                    rfl

theorem cell22_1807651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 4, 2, 4].length) (baseStart_1807651 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1807651 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1807651 prefixEnd_1807651 := by exact prefixLift 1807651
  have htrace : WordTrace (prefixWord ++ tailWord_1807651) baseStart_1807651 baseEnd_1807651 := by
    simpa [prefixWord, tailWord_1807651, baseEnd_1807651] using wordTrace_append hprefix tailTrace_1807651
  have hstable : (prefixWord ++ tailWord_1807651).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1807651).length < 2 ^ (prefixWord ++ tailWord_1807651).sum := by decide
  have hdescent : baseEnd_1807651 < baseStart_1807651 := by decide
  rcases family_descends (prefixWord ++ tailWord_1807651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1807666 : List Nat := [3, 2, 1, 1, 4, 1, 2, 3, 2, 3]
def baseStart_1807666 : Nat := 118140960795 + 1807666 * 2 ^ 59
def prefixEnd_1807666 : Nat := 4983230072969 + 3 ^ 40 * 1807666 * 2
def baseEnd_1807666 : Nat := 618801013860286488107801

theorem tailTrace_1807666 : CollatzResearch.WordTrace tailWord_1807666 prefixEnd_1807666 618801013860286488107801 := by
  unfold tailWord_1807666
  simp only [CollatzResearch.WordTrace]
  refine ⟨16482748867285570404768713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43953996979428187746049901 16482748867285570404768713)
  ·
    refine ⟨12362061650464177803576535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16482748867285570404768713 12362061650464177803576535)
    ·
      refine ⟨18543092475696266705364803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12362061650464177803576535 18543092475696266705364803)
      ·
        refine ⟨27814638713544400058047205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18543092475696266705364803 27814638713544400058047205)
        ·
          refine ⟨5215244758789575010883851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27814638713544400058047205 5215244758789575010883851)
          ·
            refine ⟨7822867138184362516325777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5215244758789575010883851 7822867138184362516325777)
            ·
              refine ⟨5867150353638271887244333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7822867138184362516325777 5867150353638271887244333)
              ·
                refine ⟨2200181382614351957716625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5867150353638271887244333 2200181382614351957716625)
                ·
                  refine ⟨1650136036960763968287469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2200181382614351957716625 1650136036960763968287469)
                  ·
                    refine ⟨618801013860286488107801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1650136036960763968287469 618801013860286488107801)
                    ·
                      rfl

theorem cell22_1807666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 2, 3, 2, 3].length) (baseStart_1807666 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1807666 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1807666 prefixEnd_1807666 := by exact prefixLift 1807666
  have htrace : WordTrace (prefixWord ++ tailWord_1807666) baseStart_1807666 baseEnd_1807666 := by
    simpa [prefixWord, tailWord_1807666, baseEnd_1807666] using wordTrace_append hprefix tailTrace_1807666
  have hstable : (prefixWord ++ tailWord_1807666).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1807666).length < 2 ^ (prefixWord ++ tailWord_1807666).sum := by decide
  have hdescent : baseEnd_1807666 < baseStart_1807666 := by decide
  rcases family_descends (prefixWord ++ tailWord_1807666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1807679 : List Nat := [1, 1, 2, 2, 4, 3, 3, 6]
def baseStart_1807679 : Nat := 118140960795 + 1807679 * 2 ^ 59
def prefixEnd_1807679 : Nat := 4983230072969 + 3 ^ 40 * 1807679 * 2
def baseEnd_1807679 : Nat := 68756162669550976392529

theorem tailTrace_1807679 : CollatzResearch.WordTrace tailWord_1807679 prefixEnd_1807679 68756162669550976392529 := by
  unfold tailWord_1807679
  simp only [CollatzResearch.WordTrace]
  refine ⟨65931469618095184839298091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43954313078730123226198727 65931469618095184839298091)
  ·
    refine ⟨98897204427142777258947137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65931469618095184839298091 98897204427142777258947137)
    ·
      refine ⟨74172903320357082944210353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98897204427142777258947137 74172903320357082944210353)
      ·
        refine ⟨55629677490267812208157765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74172903320357082944210353 55629677490267812208157765)
        ·
          refine ⟨10430564529425214789029581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55629677490267812208157765 10430564529425214789029581)
          ·
            refine ⟨3911461698534455545886093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10430564529425214789029581 3911461698534455545886093)
            ·
              refine ⟨1466798136950420829707285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3911461698534455545886093 1466798136950420829707285)
              ·
                refine ⟨68756162669550976392529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1466798136950420829707285 68756162669550976392529)
                ·
                  rfl

theorem cell22_1807679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 3, 6].length) (baseStart_1807679 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1807679 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1807679 prefixEnd_1807679 := by exact prefixLift 1807679
  have htrace : WordTrace (prefixWord ++ tailWord_1807679) baseStart_1807679 baseEnd_1807679 := by
    simpa [prefixWord, tailWord_1807679, baseEnd_1807679] using wordTrace_append hprefix tailTrace_1807679
  have hstable : (prefixWord ++ tailWord_1807679).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1807679).length < 2 ^ (prefixWord ++ tailWord_1807679).sum := by decide
  have hdescent : baseEnd_1807679 < baseStart_1807679 := by decide
  rcases family_descends (prefixWord ++ tailWord_1807679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1807681 : List Nat := [1, 2, 5, 2, 1, 1, 3, 1, 2, 4]
def baseStart_1807681 : Nat := 118140960795 + 1807681 * 2 ^ 59
def prefixEnd_1807681 : Nat := 4983230072969 + 3 ^ 40 * 1807681 * 2
def baseEnd_1807681 : Nat := 618806148666831448982755

theorem tailTrace_1807681 : CollatzResearch.WordTrace tailWord_1807681 prefixEnd_1807681 618806148666831448982755 := by
  unfold tailWord_1807681
  simp only [CollatzResearch.WordTrace]
  refine ⟨65931542564087939180870897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43954361709391959453913931 65931542564087939180870897)
  ·
    refine ⟨49448656923065954385653173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65931542564087939180870897 49448656923065954385653173)
    ·
      refine ⟨4635811586537433223654985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 49448656923065954385653173 4635811586537433223654985)
      ·
        refine ⟨3476858689903074917741239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4635811586537433223654985 3476858689903074917741239)
        ·
          refine ⟨5215288034854612376611859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3476858689903074917741239 5215288034854612376611859)
          ·
            refine ⟨7822932052281918564917789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5215288034854612376611859 7822932052281918564917789)
            ·
              refine ⟨2933599519605719461844171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7822932052281918564917789 2933599519605719461844171)
              ·
                refine ⟨4400399279408579192766257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2933599519605719461844171 4400399279408579192766257)
                ·
                  refine ⟨3300299459556434394574693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4400399279408579192766257 3300299459556434394574693)
                  ·
                    refine ⟨618806148666831448982755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3300299459556434394574693 618806148666831448982755)
                    ·
                      rfl

theorem cell22_1807681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 3, 1, 2, 4].length) (baseStart_1807681 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1807681 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1807681 prefixEnd_1807681 := by exact prefixLift 1807681
  have htrace : WordTrace (prefixWord ++ tailWord_1807681) baseStart_1807681 baseEnd_1807681 := by
    simpa [prefixWord, tailWord_1807681, baseEnd_1807681] using wordTrace_append hprefix tailTrace_1807681
  have hstable : (prefixWord ++ tailWord_1807681).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1807681).length < 2 ^ (prefixWord ++ tailWord_1807681).sum := by decide
  have hdescent : baseEnd_1807681 < baseStart_1807681 := by decide
  rcases family_descends (prefixWord ++ tailWord_1807681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1807694 : List Nat := [4, 1, 1, 1, 1, 1, 3, 2, 5, 3]
def baseStart_1807694 : Nat := 118140960795 + 1807694 * 2 ^ 59
def prefixEnd_1807694 : Nat := 4983230072969 + 3 ^ 40 * 1807694 * 2
def baseEnd_1807694 : Nat := 618810598832503748407715

theorem tailTrace_1807694 : CollatzResearch.WordTrace tailWord_1807694 prefixEnd_1807694 618810598832503748407715 := by
  unfold tailWord_1807694
  simp only [CollatzResearch.WordTrace]
  refine ⟨8241502089130105300136767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43954677808693894934062757 8241502089130105300136767)
  ·
    refine ⟨12362253133695157950205151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8241502089130105300136767 12362253133695157950205151)
    ·
      refine ⟨18543379700542736925307727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12362253133695157950205151 18543379700542736925307727)
      ·
        refine ⟨27815069550814105387961591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18543379700542736925307727 27815069550814105387961591)
        ·
          refine ⟨41722604326221158081942387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27815069550814105387961591 41722604326221158081942387)
          ·
            refine ⟨62583906489331737122913581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41722604326221158081942387 62583906489331737122913581)
            ·
              refine ⟨23468964933499401421092593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62583906489331737122913581 23468964933499401421092593)
              ·
                refine ⟨17601723700124551065819445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23468964933499401421092593 17601723700124551065819445)
                ·
                  refine ⟨1650161596886676662420573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 17601723700124551065819445 1650161596886676662420573)
                  ·
                    refine ⟨618810598832503748407715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1650161596886676662420573 618810598832503748407715)
                    ·
                      rfl

theorem cell22_1807694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 2, 5, 3].length) (baseStart_1807694 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1807694 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1807694 prefixEnd_1807694 := by exact prefixLift 1807694
  have htrace : WordTrace (prefixWord ++ tailWord_1807694) baseStart_1807694 baseEnd_1807694 := by
    simpa [prefixWord, tailWord_1807694, baseEnd_1807694] using wordTrace_append hprefix tailTrace_1807694
  have hstable : (prefixWord ++ tailWord_1807694).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1807694).length < 2 ^ (prefixWord ++ tailWord_1807694).sum := by decide
  have hdescent : baseEnd_1807694 < baseStart_1807694 := by decide
  rcases family_descends (prefixWord ++ tailWord_1807694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1807762 : List Nat := [3, 2, 3, 3, 2, 1, 1, 1, 3, 3]
def baseStart_1807762 : Nat := 118140960795 + 1807762 * 2 ^ 59
def prefixEnd_1807762 : Nat := 4983230072969 + 3 ^ 40 * 1807762 * 2
def baseEnd_1807762 : Nat := 618833876622174237707507

theorem tailTrace_1807762 : CollatzResearch.WordTrace tailWord_1807762 prefixEnd_1807762 618833876622174237707507 := by
  unfold tailWord_1807762
  simp only [CollatzResearch.WordTrace]
  refine ⟨16483624219198622503642385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43956331251196326676379693 16483624219198622503642385)
  ·
    refine ⟨12362718164398966877731789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16483624219198622503642385 12362718164398966877731789)
    ·
      refine ⟨4636019311649612579149421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12362718164398966877731789 4636019311649612579149421)
      ·
        refine ⟨1738507241868604717181033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4636019311649612579149421 1738507241868604717181033)
        ·
          refine ⟨1303880431401453537885775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1738507241868604717181033 1303880431401453537885775)
          ·
            refine ⟨1955820647102180306828663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1303880431401453537885775 1955820647102180306828663)
            ·
              refine ⟨2933730970653270460242995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1955820647102180306828663 2933730970653270460242995)
              ·
                refine ⟨4400596455979905690364493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2933730970653270460242995 4400596455979905690364493)
                ·
                  refine ⟨1650223670992464633886685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4400596455979905690364493 1650223670992464633886685)
                  ·
                    refine ⟨618833876622174237707507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1650223670992464633886685 618833876622174237707507)
                    ·
                      rfl

theorem cell22_1807762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 1, 1, 1, 3, 3].length) (baseStart_1807762 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1807762 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1807762 prefixEnd_1807762 := by exact prefixLift 1807762
  have htrace : WordTrace (prefixWord ++ tailWord_1807762) baseStart_1807762 baseEnd_1807762 := by
    simpa [prefixWord, tailWord_1807762, baseEnd_1807762] using wordTrace_append hprefix tailTrace_1807762
  have hstable : (prefixWord ++ tailWord_1807762).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1807762).length < 2 ^ (prefixWord ++ tailWord_1807762).sum := by decide
  have hdescent : baseEnd_1807762 < baseStart_1807762 := by decide
  rcases family_descends (prefixWord ++ tailWord_1807762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1807769 : List Nat := [1, 2, 1, 2, 1, 5, 3, 1, 6]
def baseStart_1807769 : Nat := 118140960795 + 1807769 * 2 ^ 59
def prefixEnd_1807769 : Nat := 4983230072969 + 3 ^ 40 * 1807769 * 2
def baseEnd_1807769 : Nat := 206278757621742850927495

theorem tailTrace_1807769 : CollatzResearch.WordTrace tailWord_1807769 prefixEnd_1807769 206278757621742850927495 := by
  unfold tailWord_1807769
  simp only [CollatzResearch.WordTrace]
  refine ⟨65934752187769130210074361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43956501458512753473382907 65934752187769130210074361)
  ·
    refine ⟨49451064140826847657555771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65934752187769130210074361 49451064140826847657555771)
    ·
      refine ⟨74176596211240271486333657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49451064140826847657555771 74176596211240271486333657)
      ·
        refine ⟨55632447158430203614750243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74176596211240271486333657 55632447158430203614750243)
        ·
          refine ⟨83448670737645305422125365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55632447158430203614750243 83448670737645305422125365)
          ·
            refine ⟨7823312881654247383324253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 83448670737645305422125365 7823312881654247383324253)
            ·
              refine ⟨2933742330620342768746595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7823312881654247383324253 2933742330620342768746595)
              ·
                refine ⟨4400613495930514153119893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2933742330620342768746595 4400613495930514153119893)
                ·
                  refine ⟨206278757621742850927495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4400613495930514153119893 206278757621742850927495)
                  ·
                    rfl

theorem cell22_1807769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 3, 1, 6].length) (baseStart_1807769 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1807769 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1807769 prefixEnd_1807769 := by exact prefixLift 1807769
  have htrace : WordTrace (prefixWord ++ tailWord_1807769) baseStart_1807769 baseEnd_1807769 := by
    simpa [prefixWord, tailWord_1807769, baseEnd_1807769] using wordTrace_append hprefix tailTrace_1807769
  have hstable : (prefixWord ++ tailWord_1807769).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1807769).length < 2 ^ (prefixWord ++ tailWord_1807769).sum := by decide
  have hdescent : baseEnd_1807769 < baseStart_1807769 := by decide
  rcases family_descends (prefixWord ++ tailWord_1807769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1807801 : List Nat := [1, 2, 1, 4, 4, 1, 1, 2, 1, 5]
def baseStart_1807801 : Nat := 118140960795 + 1807801 * 2 ^ 59
def prefixEnd_1807801 : Nat := 4983230072969 + 3 ^ 40 * 1807801 * 2
def baseEnd_1807801 : Nat := 618847227119191135982387

theorem tailTrace_1807801 : CollatzResearch.WordTrace tailWord_1807801 prefixEnd_1807801 618847227119191135982387 := by
  unfold tailWord_1807801
  simp only [CollatzResearch.WordTrace]
  refine ⟨65935919323653199675239257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43957279549102133116826171 65935919323653199675239257)
  ·
    refine ⟨49451939492739899756429443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65935919323653199675239257 49451939492739899756429443)
    ·
      refine ⟨74177909239109849634644165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49451939492739899756429443 74177909239109849634644165)
      ·
        refine ⟨13908357982333096806495781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74177909239109849634644165 13908357982333096806495781)
        ·
          refine ⟨2607817121687455651217959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13908357982333096806495781 2607817121687455651217959)
          ·
            refine ⟨3911725682531183476826939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2607817121687455651217959 3911725682531183476826939)
            ·
              refine ⟨5867588523796775215240409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3911725682531183476826939 5867588523796775215240409)
              ·
                refine ⟨4400691392847581411430307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5867588523796775215240409 4400691392847581411430307)
                ·
                  refine ⟨6601037089271372117145461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4400691392847581411430307 6601037089271372117145461)
                  ·
                    refine ⟨618847227119191135982387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6601037089271372117145461 618847227119191135982387)
                    ·
                      rfl

theorem cell22_1807801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 1, 2, 1, 5].length) (baseStart_1807801 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1807801 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1807801 prefixEnd_1807801 := by exact prefixLift 1807801
  have htrace : WordTrace (prefixWord ++ tailWord_1807801) baseStart_1807801 baseEnd_1807801 := by
    simpa [prefixWord, tailWord_1807801, baseEnd_1807801] using wordTrace_append hprefix tailTrace_1807801
  have hstable : (prefixWord ++ tailWord_1807801).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1807801).length < 2 ^ (prefixWord ++ tailWord_1807801).sum := by decide
  have hdescent : baseEnd_1807801 < baseStart_1807801 := by decide
  rcases family_descends (prefixWord ++ tailWord_1807801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1807818 : List Nat := [3, 1, 2, 1, 2, 4, 2, 2, 2, 3]
def baseStart_1807818 : Nat := 118140960795 + 1807818 * 2 ^ 59
def prefixEnd_1807818 : Nat := 4983230072969 + 3 ^ 40 * 1807818 * 2
def baseEnd_1807818 : Nat := 618853046566608758307335

theorem tailTrace_1807818 : CollatzResearch.WordTrace tailWord_1807818 prefixEnd_1807818 618853046566608758307335 := by
  unfold tailWord_1807818
  simp only [CollatzResearch.WordTrace]
  refine ⟨16484134841147902894652027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43957692909727741052405405 16484134841147902894652027)
  ·
    refine ⟨24726202261721854341978041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16484134841147902894652027 24726202261721854341978041)
    ·
      refine ⟨18544651696291390756483531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24726202261721854341978041 18544651696291390756483531)
      ·
        refine ⟨27816977544437086134725297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18544651696291390756483531 27816977544437086134725297)
        ·
          refine ⟨20862733158327814601043973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27816977544437086134725297 20862733158327814601043973)
          ·
            refine ⟨3911762467186465237695745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20862733158327814601043973 3911762467186465237695745)
            ·
              refine ⟨2933821850389848928271809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3911762467186465237695745 2933821850389848928271809)
              ·
                refine ⟨2200366387792386696203857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2933821850389848928271809 2200366387792386696203857)
                ·
                  refine ⟨1650274790844290022152893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2200366387792386696203857 1650274790844290022152893)
                  ·
                    refine ⟨618853046566608758307335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1650274790844290022152893 618853046566608758307335)
                    ·
                      rfl

theorem cell22_1807818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 2, 2, 2, 3].length) (baseStart_1807818 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1807818 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1807818 prefixEnd_1807818 := by exact prefixLift 1807818
  have htrace : WordTrace (prefixWord ++ tailWord_1807818) baseStart_1807818 baseEnd_1807818 := by
    simpa [prefixWord, tailWord_1807818, baseEnd_1807818] using wordTrace_append hprefix tailTrace_1807818
  have hstable : (prefixWord ++ tailWord_1807818).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1807818).length < 2 ^ (prefixWord ++ tailWord_1807818).sum := by decide
  have hdescent : baseEnd_1807818 < baseStart_1807818 := by decide
  rcases family_descends (prefixWord ++ tailWord_1807818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1807820 : List Nat := [2, 2, 1, 4, 2, 3, 2, 2, 4]
def baseStart_1807820 : Nat := 118140960795 + 1807820 * 2 ^ 59
def prefixEnd_1807820 : Nat := 4983230072969 + 3 ^ 40 * 1807820 * 2
def baseEnd_1807820 : Nat := 206284577069160473252443

theorem tailTrace_1807820 : CollatzResearch.WordTrace tailWord_1807820 prefixEnd_1807820 206284577069160473252443 := by
  unfold tailWord_1807820
  simp only [CollatzResearch.WordTrace]
  refine ⟨32968306155292182960090457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43957741540389577280120609 32968306155292182960090457)
  ·
    refine ⟨24726229616469137220067843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32968306155292182960090457 24726229616469137220067843)
    ·
      refine ⟨37089344424703705830101765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24726229616469137220067843 37089344424703705830101765)
      ·
        refine ⟨6954252079631944843144081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37089344424703705830101765 6954252079631944843144081)
        ·
          refine ⟨5215689059723958632358061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6954252079631944843144081 5215689059723958632358061)
          ·
            refine ⟨1955883397396484487134273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5215689059723958632358061 1955883397396484487134273)
            ·
              refine ⟨1466912548047363365350705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1955883397396484487134273 1466912548047363365350705)
              ·
                refine ⟨1100184411035522524013029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1466912548047363365350705 1100184411035522524013029)
                ·
                  refine ⟨206284577069160473252443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1100184411035522524013029 206284577069160473252443)
                  ·
                    rfl

theorem cell22_1807820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 3, 2, 2, 4].length) (baseStart_1807820 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1807820 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1807820 prefixEnd_1807820 := by exact prefixLift 1807820
  have htrace : WordTrace (prefixWord ++ tailWord_1807820) baseStart_1807820 baseEnd_1807820 := by
    simpa [prefixWord, tailWord_1807820, baseEnd_1807820] using wordTrace_append hprefix tailTrace_1807820
  have hstable : (prefixWord ++ tailWord_1807820).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1807820).length < 2 ^ (prefixWord ++ tailWord_1807820).sum := by decide
  have hdescent : baseEnd_1807820 < baseStart_1807820 := by decide
  rcases family_descends (prefixWord ++ tailWord_1807820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1807850 : List Nat := [3, 1, 3, 1, 5, 1, 1, 1, 2, 4]
def baseStart_1807850 : Nat := 118140960795 + 1807850 * 2 ^ 59
def prefixEnd_1807850 : Nat := 4983230072969 + 3 ^ 40 * 1807850 * 2
def baseEnd_1807850 : Nat := 618864000820571341507237

theorem tailTrace_1807850 : CollatzResearch.WordTrace tailWord_1807850 prefixEnd_1807850 618864000820571341507237 := by
  unfold tailWord_1807850
  simp only [CollatzResearch.WordTrace]
  refine ⟨16484426625118920260943251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43958471000317120695848669 16484426625118920260943251)
  ·
    refine ⟨24726639937678380391414877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16484426625118920260943251 24726639937678380391414877)
    ·
      refine ⟨9272489976629392646780579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24726639937678380391414877 9272489976629392646780579)
      ·
        refine ⟨13908734964944088970170869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9272489976629392646780579 13908734964944088970170869)
        ·
          refine ⟨1303943902963508340953519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13908734964944088970170869 1303943902963508340953519)
          ·
            refine ⟨1955915854445262511430279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1303943902963508340953519 1955915854445262511430279)
            ·
              refine ⟨2933873781667893767145419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1955915854445262511430279 2933873781667893767145419)
              ·
                refine ⟨4400810672501840650718129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2933873781667893767145419 4400810672501840650718129)
                ·
                  refine ⟨3300608004376380488038597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4400810672501840650718129 3300608004376380488038597)
                  ·
                    refine ⟨618864000820571341507237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3300608004376380488038597 618864000820571341507237)
                    ·
                      rfl

theorem cell22_1807850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 1, 1, 1, 2, 4].length) (baseStart_1807850 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1807850 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1807850 prefixEnd_1807850 := by exact prefixLift 1807850
  have htrace : WordTrace (prefixWord ++ tailWord_1807850) baseStart_1807850 baseEnd_1807850 := by
    simpa [prefixWord, tailWord_1807850, baseEnd_1807850] using wordTrace_append hprefix tailTrace_1807850
  have hstable : (prefixWord ++ tailWord_1807850).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1807850).length < 2 ^ (prefixWord ++ tailWord_1807850).sum := by decide
  have hdescent : baseEnd_1807850 < baseStart_1807850 := by decide
  rcases family_descends (prefixWord ++ tailWord_1807850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1807893 : List Nat := [1, 3, 2, 1, 3, 3, 3, 1, 5]
def baseStart_1807893 : Nat := 118140960795 + 1807893 * 2 ^ 59
def prefixEnd_1807893 : Nat := 4983230072969 + 3 ^ 40 * 1807893 * 2
def baseEnd_1807893 : Nat := 206292906866444520894035

theorem tailTrace_1807893 : CollatzResearch.WordTrace tailWord_1807893 prefixEnd_1807893 206292906866444520894035 := by
  unfold tailWord_1807893
  simp only [CollatzResearch.WordTrace]
  refine ⟨65939274839319899387588333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43959516559546599591725555 65939274839319899387588333)
  ·
    refine ⟨24727228064744962270345625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65939274839319899387588333 24727228064744962270345625)
    ·
      refine ⟨18545421048558721702759219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24727228064744962270345625 18545421048558721702759219)
      ·
        refine ⟨27818131572838082554138829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18545421048558721702759219 27818131572838082554138829)
        ·
          refine ⟨10431799339814280957802061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27818131572838082554138829 10431799339814280957802061)
          ·
            refine ⟨3911924752430355359175773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10431799339814280957802061 3911924752430355359175773)
            ·
              refine ⟨1466971782161383259690915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3911924752430355359175773 1466971782161383259690915)
              ·
                refine ⟨2200457673242074889536373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1466971782161383259690915 2200457673242074889536373)
                ·
                  refine ⟨206292906866444520894035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2200457673242074889536373 206292906866444520894035)
                  ·
                    rfl

theorem cell22_1807893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 3, 1, 5].length) (baseStart_1807893 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1807893 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1807893 prefixEnd_1807893 := by exact prefixLift 1807893
  have htrace : WordTrace (prefixWord ++ tailWord_1807893) baseStart_1807893 baseEnd_1807893 := by
    simpa [prefixWord, tailWord_1807893, baseEnd_1807893] using wordTrace_append hprefix tailTrace_1807893
  have hstable : (prefixWord ++ tailWord_1807893).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1807893).length < 2 ^ (prefixWord ++ tailWord_1807893).sum := by decide
  have hdescent : baseEnd_1807893 < baseStart_1807893 := by decide
  rcases family_descends (prefixWord ++ tailWord_1807893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1807906 : List Nat := [3, 3, 1, 1, 1, 1, 2, 3, 3, 4]
def baseStart_1807906 : Nat := 118140960795 + 1807906 * 2 ^ 59
def prefixEnd_1807906 : Nat := 4983230072969 + 3 ^ 40 * 1807906 * 2
def baseEnd_1807906 : Nat := 618883170765005862107065

theorem tailTrace_1807906 : CollatzResearch.WordTrace tailWord_1807906 prefixEnd_1807906 618883170765005862107065 := by
  unfold tailWord_1807906
  simp only [CollatzResearch.WordTrace]
  refine ⟨16484937247068200651952893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43959832658848535071874381 16484937247068200651952893)
  ·
    refine ⟨6181851467650575244482335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16484937247068200651952893 6181851467650575244482335)
    ·
      refine ⟨9272777201475862866723503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6181851467650575244482335 9272777201475862866723503)
      ·
        refine ⟨13909165802213794300085255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9272777201475862866723503 13909165802213794300085255)
        ·
          refine ⟨20863748703320691450127883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13909165802213794300085255 20863748703320691450127883)
          ·
            refine ⟨31295623054981037175191825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20863748703320691450127883 31295623054981037175191825)
            ·
              refine ⟨23471717291235777881393869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31295623054981037175191825 23471717291235777881393869)
              ·
                refine ⟨8801893984213416705522701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23471717291235777881393869 8801893984213416705522701)
                ·
                  refine ⟨3300710244080031264571013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8801893984213416705522701 3300710244080031264571013)
                  ·
                    refine ⟨618883170765005862107065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3300710244080031264571013 618883170765005862107065)
                    ·
                      rfl

theorem cell22_1807906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 3, 3, 4].length) (baseStart_1807906 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1807906 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1807906 prefixEnd_1807906 := by exact prefixLift 1807906
  have htrace : WordTrace (prefixWord ++ tailWord_1807906) baseStart_1807906 baseEnd_1807906 := by
    simpa [prefixWord, tailWord_1807906, baseEnd_1807906] using wordTrace_append hprefix tailTrace_1807906
  have hstable : (prefixWord ++ tailWord_1807906).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1807906).length < 2 ^ (prefixWord ++ tailWord_1807906).sum := by decide
  have hdescent : baseEnd_1807906 < baseStart_1807906 := by decide
  rcases family_descends (prefixWord ++ tailWord_1807906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1807953 : List Nat := [1, 2, 2, 1, 3, 2, 3, 3, 2, 3]
def baseStart_1807953 : Nat := 118140960795 + 1807953 * 2 ^ 59
def prefixEnd_1807953 : Nat := 4983230072969 + 3 ^ 40 * 1807953 * 2
def baseEnd_1807953 : Nat := 618899259825513406181921

theorem tailTrace_1807953 : CollatzResearch.WordTrace tailWord_1807953 prefixEnd_1807953 618899259825513406181921 := by
  unfold tailWord_1807953
  simp only [CollatzResearch.WordTrace]
  refine ⟨65941463219102529634772513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43960975479401686423181675 65941463219102529634772513)
  ·
    refine ⟨49456097414326897226079385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65941463219102529634772513 49456097414326897226079385)
    ·
      refine ⟨37092073060745172919559539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49456097414326897226079385 37092073060745172919559539)
      ·
        refine ⟨55638109591117759379339309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37092073060745172919559539 55638109591117759379339309)
        ·
          refine ⟨20864291096669159767252241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55638109591117759379339309 20864291096669159767252241)
          ·
            refine ⟨15648218322501869825439181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20864291096669159767252241 15648218322501869825439181)
            ·
              refine ⟨5868081870938201184539693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15648218322501869825439181 5868081870938201184539693)
              ·
                refine ⟨2200530701601825444202385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5868081870938201184539693 2200530701601825444202385)
                ·
                  refine ⟨1650398026201369083151789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2200530701601825444202385 1650398026201369083151789)
                  ·
                    refine ⟨618899259825513406181921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1650398026201369083151789 618899259825513406181921)
                    ·
                      rfl

theorem cell22_1807953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 3, 3, 2, 3].length) (baseStart_1807953 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1807953 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1807953 prefixEnd_1807953 := by exact prefixLift 1807953
  have htrace : WordTrace (prefixWord ++ tailWord_1807953) baseStart_1807953 baseEnd_1807953 := by
    simpa [prefixWord, tailWord_1807953, baseEnd_1807953] using wordTrace_append hprefix tailTrace_1807953
  have hstable : (prefixWord ++ tailWord_1807953).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1807953).length < 2 ^ (prefixWord ++ tailWord_1807953).sum := by decide
  have hdescent : baseEnd_1807953 < baseStart_1807953 := by decide
  rcases family_descends (prefixWord ++ tailWord_1807953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1808011 : List Nat := [1, 1, 1, 1, 4, 1, 3, 5, 5]
def baseStart_1808011 : Nat := 118140960795 + 1808011 * 2 ^ 59
def prefixEnd_1808011 : Nat := 4983230072969 + 3 ^ 40 * 1808011 * 2
def baseEnd_1808011 : Nat := 206306371470273529410581

theorem tailTrace_1808011 : CollatzResearch.WordTrace tailWord_1808011 prefixEnd_1808011 206306371470273529410581 := by
  unfold tailWord_1808011
  simp only [CollatzResearch.WordTrace]
  refine ⟨65943578652892405540383887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43962385768594937026922591 65943578652892405540383887)
  ·
    refine ⟨98915367979338608310575831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65943578652892405540383887 98915367979338608310575831)
    ·
      refine ⟨148373051969007912465863747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98915367979338608310575831 148373051969007912465863747)
      ·
        refine ⟨222559577953511868698795621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148373051969007912465863747 222559577953511868698795621)
        ·
          refine ⟨41729920866283475381024179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 222559577953511868698795621 41729920866283475381024179)
          ·
            refine ⟨62594881299425213071536269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41729920866283475381024179 62594881299425213071536269)
            ·
              refine ⟨23473080487284454901826101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62594881299425213071536269 23473080487284454901826101)
              ·
                refine ⟨2200601295682917647046197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23473080487284454901826101 2200601295682917647046197)
                ·
                  refine ⟨206306371470273529410581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2200601295682917647046197 206306371470273529410581)
                  ·
                    rfl

theorem cell22_1808011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 5, 5].length) (baseStart_1808011 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1808011 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1808011 prefixEnd_1808011 := by exact prefixLift 1808011
  have htrace : WordTrace (prefixWord ++ tailWord_1808011) baseStart_1808011 baseEnd_1808011 := by
    simpa [prefixWord, tailWord_1808011, baseEnd_1808011] using wordTrace_append hprefix tailTrace_1808011
  have hstable : (prefixWord ++ tailWord_1808011).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1808011).length < 2 ^ (prefixWord ++ tailWord_1808011).sum := by decide
  have hdescent : baseEnd_1808011 < baseStart_1808011 := by decide
  rcases family_descends (prefixWord ++ tailWord_1808011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1808032 : List Nat := [2, 1, 1, 4, 3, 2, 2, 3, 1, 3]
def baseStart_1808032 : Nat := 118140960795 + 1808032 * 2 ^ 59
def prefixEnd_1808032 : Nat := 4983230072969 + 3 ^ 40 * 1808032 * 2
def baseEnd_1808032 : Nat := 618926303139983533456679

theorem tailTrace_1808032 : CollatzResearch.WordTrace tailWord_1808032 prefixEnd_1808032 618926303139983533456679 := by
  unfold tailWord_1808032
  simp only [CollatzResearch.WordTrace]
  refine ⟨32972172292908163063449175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43962896390544217417932233 32972172292908163063449175)
  ·
    refine ⟨49458258439362244595173763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32972172292908163063449175 49458258439362244595173763)
    ·
      refine ⟨74187387659043366892760645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49458258439362244595173763 74187387659043366892760645)
      ·
        refine ⟨13910135186070631292392621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74187387659043366892760645 13910135186070631292392621)
        ·
          refine ⟨5216300694776486734647233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13910135186070631292392621 5216300694776486734647233)
          ·
            refine ⟨3912225521082365050985425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5216300694776486734647233 3912225521082365050985425)
            ·
              refine ⟨2934169140811773788239069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3912225521082365050985425 2934169140811773788239069)
              ·
                refine ⟨1100313427804415170589651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2934169140811773788239069 1100313427804415170589651)
                ·
                  refine ⟨1650470141706622755884477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1100313427804415170589651 1650470141706622755884477)
                  ·
                    refine ⟨618926303139983533456679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1650470141706622755884477 618926303139983533456679)
                    ·
                      rfl

theorem cell22_1808032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 2, 3, 1, 3].length) (baseStart_1808032 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1808032 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1808032 prefixEnd_1808032 := by exact prefixLift 1808032
  have htrace : WordTrace (prefixWord ++ tailWord_1808032) baseStart_1808032 baseEnd_1808032 := by
    simpa [prefixWord, tailWord_1808032, baseEnd_1808032] using wordTrace_append hprefix tailTrace_1808032
  have hstable : (prefixWord ++ tailWord_1808032).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1808032).length < 2 ^ (prefixWord ++ tailWord_1808032).sum := by decide
  have hdescent : baseEnd_1808032 < baseStart_1808032 := by decide
  rcases family_descends (prefixWord ++ tailWord_1808032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1808088 : List Nat := [2, 1, 2, 2, 3, 1, 1, 1, 6, 3]
def baseStart_1808088 : Nat := 118140960795 + 1808088 * 2 ^ 59
def prefixEnd_1808088 : Nat := 4983230072969 + 3 ^ 40 * 1808088 * 2
def baseEnd_1808088 : Nat := 618945473084418054056507

theorem tailTrace_1808088 : CollatzResearch.WordTrace tailWord_1808088 prefixEnd_1808088 618945473084418054056507 := by
  unfold tailWord_1808088
  simp only [CollatzResearch.WordTrace]
  refine ⟨32973193536806723845468459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43964258049075631793957945 32973193536806723845468459)
  ·
    refine ⟨49459790305210085768202689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32973193536806723845468459 49459790305210085768202689)
    ·
      refine ⟨37094842728907564326152017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49459790305210085768202689 37094842728907564326152017)
      ·
        refine ⟨27821132046680673244614013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37094842728907564326152017 27821132046680673244614013)
        ·
          refine ⟨10432924517505252466730255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27821132046680673244614013 10432924517505252466730255)
          ·
            refine ⟨15649386776257878700095383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10432924517505252466730255 15649386776257878700095383)
            ·
              refine ⟨23474080164386818050143075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15649386776257878700095383 23474080164386818050143075)
              ·
                refine ⟨35211120246580227075214613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23474080164386818050143075 35211120246580227075214613)
                ·
                  refine ⟨1650521261558448144150685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 35211120246580227075214613 1650521261558448144150685)
                  ·
                    refine ⟨618945473084418054056507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1650521261558448144150685 618945473084418054056507)
                    ·
                      rfl

theorem cell22_1808088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 1, 6, 3].length) (baseStart_1808088 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1808088 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1808088 prefixEnd_1808088 := by exact prefixLift 1808088
  have htrace : WordTrace (prefixWord ++ tailWord_1808088) baseStart_1808088 baseEnd_1808088 := by
    simpa [prefixWord, tailWord_1808088, baseEnd_1808088] using wordTrace_append hprefix tailTrace_1808088
  have hstable : (prefixWord ++ tailWord_1808088).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1808088).length < 2 ^ (prefixWord ++ tailWord_1808088).sum := by decide
  have hdescent : baseEnd_1808088 < baseStart_1808088 := by decide
  rcases family_descends (prefixWord ++ tailWord_1808088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1808090 : List Nat := [3, 1, 1, 2, 2, 3, 3, 3, 4]
def baseStart_1808090 : Nat := 118140960795 + 1808090 * 2 ^ 59
def prefixEnd_1808090 : Nat := 4983230072969 + 3 ^ 40 * 1808090 * 2
def baseEnd_1808090 : Nat := 206315385908430238502167

theorem tailTrace_1808090 : CollatzResearch.WordTrace tailWord_1808090 prefixEnd_1808090 206315385908430238502167 := by
  unfold tailWord_1808090
  simp only [CollatzResearch.WordTrace]
  refine ⟨16486615004901550508127431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43964306679737468021673149 16486615004901550508127431)
  ·
    refine ⟨24729922507352325762191147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16486615004901550508127431 24729922507352325762191147)
    ·
      refine ⟨37094883761028488643286721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24729922507352325762191147 37094883761028488643286721)
      ·
        refine ⟨27821162820771366482465041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37094883761028488643286721 27821162820771366482465041)
        ·
          refine ⟨20865872115578524861848781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27821162820771366482465041 20865872115578524861848781)
          ·
            refine ⟨7824702043341946823193293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20865872115578524861848781 7824702043341946823193293)
            ·
              refine ⟨2934263266253230058697485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7824702043341946823193293 2934263266253230058697485)
              ·
                refine ⟨1100348724844961272011557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2934263266253230058697485 1100348724844961272011557)
                ·
                  refine ⟨206315385908430238502167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1100348724844961272011557 206315385908430238502167)
                  ·
                    rfl

theorem cell22_1808090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 3, 3, 4].length) (baseStart_1808090 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1808090 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1808090 prefixEnd_1808090 := by exact prefixLift 1808090
  have htrace : WordTrace (prefixWord ++ tailWord_1808090) baseStart_1808090 baseEnd_1808090 := by
    simpa [prefixWord, tailWord_1808090, baseEnd_1808090] using wordTrace_append hprefix tailTrace_1808090
  have hstable : (prefixWord ++ tailWord_1808090).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1808090).length < 2 ^ (prefixWord ++ tailWord_1808090).sum := by decide
  have hdescent : baseEnd_1808090 < baseStart_1808090 := by decide
  rcases family_descends (prefixWord ++ tailWord_1808090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1808118 : List Nat := [5, 1, 1, 1, 1, 3, 1, 9]
def baseStart_1808118 : Nat := 118140960795 + 1808118 * 2 ^ 59
def prefixEnd_1808118 : Nat := 4983230072969 + 3 ^ 40 * 1808118 * 2
def baseEnd_1808118 : Nat := 68772860299723108422935

theorem tailTrace_1808118 : CollatzResearch.WordTrace tailWord_1808118 prefixEnd_1808118 68772860299723108422935 := by
  unfold tailWord_1808118
  simp only [CollatzResearch.WordTrace]
  refine ⟨4121717578969047675908063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 43964987509003175209686005 4121717578969047675908063)
  ·
    refine ⟨6182576368453571513862095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4121717578969047675908063 6182576368453571513862095)
    ·
      refine ⟨9273864552680357270793143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6182576368453571513862095 9273864552680357270793143)
      ·
        refine ⟨13910796829020535906189715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9273864552680357270793143 13910796829020535906189715)
        ·
          refine ⟨20866195243530803859284573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13910796829020535906189715 20866195243530803859284573)
          ·
            refine ⟨7824823216324051447231715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20866195243530803859284573 7824823216324051447231715)
            ·
              refine ⟨11737234824486077170847573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7824823216324051447231715 11737234824486077170847573)
              ·
                refine ⟨68772860299723108422935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 11737234824486077170847573 68772860299723108422935)
                ·
                  rfl

theorem cell22_1808118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 9].length) (baseStart_1808118 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1808118 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1808118 prefixEnd_1808118 := by exact prefixLift 1808118
  have htrace : WordTrace (prefixWord ++ tailWord_1808118) baseStart_1808118 baseEnd_1808118 := by
    simpa [prefixWord, tailWord_1808118, baseEnd_1808118] using wordTrace_append hprefix tailTrace_1808118
  have hstable : (prefixWord ++ tailWord_1808118).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1808118).length < 2 ^ (prefixWord ++ tailWord_1808118).sum := by decide
  have hdescent : baseEnd_1808118 < baseStart_1808118 := by decide
  rcases family_descends (prefixWord ++ tailWord_1808118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1808158 : List Nat := [4, 3, 2, 2, 1, 2, 2, 2, 4]
def baseStart_1808158 : Nat := 118140960795 + 1808158 * 2 ^ 59
def prefixEnd_1808158 : Nat := 4983230072969 + 3 ^ 40 * 1808158 * 2
def baseEnd_1808158 : Nat := 206323145171653734935431

theorem tailTrace_1808158 : CollatzResearch.WordTrace tailWord_1808158 prefixEnd_1808158 206323145171653734935431 := by
  unfold tailWord_1808158
  simp only [CollatzResearch.WordTrace]
  refine ⟨8243617522919981205748141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43965960122239899763990085 8243617522919981205748141)
  ·
    refine ⟨3091356571094992952155553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8243617522919981205748141 3091356571094992952155553)
    ·
      refine ⟨2318517428321244714116665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3091356571094992952155553 2318517428321244714116665)
      ·
        refine ⟨1738888071240933535587499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2318517428321244714116665 1738888071240933535587499)
        ·
          refine ⟨2608332106861400303381249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1738888071240933535587499 2608332106861400303381249)
          ·
            refine ⟨1956249080146050227535937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2608332106861400303381249 1956249080146050227535937)
            ·
              refine ⟨1467186810109537670651953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1956249080146050227535937 1467186810109537670651953)
              ·
                refine ⟨1100390107582153252988965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1467186810109537670651953 1100390107582153252988965)
                ·
                  refine ⟨206323145171653734935431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1100390107582153252988965 206323145171653734935431)
                  ·
                    rfl

theorem cell22_1808158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 2, 2, 2, 4].length) (baseStart_1808158 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1808158 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1808158 prefixEnd_1808158 := by exact prefixLift 1808158
  have htrace : WordTrace (prefixWord ++ tailWord_1808158) baseStart_1808158 baseEnd_1808158 := by
    simpa [prefixWord, tailWord_1808158, baseEnd_1808158] using wordTrace_append hprefix tailTrace_1808158
  have hstable : (prefixWord ++ tailWord_1808158).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1808158).length < 2 ^ (prefixWord ++ tailWord_1808158).sum := by decide
  have hdescent : baseEnd_1808158 < baseStart_1808158 := by decide
  rcases family_descends (prefixWord ++ tailWord_1808158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1808163 : List Nat := [1, 1, 1, 4, 2, 1, 3, 4, 5]
def baseStart_1808163 : Nat := 118140960795 + 1808163 * 2 ^ 59
def prefixEnd_1808163 : Nat := 4983230072969 + 3 ^ 40 * 1808163 * 2
def baseEnd_1808163 : Nat := 206323715705714286143759

theorem tailTrace_1808163 : CollatzResearch.WordTrace tailWord_1808163 prefixEnd_1808163 206323715705714286143759 := by
  unfold tailWord_1808163
  simp only [CollatzResearch.WordTrace]
  refine ⟨65949122548341735499917143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43966081698894490333278095 65949122548341735499917143)
  ·
    refine ⟨98923683822512603249875715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65949122548341735499917143 98923683822512603249875715)
    ·
      refine ⟨148385525733768904874813573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98923683822512603249875715 148385525733768904874813573)
      ·
        refine ⟨27822286075081669664027545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 148385525733768904874813573 27822286075081669664027545)
        ·
          refine ⟨20866714556311252248020659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27822286075081669664027545 20866714556311252248020659)
          ·
            refine ⟨31300071834466878372030989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20866714556311252248020659 31300071834466878372030989)
            ·
              refine ⟨11737526937925079389511621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31300071834466878372030989 11737526937925079389511621)
              ·
                refine ⟨2200786300860952385533429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11737526937925079389511621 2200786300860952385533429)
                ·
                  refine ⟨206323715705714286143759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2200786300860952385533429 206323715705714286143759)
                  ·
                    rfl

theorem cell22_1808163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 4, 5].length) (baseStart_1808163 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1808163 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1808163 prefixEnd_1808163 := by exact prefixLift 1808163
  have htrace : WordTrace (prefixWord ++ tailWord_1808163) baseStart_1808163 baseEnd_1808163 := by
    simpa [prefixWord, tailWord_1808163, baseEnd_1808163] using wordTrace_append hprefix tailTrace_1808163
  have hstable : (prefixWord ++ tailWord_1808163).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1808163).length < 2 ^ (prefixWord ++ tailWord_1808163).sum := by decide
  have hdescent : baseEnd_1808163 < baseStart_1808163 := by decide
  rcases family_descends (prefixWord ++ tailWord_1808163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1808178 : List Nat := [3, 2, 1, 1, 3, 2, 1, 1, 1, 7]
def baseStart_1808178 : Nat := 118140960795 + 1808178 * 2 ^ 59
def prefixEnd_1808178 : Nat := 4983230072969 + 3 ^ 40 * 1808178 * 2
def baseEnd_1808178 : Nat := 618976281923687819306231

theorem tailTrace_1808178 : CollatzResearch.WordTrace tailWord_1808178 prefixEnd_1808178 618976281923687819306231 := by
  unfold tailWord_1808178
  simp only [CollatzResearch.WordTrace]
  refine ⟨16487417410821848265428297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43966446428858262041142125 16487417410821848265428297)
  ·
    refine ⟨12365563058116386199071223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16487417410821848265428297 12365563058116386199071223)
    ·
      refine ⟨18548344587174579298606835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12365563058116386199071223 18548344587174579298606835)
      ·
        refine ⟨27822516880761868947910253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18548344587174579298606835 27822516880761868947910253)
        ·
          refine ⟨10433443830285700855466345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27822516880761868947910253 10433443830285700855466345)
          ·
            refine ⟨7825082872714275641599759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10433443830285700855466345 7825082872714275641599759)
            ·
              refine ⟨11737624309071413462399639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7825082872714275641599759 11737624309071413462399639)
              ·
                refine ⟨17606436463607120193599459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11737624309071413462399639 17606436463607120193599459)
                ·
                  refine ⟨26409654695410680290399189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17606436463607120193599459 26409654695410680290399189)
                  ·
                    refine ⟨618976281923687819306231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 26409654695410680290399189 618976281923687819306231)
                    ·
                      rfl

theorem cell22_1808178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 1, 1, 7].length) (baseStart_1808178 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1808178 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1808178 prefixEnd_1808178 := by exact prefixLift 1808178
  have htrace : WordTrace (prefixWord ++ tailWord_1808178) baseStart_1808178 baseEnd_1808178 := by
    simpa [prefixWord, tailWord_1808178, baseEnd_1808178] using wordTrace_append hprefix tailTrace_1808178
  have hstable : (prefixWord ++ tailWord_1808178).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1808178).length < 2 ^ (prefixWord ++ tailWord_1808178).sum := by decide
  have hdescent : baseEnd_1808178 < baseStart_1808178 := by decide
  rcases family_descends (prefixWord ++ tailWord_1808178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1808225 : List Nat := [1, 2, 3, 1, 1, 1, 3, 6, 4]
def baseStart_1808225 : Nat := 118140960795 + 1808225 * 2 ^ 59
def prefixEnd_1808225 : Nat := 4983230072969 + 3 ^ 40 * 1808225 * 2
def baseEnd_1808225 : Nat := 206330790328065121127029

theorem tailTrace_1808225 : CollatzResearch.WordTrace tailWord_1808225 prefixEnd_1808225 206330790328065121127029 := by
  unfold tailWord_1808225
  simp only [CollatzResearch.WordTrace]
  refine ⟨65951383874117120088674129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43967589249411413392449419 65951383874117120088674129)
  ·
    refine ⟨49463537905587840066505597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65951383874117120088674129 49463537905587840066505597)
    ·
      refine ⟨18548826714595440024939599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49463537905587840066505597 18548826714595440024939599)
      ·
        refine ⟨27823240071893160037409399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18548826714595440024939599 27823240071893160037409399)
        ·
          refine ⟨41734860107839740056114099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27823240071893160037409399 41734860107839740056114099)
          ·
            refine ⟨62602290161759610084171149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41734860107839740056114099 62602290161759610084171149)
            ·
              refine ⟨23475858810659853781564181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62602290161759610084171149 23475858810659853781564181)
              ·
                refine ⟨1100430881749680646010821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 23475858810659853781564181 1100430881749680646010821)
                ·
                  refine ⟨206330790328065121127029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1100430881749680646010821 206330790328065121127029)
                  ·
                    rfl

theorem cell22_1808225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 6, 4].length) (baseStart_1808225 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1808225 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1808225 prefixEnd_1808225 := by exact prefixLift 1808225
  have htrace : WordTrace (prefixWord ++ tailWord_1808225) baseStart_1808225 baseEnd_1808225 := by
    simpa [prefixWord, tailWord_1808225, baseEnd_1808225] using wordTrace_append hprefix tailTrace_1808225
  have hstable : (prefixWord ++ tailWord_1808225).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1808225).length < 2 ^ (prefixWord ++ tailWord_1808225).sum := by decide
  have hdescent : baseEnd_1808225 < baseStart_1808225 := by decide
  rcases family_descends (prefixWord ++ tailWord_1808225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1808332 : List Nat := [2, 2, 1, 4, 1, 3, 2, 2, 5]
def baseStart_1808332 : Nat := 118140960795 + 1808332 * 2 ^ 59
def prefixEnd_1808332 : Nat := 4983230072969 + 3 ^ 40 * 1808332 * 2
def baseEnd_1808332 : Nat := 206342999756960916985253

theorem tailTrace_1808332 : CollatzResearch.WordTrace tailWord_1808332 prefixEnd_1808332 206342999756960916985253 := by
  unfold tailWord_1808332
  simp only [CollatzResearch.WordTrace]
  refine ⟨32977643242364738681409625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43970190989819651575212833 32977643242364738681409625)
  ·
    refine ⟨24733232431773554011057219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32977643242364738681409625 24733232431773554011057219)
    ·
      refine ⟨37099848647660331016585829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24733232431773554011057219 37099848647660331016585829)
      ·
        refine ⟨6956221621436312065609843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37099848647660331016585829 6956221621436312065609843)
        ·
          refine ⟨10434332432154468098414765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6956221621436312065609843 10434332432154468098414765)
          ·
            refine ⟨3912874662057925536905537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10434332432154468098414765 3912874662057925536905537)
            ·
              refine ⟨2934655996543444152679153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3912874662057925536905537 2934655996543444152679153)
              ·
                refine ⟨2200991997407583114509365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2934655996543444152679153 2200991997407583114509365)
                ·
                  refine ⟨206342999756960916985253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2200991997407583114509365 206342999756960916985253)
                  ·
                    rfl

theorem cell22_1808332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 2, 2, 5].length) (baseStart_1808332 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1808332 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1808332 prefixEnd_1808332 := by exact prefixLift 1808332
  have htrace : WordTrace (prefixWord ++ tailWord_1808332) baseStart_1808332 baseEnd_1808332 := by
    simpa [prefixWord, tailWord_1808332, baseEnd_1808332] using wordTrace_append hprefix tailTrace_1808332
  have hstable : (prefixWord ++ tailWord_1808332).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1808332).length < 2 ^ (prefixWord ++ tailWord_1808332).sum := by decide
  have hdescent : baseEnd_1808332 < baseStart_1808332 := by decide
  rcases family_descends (prefixWord ++ tailWord_1808332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1808362 : List Nat := [3, 1, 3, 1, 2, 1, 2, 4, 1, 4]
def baseStart_1808362 : Nat := 118140960795 + 1808362 * 2 ^ 59
def prefixEnd_1808362 : Nat := 4983230072969 + 3 ^ 40 * 1808362 * 2
def baseEnd_1808362 : Nat := 619039268883972672705667

theorem tailTrace_1808362 : CollatzResearch.WordTrace tailWord_1808362 prefixEnd_1808362 619039268883972672705667 := by
  unfold tailWord_1808362
  simp only [CollatzResearch.WordTrace]
  refine ⟨16489095168655198121602835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43970920449747194990940893 16489095168655198121602835)
  ·
    refine ⟨24733642752982797182404253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16489095168655198121602835 24733642752982797182404253)
    ·
      refine ⟨9275116032368548943401595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24733642752982797182404253 9275116032368548943401595)
      ·
        refine ⟨13912674048552823415102393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9275116032368548943401595 13912674048552823415102393)
        ·
          refine ⟨10434505536414617561326795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13912674048552823415102393 10434505536414617561326795)
          ·
            refine ⟨15651758304621926341990193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10434505536414617561326795 15651758304621926341990193)
            ·
              refine ⟨11738818728466444756492645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15651758304621926341990193 11738818728466444756492645)
              ·
                refine ⟨2201028511587458391842371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11738818728466444756492645 2201028511587458391842371)
                ·
                  refine ⟨3301542767381187587763557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2201028511587458391842371 3301542767381187587763557)
                  ·
                    refine ⟨619039268883972672705667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3301542767381187587763557 619039268883972672705667)
                    ·
                      rfl

theorem cell22_1808362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 4, 1, 4].length) (baseStart_1808362 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1808362 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1808362 prefixEnd_1808362 := by exact prefixLift 1808362
  have htrace : WordTrace (prefixWord ++ tailWord_1808362) baseStart_1808362 baseEnd_1808362 := by
    simpa [prefixWord, tailWord_1808362, baseEnd_1808362] using wordTrace_append hprefix tailTrace_1808362
  have hstable : (prefixWord ++ tailWord_1808362).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1808362).length < 2 ^ (prefixWord ++ tailWord_1808362).sum := by decide
  have hdescent : baseEnd_1808362 < baseStart_1808362 := by decide
  rcases family_descends (prefixWord ++ tailWord_1808362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1808377 : List Nat := [1, 2, 1, 3, 1, 4, 1, 5, 4]
def baseStart_1808377 : Nat := 118140960795 + 1808377 * 2 ^ 59
def prefixEnd_1808377 : Nat := 4983230072969 + 3 ^ 40 * 1808377 * 2
def baseEnd_1808377 : Nat := 206348134563505877860207

theorem tailTrace_1808377 : CollatzResearch.WordTrace tailWord_1808377 prefixEnd_1808377 206348134563505877860207 := by
  unfold tailWord_1808377
  simp only [CollatzResearch.WordTrace]
  refine ⟨65956927769566450048207385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43971285179710966698804923 65956927769566450048207385)
  ·
    refine ⟨49467695827174837536155539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65956927769566450048207385 49467695827174837536155539)
    ·
      refine ⟨74201543740762256304233309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49467695827174837536155539 74201543740762256304233309)
      ·
        refine ⟨27825578902785846114087491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74201543740762256304233309 27825578902785846114087491)
        ·
          refine ⟨41738368354178769171131237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27825578902785846114087491 41738368354178769171131237)
          ·
            refine ⟨7825944066408519219587107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41738368354178769171131237 7825944066408519219587107)
            ·
              refine ⟨11738916099612778829380661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7825944066408519219587107 11738916099612778829380661)
              ·
                refine ⟨1100523384338698015254437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11738916099612778829380661 1100523384338698015254437)
                ·
                  refine ⟨206348134563505877860207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1100523384338698015254437 206348134563505877860207)
                  ·
                    rfl

theorem cell22_1808377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 5, 4].length) (baseStart_1808377 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1808377 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1808377 prefixEnd_1808377 := by exact prefixLift 1808377
  have htrace : WordTrace (prefixWord ++ tailWord_1808377) baseStart_1808377 baseEnd_1808377 := by
    simpa [prefixWord, tailWord_1808377, baseEnd_1808377] using wordTrace_append hprefix tailTrace_1808377
  have hstable : (prefixWord ++ tailWord_1808377).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1808377).length < 2 ^ (prefixWord ++ tailWord_1808377).sum := by decide
  have hdescent : baseEnd_1808377 < baseStart_1808377 := by decide
  rcases family_descends (prefixWord ++ tailWord_1808377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1808392 : List Nat := [2, 1, 3, 2, 1, 2, 3, 1, 4, 3]
def baseStart_1808392 : Nat := 118140960795 + 1808392 * 2 ^ 59
def prefixEnd_1808392 : Nat := 4983230072969 + 3 ^ 40 * 1808392 * 2
def baseEnd_1808392 : Nat := 619049538497062594455575

theorem tailTrace_1808392 : CollatzResearch.WordTrace tailWord_1808392 prefixEnd_1808392 619049538497062594455575 := by
  unfold tailWord_1808392
  simp only [CollatzResearch.WordTrace]
  refine ⟨32978737432256053805001715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43971649909674738406668953 32978737432256053805001715)
  ·
    refine ⟨49468106148384080707502573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32978737432256053805001715 49468106148384080707502573)
    ·
      refine ⟨18550539805644030265313465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49468106148384080707502573 18550539805644030265313465)
      ·
        refine ⟨13912904854233022698985099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18550539805644030265313465 13912904854233022698985099)
        ·
          refine ⟨20869357281349534048477649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13912904854233022698985099 20869357281349534048477649)
          ·
            refine ⟨15652017961012150536358237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20869357281349534048477649 15652017961012150536358237)
            ·
              refine ⟨5869506735379556451134339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15652017961012150536358237 5869506735379556451134339)
              ·
                refine ⟨8804260103069334676701509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5869506735379556451134339 8804260103069334676701509)
                ·
                  refine ⟨1650798769325500251881533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8804260103069334676701509 1650798769325500251881533)
                  ·
                    refine ⟨619049538497062594455575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1650798769325500251881533 619049538497062594455575)
                    ·
                      rfl

theorem cell22_1808392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 3, 1, 4, 3].length) (baseStart_1808392 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1808392 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1808392 prefixEnd_1808392 := by exact prefixLift 1808392
  have htrace : WordTrace (prefixWord ++ tailWord_1808392) baseStart_1808392 baseEnd_1808392 := by
    simpa [prefixWord, tailWord_1808392, baseEnd_1808392] using wordTrace_append hprefix tailTrace_1808392
  have hstable : (prefixWord ++ tailWord_1808392).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1808392).length < 2 ^ (prefixWord ++ tailWord_1808392).sum := by decide
  have hdescent : baseEnd_1808392 < baseStart_1808392 := by decide
  rcases family_descends (prefixWord ++ tailWord_1808392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1808437 : List Nat := [1, 3, 3, 1, 1, 1, 2, 2, 5, 3]
def baseStart_1808437 : Nat := 118140960795 + 1808437 * 2 ^ 59
def prefixEnd_1808437 : Nat := 4983230072969 + 3 ^ 40 * 1808437 * 2
def baseEnd_1808437 : Nat := 619064942916697477080437

theorem tailTrace_1808437 : CollatzResearch.WordTrace tailWord_1808437 prefixEnd_1808437 619064942916697477080437 := by
  unfold tailWord_1808437
  simp only [CollatzResearch.WordTrace]
  refine ⟨65959116149349080295391565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43972744099566053530261043 65959116149349080295391565)
  ·
    refine ⟨24734668556005905110771837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65959116149349080295391565 24734668556005905110771837)
    ·
      refine ⟨9275500708502214416539439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24734668556005905110771837 9275500708502214416539439)
      ·
        refine ⟨13913251062753321624809159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9275500708502214416539439 13913251062753321624809159)
        ·
          refine ⟨20869876594129982437213739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13913251062753321624809159 20869876594129982437213739)
          ·
            refine ⟨31304814891194973655820609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20869876594129982437213739 31304814891194973655820609)
            ·
              refine ⟨23478611168396230241865457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31304814891194973655820609 23478611168396230241865457)
              ·
                refine ⟨17608958376297172681399093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23478611168396230241865457 17608958376297172681399093)
                ·
                  refine ⟨1650839847777859938881165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 17608958376297172681399093 1650839847777859938881165)
                  ·
                    refine ⟨619064942916697477080437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1650839847777859938881165 619064942916697477080437)
                    ·
                      rfl

theorem cell22_1808437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 2, 5, 3].length) (baseStart_1808437 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1808437 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1808437 prefixEnd_1808437 := by exact prefixLift 1808437
  have htrace : WordTrace (prefixWord ++ tailWord_1808437) baseStart_1808437 baseEnd_1808437 := by
    simpa [prefixWord, tailWord_1808437, baseEnd_1808437] using wordTrace_append hprefix tailTrace_1808437
  have hstable : (prefixWord ++ tailWord_1808437).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1808437).length < 2 ^ (prefixWord ++ tailWord_1808437).sum := by decide
  have hdescent : baseEnd_1808437 < baseStart_1808437 := by decide
  rcases family_descends (prefixWord ++ tailWord_1808437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1808465 : List Nat := [1, 2, 2, 1, 3, 1, 1, 3, 1, 7]
def baseStart_1808465 : Nat := 118140960795 + 1808465 * 2 ^ 59
def prefixEnd_1808465 : Nat := 4983230072969 + 3 ^ 40 * 1808465 * 2
def baseEnd_1808465 : Nat := 619074527888914737380351

theorem tailTrace_1808465 : CollatzResearch.WordTrace tailWord_1808465 prefixEnd_1808465 619074527888914737380351 := by
  unfold tailWord_1808465
  simp only [CollatzResearch.WordTrace]
  refine ⟨65960137393247641077410849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43973424928831760718273899 65960137393247641077410849)
  ·
    refine ⟨49470103044935730808058137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65960137393247641077410849 49470103044935730808058137)
    ·
      refine ⟨37102577283701798106043603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49470103044935730808058137 37102577283701798106043603)
      ·
        refine ⟨55653865925552697159065405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37102577283701798106043603 55653865925552697159065405)
        ·
          refine ⟨20870199722082261434649527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55653865925552697159065405 20870199722082261434649527)
          ·
            refine ⟨31305299583123392151974291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20870199722082261434649527 31305299583123392151974291)
            ·
              refine ⟨46957949374685088227961437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31305299583123392151974291 46957949374685088227961437)
              ·
                refine ⟨17609231015506908085485539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46957949374685088227961437 17609231015506908085485539)
                ·
                  refine ⟨26413846523260362128228309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17609231015506908085485539 26413846523260362128228309)
                  ·
                    refine ⟨619074527888914737380351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 26413846523260362128228309 619074527888914737380351)
                    ·
                      rfl

theorem cell22_1808465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 3, 1, 7].length) (baseStart_1808465 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1808465 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1808465 prefixEnd_1808465 := by exact prefixLift 1808465
  have htrace : WordTrace (prefixWord ++ tailWord_1808465) baseStart_1808465 baseEnd_1808465 := by
    simpa [prefixWord, tailWord_1808465, baseEnd_1808465] using wordTrace_append hprefix tailTrace_1808465
  have hstable : (prefixWord ++ tailWord_1808465).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1808465).length < 2 ^ (prefixWord ++ tailWord_1808465).sum := by decide
  have hdescent : baseEnd_1808465 < baseStart_1808465 := by decide
  rcases family_descends (prefixWord ++ tailWord_1808465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1808546 : List Nat := [3, 3, 1, 3, 1, 1, 1, 5, 4]
def baseStart_1808546 : Nat := 118140960795 + 1808546 * 2 ^ 59
def prefixEnd_1808546 : Nat := 4983230072969 + 3 ^ 40 * 1808546 * 2
def baseEnd_1808546 : Nat := 206367418614752508701701

theorem tailTrace_1808546 : CollatzResearch.WordTrace tailWord_1808546 prefixEnd_1808546 206367418614752508701701 := by
  unfold tailWord_1808546
  simp only [CollatzResearch.WordTrace]
  refine ⟨16490772926488547977777373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43975394470636127940739661 16490772926488547977777373)
  ·
    refine ⟨6184039847433205491666515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16490772926488547977777373 6184039847433205491666515)
    ·
      refine ⟨9276059771149808237499773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6184039847433205491666515 9276059771149808237499773)
      ·
        refine ⟨3478522414181178089062415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9276059771149808237499773 3478522414181178089062415)
        ·
          refine ⟨5217783621271767133593623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3478522414181178089062415 5217783621271767133593623)
          ·
            refine ⟨7826675431907650700390435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5217783621271767133593623 7826675431907650700390435)
            ·
              refine ⟨11740013147861476050585653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7826675431907650700390435 11740013147861476050585653)
              ·
                refine ⟨1100626232612013379742405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11740013147861476050585653 1100626232612013379742405)
                ·
                  refine ⟨206367418614752508701701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1100626232612013379742405 206367418614752508701701)
                  ·
                    rfl

theorem cell22_1808546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 5, 4].length) (baseStart_1808546 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1808546 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1808546 prefixEnd_1808546 := by exact prefixLift 1808546
  have htrace : WordTrace (prefixWord ++ tailWord_1808546) baseStart_1808546 baseEnd_1808546 := by
    simpa [prefixWord, tailWord_1808546, baseEnd_1808546] using wordTrace_append hprefix tailTrace_1808546
  have hstable : (prefixWord ++ tailWord_1808546).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1808546).length < 2 ^ (prefixWord ++ tailWord_1808546).sum := by decide
  have hdescent : baseEnd_1808546 < baseStart_1808546 := by decide
  rcases family_descends (prefixWord ++ tailWord_1808546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1808548 : List Nat := [2, 3, 1, 2, 4, 2, 2, 1, 1, 4]
def baseStart_1808548 : Nat := 118140960795 + 1808548 * 2 ^ 59
def prefixEnd_1808548 : Nat := 4983230072969 + 3 ^ 40 * 1808548 * 2
def baseEnd_1808548 : Nat := 619102940485130187555097

theorem tailTrace_1808548 : CollatzResearch.WordTrace tailWord_1808548 prefixEnd_1808548 619102940485130187555097 := by
  unfold tailWord_1808548
  simp only [CollatzResearch.WordTrace]
  refine ⟨32981582325973473126341149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43975443101297964168454865 32981582325973473126341149)
  ·
    refine ⟨12368093372240052422377931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32981582325973473126341149 12368093372240052422377931)
    ·
      refine ⟨18552140058360078633566897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12368093372240052422377931 18552140058360078633566897)
      ·
        refine ⟨13914105043770058975175173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18552140058360078633566897 13914105043770058975175173)
        ·
          refine ⟨2608894695706886057845345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13914105043770058975175173 2608894695706886057845345)
          ·
            refine ⟨1956671021780164543384009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2608894695706886057845345 1956671021780164543384009)
            ·
              refine ⟨1467503266335123407538007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1956671021780164543384009 1467503266335123407538007)
              ·
                refine ⟨2201254899502685111307011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1467503266335123407538007 2201254899502685111307011)
                ·
                  refine ⟨3301882349254027666960517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2201254899502685111307011 3301882349254027666960517)
                  ·
                    refine ⟨619102940485130187555097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3301882349254027666960517 619102940485130187555097)
                    ·
                      rfl

theorem cell22_1808548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 2, 2, 1, 1, 4].length) (baseStart_1808548 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1808548 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1808548 prefixEnd_1808548 := by exact prefixLift 1808548
  have htrace : WordTrace (prefixWord ++ tailWord_1808548) baseStart_1808548 baseEnd_1808548 := by
    simpa [prefixWord, tailWord_1808548, baseEnd_1808548] using wordTrace_append hprefix tailTrace_1808548
  have hstable : (prefixWord ++ tailWord_1808548).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1808548).length < 2 ^ (prefixWord ++ tailWord_1808548).sum := by decide
  have hdescent : baseEnd_1808548 < baseStart_1808548 := by decide
  rcases family_descends (prefixWord ++ tailWord_1808548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1808561 : List Nat := [1, 2, 2, 5, 2, 1, 1, 1, 4, 3]
def baseStart_1808561 : Nat := 118140960795 + 1808561 * 2 ^ 59
def prefixEnd_1808561 : Nat := 4983230072969 + 3 ^ 40 * 1808561 * 2
def baseEnd_1808561 : Nat := 619107390650802486980057

theorem tailTrace_1808561 : CollatzResearch.WordTrace tailWord_1808561 prefixEnd_1808561 619107390650802486980057 := by
  unfold tailWord_1808561
  simp only [CollatzResearch.WordTrace]
  refine ⟨65963638800899849472905537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43975759200599899648603691 65963638800899849472905537)
  ·
    refine ⟨49472729100674887104679153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65963638800899849472905537 49472729100674887104679153)
    ·
      refine ⟨37104546825506165328509365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49472729100674887104679153 37104546825506165328509365)
      ·
        refine ⟨3478551264891202999547753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 37104546825506165328509365 3478551264891202999547753)
        ·
          refine ⟨2608913448668402249660815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3478551264891202999547753 2608913448668402249660815)
          ·
            refine ⟨3913370173002603374491223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2608913448668402249660815 3913370173002603374491223)
            ·
              refine ⟨5870055259503905061736835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3913370173002603374491223 5870055259503905061736835)
              ·
                refine ⟨8805082889255857592605253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5870055259503905061736835 8805082889255857592605253)
                ·
                  refine ⟨1650953041735473298613485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8805082889255857592605253 1650953041735473298613485)
                  ·
                    refine ⟨619107390650802486980057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1650953041735473298613485 619107390650802486980057)
                    ·
                      rfl

theorem cell22_1808561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 1, 1, 4, 3].length) (baseStart_1808561 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1808561 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1808561 prefixEnd_1808561 := by exact prefixLift 1808561
  have htrace : WordTrace (prefixWord ++ tailWord_1808561) baseStart_1808561 baseEnd_1808561 := by
    simpa [prefixWord, tailWord_1808561, baseEnd_1808561] using wordTrace_append hprefix tailTrace_1808561
  have hstable : (prefixWord ++ tailWord_1808561).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1808561).length < 2 ^ (prefixWord ++ tailWord_1808561).sum := by decide
  have hdescent : baseEnd_1808561 < baseStart_1808561 := by decide
  rcases family_descends (prefixWord ++ tailWord_1808561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1808578 : List Nat := [3, 5, 1, 1, 1, 1, 3, 1, 1, 5]
def baseStart_1808578 : Nat := 118140960795 + 1808578 * 2 ^ 59
def prefixEnd_1808578 : Nat := 4983230072969 + 3 ^ 40 * 1808578 * 2
def baseEnd_1808578 : Nat := 619113210098220109305005

theorem tailTrace_1808578 : CollatzResearch.WordTrace tailWord_1808578 prefixEnd_1808578 619113210098220109305005 := by
  unfold tailWord_1808578
  simp only [CollatzResearch.WordTrace]
  refine ⟨16491064710459565344068597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43976172561225507584182925 16491064710459565344068597)
  ·
    refine ⟨1546037316605584251006431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 16491064710459565344068597 1546037316605584251006431)
    ·
      refine ⟨2319055974908376376509647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1546037316605584251006431 2319055974908376376509647)
      ·
        refine ⟨3478583962362564564764471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2319055974908376376509647 3478583962362564564764471)
        ·
          refine ⟨5217875943543846847146707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3478583962362564564764471 5217875943543846847146707)
          ·
            refine ⟨7826813915315770270720061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5217875943543846847146707 7826813915315770270720061)
            ·
              refine ⟨2935055218243413851520023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7826813915315770270720061 2935055218243413851520023)
              ·
                refine ⟨4402582827365120777280035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2935055218243413851520023 4402582827365120777280035)
                ·
                  refine ⟨6603874241047681165920053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4402582827365120777280035 6603874241047681165920053)
                  ·
                    refine ⟨619113210098220109305005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6603874241047681165920053 619113210098220109305005)
                    ·
                      rfl

theorem cell22_1808578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 3, 1, 1, 5].length) (baseStart_1808578 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1808578 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1808578 prefixEnd_1808578 := by exact prefixLift 1808578
  have htrace : WordTrace (prefixWord ++ tailWord_1808578) baseStart_1808578 baseEnd_1808578 := by
    simpa [prefixWord, tailWord_1808578, baseEnd_1808578] using wordTrace_append hprefix tailTrace_1808578
  have hstable : (prefixWord ++ tailWord_1808578).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1808578).length < 2 ^ (prefixWord ++ tailWord_1808578).sum := by decide
  have hdescent : baseEnd_1808578 < baseStart_1808578 := by decide
  rcases family_descends (prefixWord ++ tailWord_1808578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1808602 : List Nat := [3, 1, 1, 2, 2, 1, 3, 2, 7]
def baseStart_1808602 : Nat := 118140960795 + 1808602 * 2 ^ 59
def prefixEnd_1808602 : Nat := 4983230072969 + 3 ^ 40 * 1808602 * 2
def baseEnd_1808602 : Nat := 206373808596230682234977

theorem tailTrace_1808602 : CollatzResearch.WordTrace tailWord_1808602 prefixEnd_1808602 206373808596230682234977 := by
  unfold tailWord_1808602
  simp only [CollatzResearch.WordTrace]
  refine ⟨16491283548437828368787015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43976756129167542316765373 16491283548437828368787015)
  ·
    refine ⟨24736925322656742553180523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16491283548437828368787015 24736925322656742553180523)
    ·
      refine ⟨37105387983985113829770785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24736925322656742553180523 37105387983985113829770785)
      ·
        refine ⟨27829040987988835372328089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37105387983985113829770785 27829040987988835372328089)
        ·
          refine ⟨20871780740991626529246067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27829040987988835372328089 20871780740991626529246067)
          ·
            refine ⟨31307671111487439793869101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20871780740991626529246067 31307671111487439793869101)
            ·
              refine ⟨11740376666807789922700913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31307671111487439793869101 11740376666807789922700913)
              ·
                refine ⟨8805282500105842442025685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11740376666807789922700913 8805282500105842442025685)
                ·
                  refine ⟨206373808596230682234977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8805282500105842442025685 206373808596230682234977)
                  ·
                    rfl

theorem cell22_1808602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 2, 7].length) (baseStart_1808602 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1808602 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1808602 prefixEnd_1808602 := by exact prefixLift 1808602
  have htrace : WordTrace (prefixWord ++ tailWord_1808602) baseStart_1808602 baseEnd_1808602 := by
    simpa [prefixWord, tailWord_1808602, baseEnd_1808602] using wordTrace_append hprefix tailTrace_1808602
  have hstable : (prefixWord ++ tailWord_1808602).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1808602).length < 2 ^ (prefixWord ++ tailWord_1808602).sum := by decide
  have hdescent : baseEnd_1808602 < baseStart_1808602 := by decide
  rcases family_descends (prefixWord ++ tailWord_1808602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1808610 : List Nat := [3, 3, 4, 1, 1, 1, 1, 2, 2, 4]
def baseStart_1808610 : Nat := 118140960795 + 1808610 * 2 ^ 59
def prefixEnd_1808610 : Nat := 4983230072969 + 3 ^ 40 * 1808610 * 2
def baseEnd_1808610 : Nat := 619124164352182692504907

theorem tailTrace_1808610 : CollatzResearch.WordTrace tailWord_1808610 prefixEnd_1808610 619124164352182692504907 := by
  unfold tailWord_1808610
  simp only [CollatzResearch.WordTrace]
  refine ⟨16491356494430582710359821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43976950651814887227626189 16491356494430582710359821)
  ·
    refine ⟨6184258685411468516384933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16491356494430582710359821 6184258685411468516384933)
    ·
      refine ⟨1159548503514650346822175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6184258685411468516384933 1159548503514650346822175)
      ·
        refine ⟨1739322755271975520233263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1159548503514650346822175 1739322755271975520233263)
        ·
          refine ⟨2608984132907963280349895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1739322755271975520233263 2608984132907963280349895)
          ·
            refine ⟨3913476199361944920524843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2608984132907963280349895 3913476199361944920524843)
            ·
              refine ⟨5870214299042917380787265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3913476199361944920524843 5870214299042917380787265)
              ·
                refine ⟨4402660724282188035590449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5870214299042917380787265 4402660724282188035590449)
                ·
                  refine ⟨3301995543211641026692837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4402660724282188035590449 3301995543211641026692837)
                  ·
                    refine ⟨619124164352182692504907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3301995543211641026692837 619124164352182692504907)
                    ·
                      rfl

theorem cell22_1808610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 1, 2, 2, 4].length) (baseStart_1808610 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1808610 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1808610 prefixEnd_1808610 := by exact prefixLift 1808610
  have htrace : WordTrace (prefixWord ++ tailWord_1808610) baseStart_1808610 baseEnd_1808610 := by
    simpa [prefixWord, tailWord_1808610, baseEnd_1808610] using wordTrace_append hprefix tailTrace_1808610
  have hstable : (prefixWord ++ tailWord_1808610).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1808610).length < 2 ^ (prefixWord ++ tailWord_1808610).sum := by decide
  have hdescent : baseEnd_1808610 < baseStart_1808610 := by decide
  rcases family_descends (prefixWord ++ tailWord_1808610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1808636 : List Nat := [2, 2, 2, 1, 4, 1, 4, 1, 5]
def baseStart_1808636 : Nat := 118140960795 + 1808636 * 2 ^ 59
def prefixEnd_1808636 : Nat := 4983230072969 + 3 ^ 40 * 1808636 * 2
def baseEnd_1808636 : Nat := 206377688227842430451609

theorem tailTrace_1808636 : CollatzResearch.WordTrace tailWord_1808636 prefixEnd_1808636 206377688227842430451609 := by
  unfold tailWord_1808636
  simp only [CollatzResearch.WordTrace]
  refine ⟨32983187137814068640942881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43977582850418758187923841 32983187137814068640942881)
  ·
    refine ⟨24737390353360551480707161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32983187137814068640942881 24737390353360551480707161)
    ·
      refine ⟨18553042765020413610530371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24737390353360551480707161 18553042765020413610530371)
      ·
        refine ⟨27829564147530620415795557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18553042765020413610530371 27829564147530620415795557)
        ·
          refine ⟨5218043277661991327961667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27829564147530620415795557 5218043277661991327961667)
          ·
            refine ⟨7827064916492986991942501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5218043277661991327961667 7827064916492986991942501)
            ·
              refine ⟨1467574671842435060989219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7827064916492986991942501 1467574671842435060989219)
              ·
                refine ⟨2201362007763652591483829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1467574671842435060989219 2201362007763652591483829)
                ·
                  refine ⟨206377688227842430451609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2201362007763652591483829 206377688227842430451609)
                  ·
                    rfl

theorem cell22_1808636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 4, 1, 5].length) (baseStart_1808636 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1808636 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1808636 prefixEnd_1808636 := by exact prefixLift 1808636
  have htrace : WordTrace (prefixWord ++ tailWord_1808636) baseStart_1808636 baseEnd_1808636 := by
    simpa [prefixWord, tailWord_1808636, baseEnd_1808636] using wordTrace_append hprefix tailTrace_1808636
  have hstable : (prefixWord ++ tailWord_1808636).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1808636).length < 2 ^ (prefixWord ++ tailWord_1808636).sum := by decide
  have hdescent : baseEnd_1808636 < baseStart_1808636 := by decide
  rcases family_descends (prefixWord ++ tailWord_1808636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1808649 : List Nat := [1, 2, 1, 1, 3, 5, 1, 1, 3, 4]
def baseStart_1808649 : Nat := 118140960795 + 1808649 * 2 ^ 59
def prefixEnd_1808649 : Nat := 4983230072969 + 3 ^ 40 * 1808649 * 2
def baseEnd_1808649 : Nat := 619137514849199590779787

theorem tailTrace_1808649 : CollatzResearch.WordTrace tailWord_1808649 prefixEnd_1808649 619137514849199590779787 := by
  unfold tailWord_1808649
  simp only [CollatzResearch.WordTrace]
  refine ⟨65966848424581040502109001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43977898949720693668072667 65966848424581040502109001)
  ·
    refine ⟨49475136318435780376581751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65966848424581040502109001 49475136318435780376581751)
    ·
      refine ⟨74212704477653670564872627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49475136318435780376581751 74212704477653670564872627)
      ·
        refine ⟨111319056716480505847308941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74212704477653670564872627 111319056716480505847308941)
        ·
          refine ⟨41744646268680189692740853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111319056716480505847308941 41744646268680189692740853)
          ·
            refine ⟨3913560587688767783694455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 41744646268680189692740853 3913560587688767783694455)
            ·
              refine ⟨5870340881533151675541683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3913560587688767783694455 5870340881533151675541683)
              ·
                refine ⟨8805511322299727513312525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5870340881533151675541683 8805511322299727513312525)
                ·
                  refine ⟨3302066745862397817492197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8805511322299727513312525 3302066745862397817492197)
                  ·
                    refine ⟨619137514849199590779787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3302066745862397817492197 619137514849199590779787)
                    ·
                      rfl

theorem cell22_1808649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 1, 1, 3, 4].length) (baseStart_1808649 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1808649 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1808649 prefixEnd_1808649 := by exact prefixLift 1808649
  have htrace : WordTrace (prefixWord ++ tailWord_1808649) baseStart_1808649 baseEnd_1808649 := by
    simpa [prefixWord, tailWord_1808649, baseEnd_1808649] using wordTrace_append hprefix tailTrace_1808649
  have hstable : (prefixWord ++ tailWord_1808649).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1808649).length < 2 ^ (prefixWord ++ tailWord_1808649).sum := by decide
  have hdescent : baseEnd_1808649 < baseStart_1808649 := by decide
  rcases family_descends (prefixWord ++ tailWord_1808649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1808696 : List Nat := [2, 1, 2, 1, 3, 1, 4, 3, 2, 3]
def baseStart_1808696 : Nat := 118140960795 + 1808696 * 2 ^ 59
def prefixEnd_1808696 : Nat := 4983230072969 + 3 ^ 40 * 1808696 * 2
def baseEnd_1808696 : Nat := 619153603909707134854643

theorem tailTrace_1808696 : CollatzResearch.WordTrace tailWord_1808696 prefixEnd_1808696 619153603909707134854643 := by
  unfold tailWord_1808696
  simp only [CollatzResearch.WordTrace]
  refine ⟨32984281327705383764534971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43979041770273845019379961 32984281327705383764534971)
  ·
    refine ⟨49476421991558075646802457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32984281327705383764534971 49476421991558075646802457)
    ·
      refine ⟨37107316493668556735101843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49476421991558075646802457 37107316493668556735101843)
      ·
        refine ⟨55660974740502835102652765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37107316493668556735101843 55660974740502835102652765)
        ·
          refine ⟨20872865527688563163494787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55660974740502835102652765 20872865527688563163494787)
          ·
            refine ⟨31309298291532844745242181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20872865527688563163494787 31309298291532844745242181)
            ·
              refine ⟨5870493429662408389732909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31309298291532844745242181 5870493429662408389732909)
              ·
                refine ⟨2201435036123403146149841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5870493429662408389732909 2201435036123403146149841)
                ·
                  refine ⟨1651076277092552359612381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2201435036123403146149841 1651076277092552359612381)
                  ·
                    refine ⟨619153603909707134854643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1651076277092552359612381 619153603909707134854643)
                    ·
                      rfl

theorem cell22_1808696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 4, 3, 2, 3].length) (baseStart_1808696 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1808696 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1808696 prefixEnd_1808696 := by exact prefixLift 1808696
  have htrace : WordTrace (prefixWord ++ tailWord_1808696) baseStart_1808696 baseEnd_1808696 := by
    simpa [prefixWord, tailWord_1808696, baseEnd_1808696] using wordTrace_append hprefix tailTrace_1808696
  have hstable : (prefixWord ++ tailWord_1808696).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1808696).length < 2 ^ (prefixWord ++ tailWord_1808696).sum := by decide
  have hdescent : baseEnd_1808696 < baseStart_1808696 := by decide
  rcases family_descends (prefixWord ++ tailWord_1808696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1808741 : List Nat := [1, 3, 1, 3, 1, 3, 1, 3, 3, 3]
def baseStart_1808741 : Nat := 118140960795 + 1808741 * 2 ^ 59
def prefixEnd_1808741 : Nat := 4983230072969 + 3 ^ 40 * 1808741 * 2
def baseEnd_1808741 : Nat := 619169008329342017479505

theorem tailTrace_1808741 : CollatzResearch.WordTrace tailWord_1808741 prefixEnd_1808741 619169008329342017479505 := by
  unfold tailWord_1808741
  simp only [CollatzResearch.WordTrace]
  refine ⟨65970203940247740214458077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43980135960165160142972051 65970203940247740214458077)
  ·
    refine ⟨24738826477592902580421779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65970203940247740214458077 24738826477592902580421779)
    ·
      refine ⟨37108239716389353870632669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24738826477592902580421779 37108239716389353870632669)
      ·
        refine ⟨13915589893646007701487251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37108239716389353870632669 13915589893646007701487251)
        ·
          refine ⟨20873384840469011552230877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13915589893646007701487251 20873384840469011552230877)
          ·
            refine ⟨7827519315175879332086579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20873384840469011552230877 7827519315175879332086579)
            ·
              refine ⟨11741278972763818998129869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7827519315175879332086579 11741278972763818998129869)
              ·
                refine ⟨4402979614786432124298701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11741278972763818998129869 4402979614786432124298701)
                ·
                  refine ⟨1651117355544912046612013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4402979614786432124298701 1651117355544912046612013)
                  ·
                    refine ⟨619169008329342017479505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1651117355544912046612013 619169008329342017479505)
                    ·
                      rfl

theorem cell22_1808741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 3, 3, 3].length) (baseStart_1808741 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1808741 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1808741 prefixEnd_1808741 := by exact prefixLift 1808741
  have htrace : WordTrace (prefixWord ++ tailWord_1808741) baseStart_1808741 baseEnd_1808741 := by
    simpa [prefixWord, tailWord_1808741, baseEnd_1808741] using wordTrace_append hprefix tailTrace_1808741
  have hstable : (prefixWord ++ tailWord_1808741).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1808741).length < 2 ^ (prefixWord ++ tailWord_1808741).sum := by decide
  have hdescent : baseEnd_1808741 < baseStart_1808741 := by decide
  rcases family_descends (prefixWord ++ tailWord_1808741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1808792 : List Nat := [2, 1, 2, 5, 1, 2, 3, 2, 1, 3]
def baseStart_1808792 : Nat := 118140960795 + 1808792 * 2 ^ 59
def prefixEnd_1808792 : Nat := 4983230072969 + 3 ^ 40 * 1808792 * 2
def baseEnd_1808792 : Nat := 619186466671594884454349

theorem tailTrace_1808792 : CollatzResearch.WordTrace tailWord_1808792 prefixEnd_1808792 619186466671594884454349 := by
  unfold tailWord_1808792
  simp only [CollatzResearch.WordTrace]
  refine ⟨32986032031531487962282315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43981376042041983949709753 32986032031531487962282315)
  ·
    refine ⟨49479048047297231943423473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32986032031531487962282315 49479048047297231943423473)
    ·
      refine ⟨37109286035472923957567605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49479048047297231943423473 37109286035472923957567605)
      ·
        refine ⟨3478995565825586621021963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 37109286035472923957567605 3478995565825586621021963)
        ·
          refine ⟨5218493348738379931532945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3478995565825586621021963 5218493348738379931532945)
          ·
            refine ⟨3913870011553784948649709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5218493348738379931532945 3913870011553784948649709)
            ·
              refine ⟨1467701254332669355743641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3913870011553784948649709 1467701254332669355743641)
              ·
                refine ⟨1100775940749502016807731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1467701254332669355743641 1100775940749502016807731)
                ·
                  refine ⟨1651163911124253025211597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1100775940749502016807731 1651163911124253025211597)
                  ·
                    refine ⟨619186466671594884454349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1651163911124253025211597 619186466671594884454349)
                    ·
                      rfl

theorem cell22_1808792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 3, 2, 1, 3].length) (baseStart_1808792 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1808792 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1808792 prefixEnd_1808792 := by exact prefixLift 1808792
  have htrace : WordTrace (prefixWord ++ tailWord_1808792) baseStart_1808792 baseEnd_1808792 := by
    simpa [prefixWord, tailWord_1808792, baseEnd_1808792] using wordTrace_append hprefix tailTrace_1808792
  have hstable : (prefixWord ++ tailWord_1808792).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1808792).length < 2 ^ (prefixWord ++ tailWord_1808792).sum := by decide
  have hdescent : baseEnd_1808792 < baseStart_1808792 := by decide
  rcases family_descends (prefixWord ++ tailWord_1808792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1808844 : List Nat := [2, 2, 1, 4, 13]
def baseStart_1808844 : Nat := 118140960795 + 1808844 * 2 ^ 59
def prefixEnd_1808844 : Nat := 4983230072969 + 3 ^ 40 * 1808844 * 2
def baseEnd_1808844 : Nat := 2548165709194584700223

theorem tailTrace_1808844 : CollatzResearch.WordTrace tailWord_1808844 prefixEnd_1808844 2548165709194584700223 := by
  unfold tailWord_1808844
  simp only [CollatzResearch.WordTrace]
  refine ⟨32986980329437294402728793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43982640439249725870305057 32986980329437294402728793)
  ·
    refine ⟨24740235247077970802046595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32986980329437294402728793 24740235247077970802046595)
    ·
      refine ⟨37110352870616956203069893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24740235247077970802046595 37110352870616956203069893)
      ·
        refine ⟨6958191163240679288075605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37110352870616956203069893 6958191163240679288075605)
        ·
          refine ⟨2548165709194584700223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 6958191163240679288075605 2548165709194584700223)
          ·
            rfl

theorem cell22_1808844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 13].length) (baseStart_1808844 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1808844 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1808844 prefixEnd_1808844 := by exact prefixLift 1808844
  have htrace : WordTrace (prefixWord ++ tailWord_1808844) baseStart_1808844 baseEnd_1808844 := by
    simpa [prefixWord, tailWord_1808844, baseEnd_1808844] using wordTrace_append hprefix tailTrace_1808844
  have hstable : (prefixWord ++ tailWord_1808844).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1808844).length < 2 ^ (prefixWord ++ tailWord_1808844).sum := by decide
  have hdescent : baseEnd_1808844 < baseStart_1808844 := by decide
  rcases family_descends (prefixWord ++ tailWord_1808844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1808878 : List Nat := [4, 1, 2, 1, 2, 3, 3, 6]
def baseStart_1808878 : Nat := 118140960795 + 1808878 * 2 ^ 59
def prefixEnd_1808878 : Nat := 4983230072969 + 3 ^ 40 * 1808878 * 2
def baseEnd_1808878 : Nat := 68801767358791036311565

theorem tailTrace_1808878 : CollatzResearch.WordTrace tailWord_1808878 prefixEnd_1808878 68801767358791036311565 := by
  unfold tailWord_1808878
  simp only [CollatzResearch.WordTrace]
  refine ⟨8246900092593926576524411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43983467160500941741463525 8246900092593926576524411)
  ·
    refine ⟨12370350138890889864786617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8246900092593926576524411 12370350138890889864786617)
    ·
      refine ⟨9277762604168167398589963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12370350138890889864786617 9277762604168167398589963)
      ·
        refine ⟨13916643906252251097884945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9277762604168167398589963 13916643906252251097884945)
        ·
          refine ⟨10437482929689188323413709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13916643906252251097884945 10437482929689188323413709)
          ·
            refine ⟨3914056098633445621280141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10437482929689188323413709 3914056098633445621280141)
            ·
              refine ⟨1467771036987542107980053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3914056098633445621280141 1467771036987542107980053)
              ·
                refine ⟨68801767358791036311565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1467771036987542107980053 68801767358791036311565)
                ·
                  rfl

theorem cell22_1808878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 3, 6].length) (baseStart_1808878 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1808878 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1808878 prefixEnd_1808878 := by exact prefixLift 1808878
  have htrace : WordTrace (prefixWord ++ tailWord_1808878) baseStart_1808878 baseEnd_1808878 := by
    simpa [prefixWord, tailWord_1808878, baseEnd_1808878] using wordTrace_append hprefix tailTrace_1808878
  have hstable : (prefixWord ++ tailWord_1808878).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1808878).length < 2 ^ (prefixWord ++ tailWord_1808878).sum := by decide
  have hdescent : baseEnd_1808878 < baseStart_1808878 := by decide
  rcases family_descends (prefixWord ++ tailWord_1808878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1808906 : List Nat := [3, 1, 2, 2, 2, 1, 3, 1, 7]
def baseStart_1808906 : Nat := 118140960795 + 1808906 * 2 ^ 59
def prefixEnd_1808906 : Nat := 4983230072969 + 3 ^ 40 * 1808906 * 2
def baseEnd_1808906 : Nat := 206408497067112195701333

theorem tailTrace_1808906 : CollatzResearch.WordTrace tailWord_1808906 prefixEnd_1808906 206408497067112195701333 := by
  unfold tailWord_1808906
  simp only [CollatzResearch.WordTrace]
  refine ⟨16494055496162493348553643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43984147989766648929476381 16494055496162493348553643)
  ·
    refine ⟨24741083244243740022830465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16494055496162493348553643 24741083244243740022830465)
    ·
      refine ⟨18555812433182805017122849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24741083244243740022830465 18555812433182805017122849)
      ·
        refine ⟨13916859324887103762842137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18555812433182805017122849 13916859324887103762842137)
        ·
          refine ⟨10437644493665327822131603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13916859324887103762842137 10437644493665327822131603)
          ·
            refine ⟨15656466740497991733197405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10437644493665327822131603 15656466740497991733197405)
            ·
              refine ⟨5871175027686746899949027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15656466740497991733197405 5871175027686746899949027)
              ·
                refine ⟨8806762541530120349923541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5871175027686746899949027 8806762541530120349923541)
                ·
                  refine ⟨206408497067112195701333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8806762541530120349923541 206408497067112195701333)
                  ·
                    rfl

theorem cell22_1808906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 3, 1, 7].length) (baseStart_1808906 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1808906 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1808906 prefixEnd_1808906 := by exact prefixLift 1808906
  have htrace : WordTrace (prefixWord ++ tailWord_1808906) baseStart_1808906 baseEnd_1808906 := by
    simpa [prefixWord, tailWord_1808906, baseEnd_1808906] using wordTrace_append hprefix tailTrace_1808906
  have hstable : (prefixWord ++ tailWord_1808906).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1808906).length < 2 ^ (prefixWord ++ tailWord_1808906).sum := by decide
  have hdescent : baseEnd_1808906 < baseStart_1808906 := by decide
  rcases family_descends (prefixWord ++ tailWord_1808906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1808910 : List Nat := [4, 1, 1, 2, 3, 2, 2, 1, 3, 3]
def baseStart_1808910 : Nat := 118140960795 + 1808910 * 2 ^ 59
def prefixEnd_1808910 : Nat := 4983230072969 + 3 ^ 40 * 1808910 * 2
def baseEnd_1808910 : Nat := 619226860483081910003987

theorem tailTrace_1808910 : CollatzResearch.WordTrace tailWord_1808910 prefixEnd_1808910 619226860483081910003987 := by
  unfold tailWord_1808910
  simp only [CollatzResearch.WordTrace]
  refine ⟨8247045984579435259670023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43984245251090321384906789 8247045984579435259670023)
  ·
    refine ⟨12370568976869152889505035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8247045984579435259670023 12370568976869152889505035)
    ·
      refine ⟨18555853465303729334257553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12370568976869152889505035 18555853465303729334257553)
      ·
        refine ⟨13916890098977797000693165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18555853465303729334257553 13916890098977797000693165)
        ·
          refine ⟨5218833787116673875259937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13916890098977797000693165 5218833787116673875259937)
          ·
            refine ⟨3914125340337505406444953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5218833787116673875259937 3914125340337505406444953)
            ·
              refine ⟨2935594005253129054833715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3914125340337505406444953 2935594005253129054833715)
              ·
                refine ⟨4403391007879693582250573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2935594005253129054833715 4403391007879693582250573)
                ·
                  refine ⟨1651271627954885093343965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4403391007879693582250573 1651271627954885093343965)
                  ·
                    refine ⟨619226860483081910003987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1651271627954885093343965 619226860483081910003987)
                    ·
                      rfl

theorem cell22_1808910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 2, 1, 3, 3].length) (baseStart_1808910 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1808910 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1808910 prefixEnd_1808910 := by exact prefixLift 1808910
  have htrace : WordTrace (prefixWord ++ tailWord_1808910) baseStart_1808910 baseEnd_1808910 := by
    simpa [prefixWord, tailWord_1808910, baseEnd_1808910] using wordTrace_append hprefix tailTrace_1808910
  have hstable : (prefixWord ++ tailWord_1808910).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1808910).length < 2 ^ (prefixWord ++ tailWord_1808910).sum := by decide
  have hdescent : baseEnd_1808910 < baseStart_1808910 := by decide
  rcases family_descends (prefixWord ++ tailWord_1808910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1808953 : List Nat := [1, 2, 1, 5, 1, 1, 1, 5, 1, 4]
def baseStart_1808953 : Nat := 118140960795 + 1808953 * 2 ^ 59
def prefixEnd_1808953 : Nat := 4983230072969 + 3 ^ 40 * 1808953 * 2
def baseEnd_1808953 : Nat := 619241580261844131178855

theorem tailTrace_1808953 : CollatzResearch.WordTrace tailWord_1808953 prefixEnd_1808953 619241580261844131178855 := by
  unfold tailWord_1808953
  simp only [CollatzResearch.WordTrace]
  refine ⟨65977936215479700421175513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43985290810319800280783675 65977936215479700421175513)
  ·
    refine ⟨49483452161609775315881635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65977936215479700421175513 49483452161609775315881635)
    ·
      refine ⟨74225178242414662973822453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49483452161609775315881635 74225178242414662973822453)
      ·
        refine ⟨6958610460226374653795855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 74225178242414662973822453 6958610460226374653795855)
        ·
          refine ⟨10437915690339561980693783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6958610460226374653795855 10437915690339561980693783)
          ·
            refine ⟨15656873535509342971040675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10437915690339561980693783 15656873535509342971040675)
            ·
              refine ⟨23485310303264014456561013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15656873535509342971040675 23485310303264014456561013)
              ·
                refine ⟨2201747840931001355302595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23485310303264014456561013 2201747840931001355302595)
                ·
                  refine ⟨3302621761396502032953893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2201747840931001355302595 3302621761396502032953893)
                  ·
                    refine ⟨619241580261844131178855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3302621761396502032953893 619241580261844131178855)
                    ·
                      rfl

theorem cell22_1808953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 5, 1, 4].length) (baseStart_1808953 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1808953 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1808953 prefixEnd_1808953 := by exact prefixLift 1808953
  have htrace : WordTrace (prefixWord ++ tailWord_1808953) baseStart_1808953 baseEnd_1808953 := by
    simpa [prefixWord, tailWord_1808953, baseEnd_1808953] using wordTrace_append hprefix tailTrace_1808953
  have hstable : (prefixWord ++ tailWord_1808953).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1808953).length < 2 ^ (prefixWord ++ tailWord_1808953).sum := by decide
  have hdescent : baseEnd_1808953 < baseStart_1808953 := by decide
  rcases family_descends (prefixWord ++ tailWord_1808953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1808968 : List Nat := [2, 1, 3, 1, 1, 1, 1, 8, 4]
def baseStart_1808968 : Nat := 118140960795 + 1808968 * 2 ^ 59
def prefixEnd_1808968 : Nat := 4983230072969 + 3 ^ 40 * 1808968 * 2
def baseEnd_1808968 : Nat := 206415571689463030684603

theorem tailTrace_1808968 : CollatzResearch.WordTrace tailWord_1808968 prefixEnd_1808968 206415571689463030684603 := by
  unfold tailWord_1808968
  simp only [CollatzResearch.WordTrace]
  refine ⟨32989241655212678991485779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43985655540283571988647705 32989241655212678991485779)
  ·
    refine ⟨49483862482819018487228669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32989241655212678991485779 49483862482819018487228669)
    ·
      refine ⟨18556448431057131932710751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49483862482819018487228669 18556448431057131932710751)
      ·
        refine ⟨27834672646585697899066127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18556448431057131932710751 27834672646585697899066127)
        ·
          refine ⟨41752008969878546848599191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27834672646585697899066127 41752008969878546848599191)
          ·
            refine ⟨62628013454817820272898787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41752008969878546848599191 62628013454817820272898787)
            ·
              refine ⟨93942020182226730409348181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62628013454817820272898787 93942020182226730409348181)
              ·
                refine ⟨1100883049010469496984549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 93942020182226730409348181 1100883049010469496984549)
                ·
                  refine ⟨206415571689463030684603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1100883049010469496984549 206415571689463030684603)
                  ·
                    rfl

theorem cell22_1808968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 8, 4].length) (baseStart_1808968 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1808968 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1808968 prefixEnd_1808968 := by exact prefixLift 1808968
  have htrace : WordTrace (prefixWord ++ tailWord_1808968) baseStart_1808968 baseEnd_1808968 := by
    simpa [prefixWord, tailWord_1808968, baseEnd_1808968] using wordTrace_append hprefix tailTrace_1808968
  have hstable : (prefixWord ++ tailWord_1808968).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1808968).length < 2 ^ (prefixWord ++ tailWord_1808968).sum := by decide
  have hdescent : baseEnd_1808968 < baseStart_1808968 := by decide
  rcases family_descends (prefixWord ++ tailWord_1808968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1808981 : List Nat := [1, 3, 2, 2, 1, 1, 2, 1, 3, 6]
def baseStart_1808981 : Nat := 118140960795 + 1808981 * 2 ^ 59
def prefixEnd_1808981 : Nat := 4983230072969 + 3 ^ 40 * 1808981 * 2
def baseEnd_1808981 : Nat := 619251165234061391478769

theorem tailTrace_1808981 : CollatzResearch.WordTrace tailWord_1808981 prefixEnd_1808981 619251165234061391478769 := by
  unfold tailWord_1808981
  simp only [CollatzResearch.WordTrace]
  refine ⟨65978957459378261203194797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43985971639585507468796531 65978957459378261203194797)
  ·
    refine ⟨24742109047266847951198049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65978957459378261203194797 24742109047266847951198049)
    ·
      refine ⟨18556581785450135963398537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24742109047266847951198049 18556581785450135963398537)
      ·
        refine ⟨13917436339087601972548903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18556581785450135963398537 13917436339087601972548903)
        ·
          refine ⟨20876154508631402958823355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13917436339087601972548903 20876154508631402958823355)
          ·
            refine ⟨31314231762947104438235033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20876154508631402958823355 31314231762947104438235033)
            ·
              refine ⟨23485673822210328328676275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31314231762947104438235033 23485673822210328328676275)
              ·
                refine ⟨35228510733315492493014413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23485673822210328328676275 35228510733315492493014413)
                ·
                  refine ⟨13210691524993309684880405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35228510733315492493014413 13210691524993309684880405)
                  ·
                    refine ⟨619251165234061391478769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13210691524993309684880405 619251165234061391478769)
                    ·
                      rfl

theorem cell22_1808981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 1, 3, 6].length) (baseStart_1808981 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1808981 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1808981 prefixEnd_1808981 := by exact prefixLift 1808981
  have htrace : WordTrace (prefixWord ++ tailWord_1808981) baseStart_1808981 baseEnd_1808981 := by
    simpa [prefixWord, tailWord_1808981, baseEnd_1808981] using wordTrace_append hprefix tailTrace_1808981
  have hstable : (prefixWord ++ tailWord_1808981).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1808981).length < 2 ^ (prefixWord ++ tailWord_1808981).sum := by decide
  have hdescent : baseEnd_1808981 < baseStart_1808981 := by decide
  rcases family_descends (prefixWord ++ tailWord_1808981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1808996 : List Nat := [2, 3, 1, 1, 2, 2, 1, 10]
def baseStart_1808996 : Nat := 118140960795 + 1808996 * 2 ^ 59
def prefixEnd_1808996 : Nat := 4983230072969 + 3 ^ 40 * 1808996 * 2
def baseEnd_1808996 : Nat := 68806255560067372483747

theorem tailTrace_1808996 : CollatzResearch.WordTrace tailWord_1808996 prefixEnd_1808996 68806255560067372483747 := by
  unfold tailWord_1808996
  simp only [CollatzResearch.WordTrace]
  refine ⟨32989752277161959382495421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43986336369549279176660561 32989752277161959382495421)
  ·
    refine ⟨12371157103935734768435783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32989752277161959382495421 12371157103935734768435783)
    ·
      refine ⟨18556735655903602152653675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12371157103935734768435783 18556735655903602152653675)
      ·
        refine ⟨27835103483855403228980513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18556735655903602152653675 27835103483855403228980513)
        ·
          refine ⟨20876327612891552421735385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27835103483855403228980513 20876327612891552421735385)
          ·
            refine ⟨15657245709668664316301539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20876327612891552421735385 15657245709668664316301539)
            ·
              refine ⟨23485868564502996474452309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15657245709668664316301539 23485868564502996474452309)
              ·
                refine ⟨68806255560067372483747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 23485868564502996474452309 68806255560067372483747)
                ·
                  rfl

theorem cell22_1808996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 10].length) (baseStart_1808996 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1808996 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1808996 prefixEnd_1808996 := by exact prefixLift 1808996
  have htrace : WordTrace (prefixWord ++ tailWord_1808996) baseStart_1808996 baseEnd_1808996 := by
    simpa [prefixWord, tailWord_1808996, baseEnd_1808996] using wordTrace_append hprefix tailTrace_1808996
  have hstable : (prefixWord ++ tailWord_1808996).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1808996).length < 2 ^ (prefixWord ++ tailWord_1808996).sum := by decide
  have hdescent : baseEnd_1808996 < baseStart_1808996 := by decide
  rcases family_descends (prefixWord ++ tailWord_1808996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1809000 : List Nat := [2, 1, 4, 3, 2, 1, 1, 2, 1, 5]
def baseStart_1809000 : Nat := 118140960795 + 1809000 * 2 ^ 59
def prefixEnd_1809000 : Nat := 4983230072969 + 3 ^ 40 * 1809000 * 2
def baseEnd_1809000 : Nat := 619257669322351675253711

theorem tailTrace_1809000 : CollatzResearch.WordTrace tailWord_1809000 prefixEnd_1809000 619257669322351675253711 := by
  unfold tailWord_1809000
  simp only [CollatzResearch.WordTrace]
  refine ⟨32989825223154713724068227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43986433630872951632090969 32989825223154713724068227)
  ·
    refine ⟨49484737834732070586102341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32989825223154713724068227 49484737834732070586102341)
    ·
      refine ⟨9278388344012263234894189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49484737834732070586102341 9278388344012263234894189)
      ·
        refine ⟨3479395629004598713085321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9278388344012263234894189 3479395629004598713085321)
        ·
          refine ⟨2609546721753449034813991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3479395629004598713085321 2609546721753449034813991)
          ·
            refine ⟨3914320082630173552220987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2609546721753449034813991 3914320082630173552220987)
            ·
              refine ⟨5871480123945260328331481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3914320082630173552220987 5871480123945260328331481)
              ·
                refine ⟨4403610092958945246248611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5871480123945260328331481 4403610092958945246248611)
                ·
                  refine ⟨6605415139438417869372917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4403610092958945246248611 6605415139438417869372917)
                  ·
                    refine ⟨619257669322351675253711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6605415139438417869372917 619257669322351675253711)
                    ·
                      rfl

theorem cell22_1809000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 1, 2, 1, 5].length) (baseStart_1809000 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1809000 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1809000 prefixEnd_1809000 := by exact prefixLift 1809000
  have htrace : WordTrace (prefixWord ++ tailWord_1809000) baseStart_1809000 baseEnd_1809000 := by
    simpa [prefixWord, tailWord_1809000, baseEnd_1809000] using wordTrace_append hprefix tailTrace_1809000
  have hstable : (prefixWord ++ tailWord_1809000).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1809000).length < 2 ^ (prefixWord ++ tailWord_1809000).sum := by decide
  have hdescent : baseEnd_1809000 < baseStart_1809000 := by decide
  rcases family_descends (prefixWord ++ tailWord_1809000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1809013 : List Nat := [1, 3, 4, 2, 2, 10]
def baseStart_1809013 : Nat := 118140960795 + 1809013 * 2 ^ 59
def prefixEnd_1809013 : Nat := 4983230072969 + 3 ^ 40 * 1809013 * 2
def baseEnd_1809013 : Nat := 7645211351703999687391

theorem tailTrace_1809013 : CollatzResearch.WordTrace tailWord_1809013 prefixEnd_1809013 7645211351703999687391 := by
  unfold tailWord_1809013
  simp only [CollatzResearch.WordTrace]
  refine ⟨65980124595262330668359693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43986749730174887112239795 65980124595262330668359693)
  ·
    refine ⟨24742546723223374000634885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65980124595262330668359693 24742546723223374000634885)
    ·
      refine ⟨4639227510604382625119041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24742546723223374000634885 4639227510604382625119041)
      ·
        refine ⟨3479420632953286968839281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4639227510604382625119041 3479420632953286968839281)
        ·
          refine ⟨2609565474714965226629461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3479420632953286968839281 2609565474714965226629461)
          ·
            refine ⟨7645211351703999687391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 2609565474714965226629461 7645211351703999687391)
            ·
              rfl

theorem cell22_1809013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 10].length) (baseStart_1809013 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1809013 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1809013 prefixEnd_1809013 := by exact prefixLift 1809013
  have htrace : WordTrace (prefixWord ++ tailWord_1809013) baseStart_1809013 baseEnd_1809013 := by
    simpa [prefixWord, tailWord_1809013, baseEnd_1809013] using wordTrace_append hprefix tailTrace_1809013
  have hstable : (prefixWord ++ tailWord_1809013).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1809013).length < 2 ^ (prefixWord ++ tailWord_1809013).sum := by decide
  have hdescent : baseEnd_1809013 < baseStart_1809013 := by decide
  rcases family_descends (prefixWord ++ tailWord_1809013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1809075 : List Nat := [1, 1, 1, 2, 3, 6, 1, 2, 5]
def baseStart_1809075 : Nat := 118140960795 + 1809075 * 2 ^ 59
def prefixEnd_1809075 : Nat := 4983230072969 + 3 ^ 40 * 1809075 * 2
def baseEnd_1809075 : Nat := 206427781118358826542827

theorem tailTrace_1809075 : CollatzResearch.WordTrace tailWord_1809075 prefixEnd_1809075 206427781118358826542827 := by
  unfold tailWord_1809075
  simp only [CollatzResearch.WordTrace]
  refine ⟨65982385921037715257116679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43988257280691810171411119 65982385921037715257116679)
  ·
    refine ⟨98973578881556572885675019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65982385921037715257116679 98973578881556572885675019)
    ·
      refine ⟨148460368322334859328512529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98973578881556572885675019 148460368322334859328512529)
      ·
        refine ⟨111345276241751144496384397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148460368322334859328512529 111345276241751144496384397)
        ·
          refine ⟨41754478590656679186144149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111345276241751144496384397 41754478590656679186144149)
          ·
            refine ⟨1957241183937031836850507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 41754478590656679186144149 1957241183937031836850507)
            ·
              refine ⟨2935861775905547755275761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1957241183937031836850507 2935861775905547755275761)
              ·
                refine ⟨2201896331929160816456821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2935861775905547755275761 2201896331929160816456821)
                ·
                  refine ⟨206427781118358826542827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2201896331929160816456821 206427781118358826542827)
                  ·
                    rfl

theorem cell22_1809075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 6, 1, 2, 5].length) (baseStart_1809075 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1809075 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1809075 prefixEnd_1809075 := by exact prefixLift 1809075
  have htrace : WordTrace (prefixWord ++ tailWord_1809075) baseStart_1809075 baseEnd_1809075 := by
    simpa [prefixWord, tailWord_1809075, baseEnd_1809075] using wordTrace_append hprefix tailTrace_1809075
  have hstable : (prefixWord ++ tailWord_1809075).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1809075).length < 2 ^ (prefixWord ++ tailWord_1809075).sum := by decide
  have hdescent : baseEnd_1809075 < baseStart_1809075 := by decide
  rcases family_descends (prefixWord ++ tailWord_1809075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1809092 : List Nat := [2, 3, 3, 1, 1, 3, 3, 1, 5]
def baseStart_1809092 : Nat := 118140960795 + 1809092 * 2 ^ 59
def prefixEnd_1809092 : Nat := 4983230072969 + 3 ^ 40 * 1809092 * 2
def baseEnd_1809092 : Nat := 206429720934164700651143

theorem tailTrace_1809092 : CollatzResearch.WordTrace tailWord_1809092 prefixEnd_1809092 206429720934164700651143 := by
  unfold tailWord_1809092
  simp only [CollatzResearch.WordTrace]
  refine ⟨32991502980988063580242765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43988670641317418106990353 32991502980988063580242765)
  ·
    refine ⟨12371813617870523842591037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32991502980988063580242765 12371813617870523842591037)
    ·
      refine ⟨4639430106701446440971639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12371813617870523842591037 4639430106701446440971639)
      ·
        refine ⟨6959145160052169661457459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4639430106701446440971639 6959145160052169661457459)
        ·
          refine ⟨10438717740078254492186189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6959145160052169661457459 10438717740078254492186189)
          ·
            refine ⟨3914519152529345434569821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10438717740078254492186189 3914519152529345434569821)
            ·
              refine ⟨1467944682198504537963683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3914519152529345434569821 1467944682198504537963683)
              ·
                refine ⟨2201917023297756806945525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1467944682198504537963683 2201917023297756806945525)
                ·
                  refine ⟨206429720934164700651143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2201917023297756806945525 206429720934164700651143)
                  ·
                    rfl

theorem cell22_1809092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 3, 1, 5].length) (baseStart_1809092 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1809092 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1809092 prefixEnd_1809092 := by exact prefixLift 1809092
  have htrace : WordTrace (prefixWord ++ tailWord_1809092) baseStart_1809092 baseEnd_1809092 := by
    simpa [prefixWord, tailWord_1809092, baseEnd_1809092] using wordTrace_append hprefix tailTrace_1809092
  have hstable : (prefixWord ++ tailWord_1809092).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1809092).length < 2 ^ (prefixWord ++ tailWord_1809092).sum := by decide
  have hdescent : baseEnd_1809092 < baseStart_1809092 := by decide
  rcases family_descends (prefixWord ++ tailWord_1809092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1809105 : List Nat := [1, 2, 2, 1, 2, 3, 4, 2, 1, 4]
def baseStart_1809105 : Nat := 118140960795 + 1809105 * 2 ^ 59
def prefixEnd_1809105 : Nat := 4983230072969 + 3 ^ 40 * 1809105 * 2
def baseEnd_1809105 : Nat := 619293612968166401378389

theorem tailTrace_1809105 : CollatzResearch.WordTrace tailWord_1809105 prefixEnd_1809105 619293612968166401378389 := by
  unfold tailWord_1809105
  simp only [CollatzResearch.WordTrace]
  refine ⟨65983480110929030380708769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43988986740619353587139179 65983480110929030380708769)
  ·
    refine ⟨49487610083196772785531577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65983480110929030380708769 49487610083196772785531577)
    ·
      refine ⟨37115707562397579589148683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49487610083196772785531577 37115707562397579589148683)
      ·
        refine ⟨55673561343596369383723025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37115707562397579589148683 55673561343596369383723025)
        ·
          refine ⟨41755171007697277037792269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55673561343596369383723025 41755171007697277037792269)
          ·
            refine ⟨15658189127886478889172101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41755171007697277037792269 15658189127886478889172101)
            ·
              refine ⟨2935910461478714791719769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15658189127886478889172101 2935910461478714791719769)
              ·
                refine ⟨2201932846109036093789827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2935910461478714791719769 2201932846109036093789827)
                ·
                  refine ⟨3302899269163554140684741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2201932846109036093789827 3302899269163554140684741)
                  ·
                    refine ⟨619293612968166401378389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3302899269163554140684741 619293612968166401378389)
                    ·
                      rfl

theorem cell22_1809105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 4, 2, 1, 4].length) (baseStart_1809105 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1809105 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1809105 prefixEnd_1809105 := by exact prefixLift 1809105
  have htrace : WordTrace (prefixWord ++ tailWord_1809105) baseStart_1809105 baseEnd_1809105 := by
    simpa [prefixWord, tailWord_1809105, baseEnd_1809105] using wordTrace_append hprefix tailTrace_1809105
  have hstable : (prefixWord ++ tailWord_1809105).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1809105).length < 2 ^ (prefixWord ++ tailWord_1809105).sum := by decide
  have hdescent : baseEnd_1809105 < baseStart_1809105 := by decide
  rcases family_descends (prefixWord ++ tailWord_1809105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1809135 : List Nat := [1, 1, 2, 1, 5, 2, 2, 1, 4, 3]
def baseStart_1809135 : Nat := 118140960795 + 1809135 * 2 ^ 59
def prefixEnd_1809135 : Nat := 4983230072969 + 3 ^ 40 * 1809135 * 2
def baseEnd_1809135 : Nat := 619303882581256323128297

theorem tailTrace_1809135 : CollatzResearch.WordTrace tailWord_1809135 prefixEnd_1809135 619303882581256323128297 := by
  unfold tailWord_1809135
  simp only [CollatzResearch.WordTrace]
  refine ⟨65984574300820345504300859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43989716200546897002867239 65984574300820345504300859)
  ·
    refine ⟨98976861451230518256451289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65984574300820345504300859 98976861451230518256451289)
    ·
      refine ⟨74232646088422888692338467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98976861451230518256451289 74232646088422888692338467)
      ·
        refine ⟨111348969132634333038507701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74232646088422888692338467 111348969132634333038507701)
        ·
          refine ⟨10438965856184468722360097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 111348969132634333038507701 10438965856184468722360097)
          ·
            refine ⟨7829224392138351541770073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10438965856184468722360097 7829224392138351541770073)
            ·
              refine ⟨5871918294103763656327555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7829224392138351541770073 5871918294103763656327555)
              ·
                refine ⟨8807877441155645484491333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5871918294103763656327555 8807877441155645484491333)
                ·
                  refine ⟨1651477020216683528342125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8807877441155645484491333 1651477020216683528342125)
                  ·
                    refine ⟨619303882581256323128297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1651477020216683528342125 619303882581256323128297)
                    ·
                      rfl

theorem cell22_1809135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 2, 1, 4, 3].length) (baseStart_1809135 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1809135 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1809135 prefixEnd_1809135 := by exact prefixLift 1809135
  have htrace : WordTrace (prefixWord ++ tailWord_1809135) baseStart_1809135 baseEnd_1809135 := by
    simpa [prefixWord, tailWord_1809135, baseEnd_1809135] using wordTrace_append hprefix tailTrace_1809135
  have hstable : (prefixWord ++ tailWord_1809135).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1809135).length < 2 ^ (prefixWord ++ tailWord_1809135).sum := by decide
  have hdescent : baseEnd_1809135 < baseStart_1809135 := by decide
  rcases family_descends (prefixWord ++ tailWord_1809135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1809137 : List Nat := [1, 2, 2, 2, 2, 2, 5, 2, 4]
def baseStart_1809137 : Nat := 118140960795 + 1809137 * 2 ^ 59
def prefixEnd_1809137 : Nat := 4983230072969 + 3 ^ 40 * 1809137 * 2
def baseEnd_1809137 : Nat := 206434855740709661526097

theorem tailTrace_1809137 : CollatzResearch.WordTrace tailWord_1809137 prefixEnd_1809137 206434855740709661526097 := by
  unfold tailWord_1809137
  simp only [CollatzResearch.WordTrace]
  refine ⟨65984647246813099845873665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43989764831208733230582443 65984647246813099845873665)
  ·
    refine ⟨49488485435109824884405249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65984647246813099845873665 49488485435109824884405249)
    ·
      refine ⟨37116364076332368663303937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49488485435109824884405249 37116364076332368663303937)
      ·
        refine ⟨27837273057249276497477953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37116364076332368663303937 27837273057249276497477953)
        ·
          refine ⟨20877954792936957373108465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27837273057249276497477953 20877954792936957373108465)
          ·
            refine ⟨15658466094702718029831349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20877954792936957373108465 15658466094702718029831349)
            ·
              refine ⟨1467981196378379815296689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15658466094702718029831349 1467981196378379815296689)
              ·
                refine ⟨1100985897283784861472517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1467981196378379815296689 1100985897283784861472517)
                ·
                  refine ⟨206434855740709661526097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1100985897283784861472517 206434855740709661526097)
                  ·
                    rfl

theorem cell22_1809137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 5, 2, 4].length) (baseStart_1809137 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1809137 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1809137 prefixEnd_1809137 := by exact prefixLift 1809137
  have htrace : WordTrace (prefixWord ++ tailWord_1809137) baseStart_1809137 baseEnd_1809137 := by
    simpa [prefixWord, tailWord_1809137, baseEnd_1809137] using wordTrace_append hprefix tailTrace_1809137
  have hstable : (prefixWord ++ tailWord_1809137).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1809137).length < 2 ^ (prefixWord ++ tailWord_1809137).sum := by decide
  have hdescent : baseEnd_1809137 < baseStart_1809137 := by decide
  rcases family_descends (prefixWord ++ tailWord_1809137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1809148 : List Nat := [2, 2, 2, 1, 3, 2, 1, 9]
def baseStart_1809148 : Nat := 118140960795 + 1809148 * 2 ^ 59
def prefixEnd_1809148 : Nat := 4983230072969 + 3 ^ 40 * 1809148 * 2
def baseEnd_1809148 : Nat := 68812036971880958061473

theorem tailTrace_1809148 : CollatzResearch.WordTrace tailWord_1809148 prefixEnd_1809148 68812036971880958061473 := by
  unfold tailWord_1809148
  simp only [CollatzResearch.WordTrace]
  refine ⟨32992524224886624362262049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43990032299848832483016065 32992524224886624362262049)
  ·
    refine ⟨24744393168664968271696537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32992524224886624362262049 24744393168664968271696537)
    ·
      refine ⟨18558294876498726203772403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24744393168664968271696537 18558294876498726203772403)
      ·
        refine ⟨27837442314748089305658605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18558294876498726203772403 27837442314748089305658605)
        ·
          refine ⟨10439040868030533489621977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27837442314748089305658605 10439040868030533489621977)
          ·
            refine ⟨7829280651022900117216483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10439040868030533489621977 7829280651022900117216483)
            ·
              refine ⟨11743920976534350175824725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7829280651022900117216483 11743920976534350175824725)
              ·
                refine ⟨68812036971880958061473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 11743920976534350175824725 68812036971880958061473)
                ·
                  rfl

theorem cell22_1809148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 9].length) (baseStart_1809148 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1809148 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1809148 prefixEnd_1809148 := by exact prefixLift 1809148
  have htrace : WordTrace (prefixWord ++ tailWord_1809148) baseStart_1809148 baseEnd_1809148 := by
    simpa [prefixWord, tailWord_1809148, baseEnd_1809148] using wordTrace_append hprefix tailTrace_1809148
  have hstable : (prefixWord ++ tailWord_1809148).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1809148).length < 2 ^ (prefixWord ++ tailWord_1809148).sum := by decide
  have hdescent : baseEnd_1809148 < baseStart_1809148 := by decide
  rcases family_descends (prefixWord ++ tailWord_1809148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1809214 : List Nat := [4, 2, 1, 2, 3, 1, 1, 2, 3, 3]
def baseStart_1809214 : Nat := 118140960795 + 1809214 * 2 ^ 59
def prefixEnd_1809214 : Nat := 4983230072969 + 3 ^ 40 * 1809214 * 2
def baseEnd_1809214 : Nat := 619330925895726450403055

theorem tailTrace_1809214 : CollatzResearch.WordTrace tailWord_1809214 prefixEnd_1809214 619330925895726450403055 := by
  unfold tailWord_1809214
  simp only [CollatzResearch.WordTrace]
  refine ⟨8248431958441767749553337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43991637111689427997617797 8248431958441767749553337)
  ·
    refine ⟨6186323968831325812165003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8248431958441767749553337 6186323968831325812165003)
    ·
      refine ⟨9279485953246988718247505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6186323968831325812165003 9279485953246988718247505)
      ·
        refine ⟨6959614464935241538685629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9279485953246988718247505 6959614464935241538685629)
        ·
          refine ⟨2609855424350715577007111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6959614464935241538685629 2609855424350715577007111)
          ·
            refine ⟨3914783136526073365510667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2609855424350715577007111 3914783136526073365510667)
            ·
              refine ⟨5872174704789110048266001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3914783136526073365510667 5872174704789110048266001)
              ·
                refine ⟨4404131028591832536199501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5872174704789110048266001 4404131028591832536199501)
                ·
                  refine ⟨1651549135721937201074813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4404131028591832536199501 1651549135721937201074813)
                  ·
                    refine ⟨619330925895726450403055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1651549135721937201074813 619330925895726450403055)
                    ·
                      rfl

theorem cell22_1809214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 1, 2, 3, 3].length) (baseStart_1809214 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1809214 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1809214 prefixEnd_1809214 := by exact prefixLift 1809214
  have htrace : WordTrace (prefixWord ++ tailWord_1809214) baseStart_1809214 baseEnd_1809214 := by
    simpa [prefixWord, tailWord_1809214, baseEnd_1809214] using wordTrace_append hprefix tailTrace_1809214
  have hstable : (prefixWord ++ tailWord_1809214).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1809214).length < 2 ^ (prefixWord ++ tailWord_1809214).sum := by decide
  have hdescent : baseEnd_1809214 < baseStart_1809214 := by decide
  rcases family_descends (prefixWord ++ tailWord_1809214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1809244 : List Nat := [2, 2, 4, 2, 1, 3, 1, 2, 5]
def baseStart_1809244 : Nat := 118140960795 + 1809244 * 2 ^ 59
def prefixEnd_1809244 : Nat := 4983230072969 + 3 ^ 40 * 1809244 * 2
def baseEnd_1809244 : Nat := 206447065169605457384321

theorem tailTrace_1809244 : CollatzResearch.WordTrace tailWord_1809244 prefixEnd_1809244 206447065169605457384321 := by
  unfold tailWord_1809244
  simp only [CollatzResearch.WordTrace]
  refine ⟨32994274928712728560009393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43992366571616971413345857 32994274928712728560009393)
  ·
    refine ⟨24745706196534546420007045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32994274928712728560009393 24745706196534546420007045)
    ·
      refine ⟨4639819911850227453751321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24745706196534546420007045 4639819911850227453751321)
      ·
        refine ⟨3479864933887670590313491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4639819911850227453751321 3479864933887670590313491)
        ·
          refine ⟨5219797400831505885470237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3479864933887670590313491 5219797400831505885470237)
          ·
            refine ⟨1957424025311814707051339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5219797400831505885470237 1957424025311814707051339)
            ·
              refine ⟨2936136037967722060577009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1957424025311814707051339 2936136037967722060577009)
              ·
                refine ⟨2202102028475791545432757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2936136037967722060577009 2202102028475791545432757)
                ·
                  refine ⟨206447065169605457384321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2202102028475791545432757 206447065169605457384321)
                  ·
                    rfl

theorem cell22_1809244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 3, 1, 2, 5].length) (baseStart_1809244 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1809244 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1809244 prefixEnd_1809244 := by exact prefixLift 1809244
  have htrace : WordTrace (prefixWord ++ tailWord_1809244) baseStart_1809244 baseEnd_1809244 := by
    simpa [prefixWord, tailWord_1809244, baseEnd_1809244] using wordTrace_append hprefix tailTrace_1809244
  have hstable : (prefixWord ++ tailWord_1809244).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1809244).length < 2 ^ (prefixWord ++ tailWord_1809244).sum := by decide
  have hdescent : baseEnd_1809244 < baseStart_1809244 := by decide
  rcases family_descends (prefixWord ++ tailWord_1809244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1809255 : List Nat := [1, 1, 5, 1, 2, 2, 1, 3, 6]
def baseStart_1809255 : Nat := 118140960795 + 1809255 * 2 ^ 59
def prefixEnd_1809255 : Nat := 4983230072969 + 3 ^ 40 * 1809255 * 2
def baseEnd_1809255 : Nat := 206448320344538670042643

theorem tailTrace_1809255 : CollatzResearch.WordTrace tailWord_1809255 prefixEnd_1809255 206448320344538670042643 := by
  unfold tailWord_1809255
  simp only [CollatzResearch.WordTrace]
  refine ⟨65988951060385605998669219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43992634040257070665779479 65988951060385605998669219)
  ·
    refine ⟨98983426590578408998003829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65988951060385605998669219 98983426590578408998003829)
    ·
      refine ⟨9279696242866725843562859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 98983426590578408998003829 9279696242866725843562859)
      ·
        refine ⟨13919544364300088765344289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9279696242866725843562859 13919544364300088765344289)
        ·
          refine ⟨10439658273225066574008217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13919544364300088765344289 10439658273225066574008217)
          ·
            refine ⟨7829743704918799930506163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10439658273225066574008217 7829743704918799930506163)
            ·
              refine ⟨11744615557378199895759245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7829743704918799930506163 11744615557378199895759245)
              ·
                refine ⟨4404230834016824960909717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11744615557378199895759245 4404230834016824960909717)
                ·
                  refine ⟨206448320344538670042643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4404230834016824960909717 206448320344538670042643)
                  ·
                    rfl

theorem cell22_1809255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 3, 6].length) (baseStart_1809255 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1809255 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1809255 prefixEnd_1809255 := by exact prefixLift 1809255
  have htrace : WordTrace (prefixWord ++ tailWord_1809255) baseStart_1809255 baseEnd_1809255 := by
    simpa [prefixWord, tailWord_1809255, baseEnd_1809255] using wordTrace_append hprefix tailTrace_1809255
  have hstable : (prefixWord ++ tailWord_1809255).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1809255).length < 2 ^ (prefixWord ++ tailWord_1809255).sum := by decide
  have hdescent : baseEnd_1809255 < baseStart_1809255 := by decide
  rcases family_descends (prefixWord ++ tailWord_1809255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1809282 : List Nat := [3, 4, 2, 2, 2, 1, 1, 3, 1, 3]
def baseStart_1809282 : Nat := 118140960795 + 1809282 * 2 ^ 59
def prefixEnd_1809282 : Nat := 4983230072969 + 3 ^ 40 * 1809282 * 2
def baseEnd_1809282 : Nat := 619354203685396939702847

theorem tailTrace_1809282 : CollatzResearch.WordTrace tailWord_1809282 prefixEnd_1809282 619354203685396939702847 := by
  unfold tailWord_1809282
  simp only [CollatzResearch.WordTrace]
  refine ⟨16497483957821947402475525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43993290554191859739934733 16497483957821947402475525)
  ·
    refine ⟨3093278242091615137964161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16497483957821947402475525 3093278242091615137964161)
    ·
      refine ⟨2319958681568711353473121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3093278242091615137964161 2319958681568711353473121)
      ·
        refine ⟨1739969011176533515104841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2319958681568711353473121 1739969011176533515104841)
        ·
          refine ⟨1304976758382400136328631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1739969011176533515104841 1304976758382400136328631)
          ·
            refine ⟨1957465137573600204492947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1304976758382400136328631 1957465137573600204492947)
            ·
              refine ⟨2936197706360400306739421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1957465137573600204492947 2936197706360400306739421)
              ·
                refine ⟨1101074139885150115027283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2936197706360400306739421 1101074139885150115027283)
                ·
                  refine ⟨1651611209827725172540925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1101074139885150115027283 1651611209827725172540925)
                  ·
                    refine ⟨619354203685396939702847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1651611209827725172540925 619354203685396939702847)
                    ·
                      rfl

theorem cell22_1809282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 1, 1, 3, 1, 3].length) (baseStart_1809282 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1809282 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1809282 prefixEnd_1809282 := by exact prefixLift 1809282
  have htrace : WordTrace (prefixWord ++ tailWord_1809282) baseStart_1809282 baseEnd_1809282 := by
    simpa [prefixWord, tailWord_1809282, baseEnd_1809282] using wordTrace_append hprefix tailTrace_1809282
  have hstable : (prefixWord ++ tailWord_1809282).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1809282).length < 2 ^ (prefixWord ++ tailWord_1809282).sum := by decide
  have hdescent : baseEnd_1809282 < baseStart_1809282 := by decide
  rcases family_descends (prefixWord ++ tailWord_1809282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1809285 : List Nat := [1, 3, 1, 1, 3, 3, 2, 1, 1, 6]
def baseStart_1809285 : Nat := 118140960795 + 1809285 * 2 ^ 59
def prefixEnd_1809285 : Nat := 4983230072969 + 3 ^ 40 * 1809285 * 2
def baseEnd_1809285 : Nat := 619355230646705931877837

theorem tailTrace_1809285 : CollatzResearch.WordTrace tailWord_1809285 prefixEnd_1809285 619355230646705931877837 := by
  unfold tailWord_1809285
  simp only [CollatzResearch.WordTrace]
  refine ⟨65990045250276921122261309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43993363500184614081507539 65990045250276921122261309)
  ·
    refine ⟨24746266968853845420847991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65990045250276921122261309 24746266968853845420847991)
    ·
      refine ⟨37119400453280768131271987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24746266968853845420847991 37119400453280768131271987)
      ·
        refine ⟨55679100679921152196907981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37119400453280768131271987 55679100679921152196907981)
        ·
          refine ⟨20879662754970432073840493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55679100679921152196907981 20879662754970432073840493)
          ·
            refine ⟨7829873533113912027690185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20879662754970432073840493 7829873533113912027690185)
            ·
              refine ⟨5872405149835434020767639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7829873533113912027690185 5872405149835434020767639)
              ·
                refine ⟨8808607724753151031151459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5872405149835434020767639 8808607724753151031151459)
                ·
                  refine ⟨13212911587129726546727189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8808607724753151031151459 13212911587129726546727189)
                  ·
                    refine ⟨619355230646705931877837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13212911587129726546727189 619355230646705931877837)
                    ·
                      rfl

theorem cell22_1809285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 2, 1, 1, 6].length) (baseStart_1809285 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1809285 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1809285 prefixEnd_1809285 := by exact prefixLift 1809285
  have htrace : WordTrace (prefixWord ++ tailWord_1809285) baseStart_1809285 baseEnd_1809285 := by
    simpa [prefixWord, tailWord_1809285, baseEnd_1809285] using wordTrace_append hprefix tailTrace_1809285
  have hstable : (prefixWord ++ tailWord_1809285).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1809285).length < 2 ^ (prefixWord ++ tailWord_1809285).sum := by decide
  have hdescent : baseEnd_1809285 < baseStart_1809285 := by decide
  rcases family_descends (prefixWord ++ tailWord_1809285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1809287 : List Nat := [1, 1, 4, 2, 3, 1, 1, 2, 4, 3]
def baseStart_1809287 : Nat := 118140960795 + 1809287 * 2 ^ 59
def prefixEnd_1809287 : Nat := 4983230072969 + 3 ^ 40 * 1809287 * 2
def baseEnd_1809287 : Nat := 619355915287578593327831

theorem tailTrace_1809287 : CollatzResearch.WordTrace tailWord_1809287 prefixEnd_1809287 619355915287578593327831 := by
  unfold tailWord_1809287
  simp only [CollatzResearch.WordTrace]
  refine ⟨65990118196269675463834115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43993412130846450309222743 65990118196269675463834115)
  ·
    refine ⟨98985177294404513195751173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65990118196269675463834115 98985177294404513195751173)
    ·
      refine ⟨18559720742700846224203345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 98985177294404513195751173 18559720742700846224203345)
      ·
        refine ⟨13919790557025634668152509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18559720742700846224203345 13919790557025634668152509)
        ·
          refine ⟨5219921458884613000557191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13919790557025634668152509 5219921458884613000557191)
          ·
            refine ⟨7829882188326919500835787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5219921458884613000557191 7829882188326919500835787)
            ·
              refine ⟨11744823282490379251253681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7829882188326919500835787 11744823282490379251253681)
              ·
                refine ⟨8808617461867784438440261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11744823282490379251253681 8808617461867784438440261)
                ·
                  refine ⟨1651615774100209582207549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8808617461867784438440261 1651615774100209582207549)
                  ·
                    refine ⟨619355915287578593327831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1651615774100209582207549 619355915287578593327831)
                    ·
                      rfl

theorem cell22_1809287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 2, 4, 3].length) (baseStart_1809287 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1809287 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1809287 prefixEnd_1809287 := by exact prefixLift 1809287
  have htrace : WordTrace (prefixWord ++ tailWord_1809287) baseStart_1809287 baseEnd_1809287 := by
    simpa [prefixWord, tailWord_1809287, baseEnd_1809287] using wordTrace_append hprefix tailTrace_1809287
  have hstable : (prefixWord ++ tailWord_1809287).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1809287).length < 2 ^ (prefixWord ++ tailWord_1809287).sum := by decide
  have hdescent : baseEnd_1809287 < baseStart_1809287 := by decide
  rcases family_descends (prefixWord ++ tailWord_1809287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1809289 : List Nat := [1, 2, 1, 1, 5, 4, 1, 3, 4]
def baseStart_1809289 : Nat := 118140960795 + 1809289 * 2 ^ 59
def prefixEnd_1809289 : Nat := 4983230072969 + 3 ^ 40 * 1809289 * 2
def baseEnd_1809289 : Nat := 206452199976150418259275

theorem tailTrace_1809289 : CollatzResearch.WordTrace tailWord_1809289 prefixEnd_1809289 206452199976150418259275 := by
  unfold tailWord_1809289
  simp only [CollatzResearch.WordTrace]
  refine ⟨65990191142262429805406921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43993460761508286536937947 65990191142262429805406921)
  ·
    refine ⟨49492643356696822354055191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65990191142262429805406921 49492643356696822354055191)
    ·
      refine ⟨74238965035045233531082787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49492643356696822354055191 74238965035045233531082787)
      ·
        refine ⟨111358447552567850296624181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74238965035045233531082787 111358447552567850296624181)
        ·
          refine ⟨10439854458053235965308517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 111358447552567850296624181 10439854458053235965308517)
          ·
            refine ⟨1957472710884981743495347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10439854458053235965308517 1957472710884981743495347)
            ·
              refine ⟨2936209066327472615243021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1957472710884981743495347 2936209066327472615243021)
              ·
                refine ⟨1101078399872802230716133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2936209066327472615243021 1101078399872802230716133)
                ·
                  refine ⟨206452199976150418259275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1101078399872802230716133 206452199976150418259275)
                  ·
                    rfl

theorem cell22_1809289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 4, 1, 3, 4].length) (baseStart_1809289 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1809289 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1809289 prefixEnd_1809289 := by exact prefixLift 1809289
  have htrace : WordTrace (prefixWord ++ tailWord_1809289) baseStart_1809289 baseEnd_1809289 := by
    simpa [prefixWord, tailWord_1809289, baseEnd_1809289] using wordTrace_append hprefix tailTrace_1809289
  have hstable : (prefixWord ++ tailWord_1809289).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1809289).length < 2 ^ (prefixWord ++ tailWord_1809289).sum := by decide
  have hdescent : baseEnd_1809289 < baseStart_1809289 := by decide
  rcases family_descends (prefixWord ++ tailWord_1809289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1809306 : List Nat := [3, 1, 1, 4, 3, 1, 3, 2, 4]
def baseStart_1809306 : Nat := 118140960795 + 1809306 * 2 ^ 59
def prefixEnd_1809306 : Nat := 4983230072969 + 3 ^ 40 * 1809306 * 2
def baseEnd_1809306 : Nat := 206454139791956292367591

theorem tailTrace_1809306 : CollatzResearch.WordTrace tailWord_1809306 prefixEnd_1809306 206454139791956292367591 := by
  unfold tailWord_1809306
  simp only [CollatzResearch.WordTrace]
  refine ⟨16497702795800210427193943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43993874122133894472517181 16497702795800210427193943)
  ·
    refine ⟨24746554193700315640790915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16497702795800210427193943 24746554193700315640790915)
    ·
      refine ⟨37119831290550473461186373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24746554193700315640790915 37119831290550473461186373)
      ·
        refine ⟨6959968366978213773972445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37119831290550473461186373 6959968366978213773972445)
        ·
          refine ⟨2609988137616830165239667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6959968366978213773972445 2609988137616830165239667)
          ·
            refine ⟨3914982206425245247859501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2609988137616830165239667 3914982206425245247859501)
            ·
              refine ⟨1468118327409466967947313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3914982206425245247859501 1468118327409466967947313)
              ·
                refine ⟨1101088745557100225960485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1468118327409466967947313 1101088745557100225960485)
                ·
                  refine ⟨206454139791956292367591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1101088745557100225960485 206454139791956292367591)
                  ·
                    rfl

theorem cell22_1809306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 3, 2, 4].length) (baseStart_1809306 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1809306 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1809306 prefixEnd_1809306 := by exact prefixLift 1809306
  have htrace : WordTrace (prefixWord ++ tailWord_1809306) baseStart_1809306 baseEnd_1809306 := by
    simpa [prefixWord, tailWord_1809306, baseEnd_1809306] using wordTrace_append hprefix tailTrace_1809306
  have hstable : (prefixWord ++ tailWord_1809306).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1809306).length < 2 ^ (prefixWord ++ tailWord_1809306).sum := by decide
  have hdescent : baseEnd_1809306 < baseStart_1809306 := by decide
  rcases family_descends (prefixWord ++ tailWord_1809306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1809357 : List Nat := [1, 6, 3, 1, 1, 2, 2, 2, 4]
def baseStart_1809357 : Nat := 118140960795 + 1809357 * 2 ^ 59
def prefixEnd_1809357 : Nat := 4983230072969 + 3 ^ 40 * 1809357 * 2
def baseEnd_1809357 : Nat := 206459959239373914692539

theorem tailTrace_1809357 : CollatzResearch.WordTrace tailWord_1809357 prefixEnd_1809357 206459959239373914692539 := by
  unfold tailWord_1809357
  simp only [CollatzResearch.WordTrace]
  refine ⟨65992671306016077418882325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43995114204010718279254883 65992671306016077418882325)
  ·
    refine ⟨3093406467469503629010109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 65992671306016077418882325 3093406467469503629010109)
    ·
      refine ⟨1160027425301063860878791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3093406467469503629010109 1160027425301063860878791)
      ·
        refine ⟨1740041137951595791318187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1160027425301063860878791 1740041137951595791318187)
        ·
          refine ⟨2610061706927393686977281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1740041137951595791318187 2610061706927393686977281)
          ·
            refine ⟨1957546280195545265232961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2610061706927393686977281 1957546280195545265232961)
            ·
              refine ⟨1468159710146658948924721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1957546280195545265232961 1468159710146658948924721)
              ·
                refine ⟨1101119782609994211693541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1468159710146658948924721 1101119782609994211693541)
                ·
                  refine ⟨206459959239373914692539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1101119782609994211693541 206459959239373914692539)
                  ·
                    rfl

theorem cell22_1809357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 2, 2, 2, 4].length) (baseStart_1809357 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1809357 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1809357 prefixEnd_1809357 := by exact prefixLift 1809357
  have htrace : WordTrace (prefixWord ++ tailWord_1809357) baseStart_1809357 baseEnd_1809357 := by
    simpa [prefixWord, tailWord_1809357, baseEnd_1809357] using wordTrace_append hprefix tailTrace_1809357
  have hstable : (prefixWord ++ tailWord_1809357).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1809357).length < 2 ^ (prefixWord ++ tailWord_1809357).sum := by decide
  have hdescent : baseEnd_1809357 < baseStart_1809357 := by decide
  rcases family_descends (prefixWord ++ tailWord_1809357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1809360 : List Nat := [2, 1, 1, 1, 1, 2, 3, 4, 2, 5]
def baseStart_1809360 : Nat := 118140960795 + 1809360 * 2 ^ 59
def prefixEnd_1809360 : Nat := 4983230072969 + 3 ^ 40 * 1809360 * 2
def baseEnd_1809360 : Nat := 619380904679430736252607

theorem tailTrace_1809360 : CollatzResearch.WordTrace tailWord_1809360 prefixEnd_1809360 619380904679430736252607 := by
  unfold tailWord_1809360
  simp only [CollatzResearch.WordTrace]
  refine ⟨32996390362502604465620767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43995187150003472620827689 32996390362502604465620767)
  ·
    refine ⟨49494585543753906698431151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32996390362502604465620767 49494585543753906698431151)
    ·
      refine ⟨74241878315630860047646727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49494585543753906698431151 74241878315630860047646727)
      ·
        refine ⟨111362817473446290071470091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74241878315630860047646727 111362817473446290071470091)
        ·
          refine ⟨167044226210169435107205137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111362817473446290071470091 167044226210169435107205137)
          ·
            refine ⟨125283169657627076330403853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 167044226210169435107205137 125283169657627076330403853)
            ·
              refine ⟨46981188621610153623901445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 125283169657627076330403853 46981188621610153623901445)
              ·
                refine ⟨8808972866551903804481521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46981188621610153623901445 8808972866551903804481521)
                ·
                  refine ⟨6606729649913927853361141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8808972866551903804481521 6606729649913927853361141)
                  ·
                    refine ⟨619380904679430736252607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6606729649913927853361141 619380904679430736252607)
                    ·
                      rfl

theorem cell22_1809360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 4, 2, 5].length) (baseStart_1809360 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1809360 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1809360 prefixEnd_1809360 := by exact prefixLift 1809360
  have htrace : WordTrace (prefixWord ++ tailWord_1809360) baseStart_1809360 baseEnd_1809360 := by
    simpa [prefixWord, tailWord_1809360, baseEnd_1809360] using wordTrace_append hprefix tailTrace_1809360
  have hstable : (prefixWord ++ tailWord_1809360).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1809360).length < 2 ^ (prefixWord ++ tailWord_1809360).sum := by decide
  have hdescent : baseEnd_1809360 < baseStart_1809360 := by decide
  rcases family_descends (prefixWord ++ tailWord_1809360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1809392 : List Nat := [2, 1, 1, 1, 3, 2, 1, 6, 1, 4]
def baseStart_1809392 : Nat := 118140960795 + 1809392 * 2 ^ 59
def prefixEnd_1809392 : Nat := 4983230072969 + 3 ^ 40 * 1809392 * 2
def baseEnd_1809392 : Nat := 619391858933393319452509

theorem tailTrace_1809392 : CollatzResearch.WordTrace tailWord_1809392 prefixEnd_1809392 619391858933393319452509 := by
  unfold tailWord_1809392
  simp only [CollatzResearch.WordTrace]
  refine ⟨32996973930444639198203215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43995965240592852264270953 32996973930444639198203215)
  ·
    refine ⟨49495460895666958797304823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32996973930444639198203215 49495460895666958797304823)
    ·
      refine ⟨74243191343500438195957235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49495460895666958797304823 74243191343500438195957235)
      ·
        refine ⟨111364787015250657293935853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74243191343500438195957235 111364787015250657293935853)
        ·
          refine ⟨41761795130718996485225945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111364787015250657293935853 41761795130718996485225945)
          ·
            refine ⟨31321346348039247363919459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41761795130718996485225945 31321346348039247363919459)
            ·
              refine ⟨46982019522058871045879189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31321346348039247363919459 46982019522058871045879189)
              ·
                refine ⟨2202282165096509580275587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 46982019522058871045879189 2202282165096509580275587)
                ·
                  refine ⟨3303423247644764370413381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2202282165096509580275587 3303423247644764370413381)
                  ·
                    refine ⟨619391858933393319452509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3303423247644764370413381 619391858933393319452509)
                    ·
                      rfl

theorem cell22_1809392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 6, 1, 4].length) (baseStart_1809392 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1809392 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1809392 prefixEnd_1809392 := by exact prefixLift 1809392
  have htrace : WordTrace (prefixWord ++ tailWord_1809392) baseStart_1809392 baseEnd_1809392 := by
    simpa [prefixWord, tailWord_1809392, baseEnd_1809392] using wordTrace_append hprefix tailTrace_1809392
  have hstable : (prefixWord ++ tailWord_1809392).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1809392).length < 2 ^ (prefixWord ++ tailWord_1809392).sum := by decide
  have hdescent : baseEnd_1809392 < baseStart_1809392 := by decide
  rcases family_descends (prefixWord ++ tailWord_1809392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1809409 : List Nat := [1, 2, 4, 1, 2, 3, 1, 3, 1, 4]
def baseStart_1809409 : Nat := 118140960795 + 1809409 * 2 ^ 59
def prefixEnd_1809409 : Nat := 4983230072969 + 3 ^ 40 * 1809409 * 2
def baseEnd_1809409 : Nat := 619397678380810941777457

theorem tailTrace_1809409 : CollatzResearch.WordTrace tailWord_1809409 prefixEnd_1809409 619397678380810941777457 := by
  unfold tailWord_1809409
  simp only [CollatzResearch.WordTrace]
  refine ⟨65994567901827690299775281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43996378601218460199850187 65994567901827690299775281)
  ·
    refine ⟨49495925926370767724831461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65994567901827690299775281 49495925926370767724831461)
    ·
      refine ⟨9280486111194518948405899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49495925926370767724831461 9280486111194518948405899)
      ·
        refine ⟨13920729166791778422608849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9280486111194518948405899 13920729166791778422608849)
        ·
          refine ⟨10440546875093833816956637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13920729166791778422608849 10440546875093833816956637)
          ·
            refine ⟨3915205078160187681358739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10440546875093833816956637 3915205078160187681358739)
            ·
              refine ⟨5872807617240281522038109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3915205078160187681358739 5872807617240281522038109)
              ·
                refine ⟨2202302856465105570764291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5872807617240281522038109 2202302856465105570764291)
                ·
                  refine ⟨3303454284697658356146437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2202302856465105570764291 3303454284697658356146437)
                  ·
                    refine ⟨619397678380810941777457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3303454284697658356146437 619397678380810941777457)
                    ·
                      rfl

theorem cell22_1809409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 1, 3, 1, 4].length) (baseStart_1809409 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1809409 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1809409 prefixEnd_1809409 := by exact prefixLift 1809409
  have htrace : WordTrace (prefixWord ++ tailWord_1809409) baseStart_1809409 baseEnd_1809409 := by
    simpa [prefixWord, tailWord_1809409, baseEnd_1809409] using wordTrace_append hprefix tailTrace_1809409
  have hstable : (prefixWord ++ tailWord_1809409).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1809409).length < 2 ^ (prefixWord ++ tailWord_1809409).sum := by decide
  have hdescent : baseEnd_1809409 < baseStart_1809409 := by decide
  rcases family_descends (prefixWord ++ tailWord_1809409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1809439 : List Nat := [1, 1, 2, 4, 1, 5, 1, 1, 1, 5]
def baseStart_1809439 : Nat := 118140960795 + 1809439 * 2 ^ 59
def prefixEnd_1809439 : Nat := 4983230072969 + 3 ^ 40 * 1809439 * 2
def baseEnd_1809439 : Nat := 619407947993900863527365

theorem tailTrace_1809439 : CollatzResearch.WordTrace tailWord_1809439 prefixEnd_1809439 619407947993900863527365 := by
  unfold tailWord_1809439
  simp only [CollatzResearch.WordTrace]
  refine ⟨65995662091719005423367371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43997108061146003615578247 65995662091719005423367371)
  ·
    refine ⟨98993493137578508135051057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65995662091719005423367371 98993493137578508135051057)
    ·
      refine ⟨74245119853183881101288293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98993493137578508135051057 74245119853183881101288293)
      ·
        refine ⟨13920959972471977706491555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74245119853183881101288293 13920959972471977706491555)
        ·
          refine ⟨20881439958707966559737333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13920959972471977706491555 20881439958707966559737333)
          ·
            refine ⟨1957634996128871864975375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 20881439958707966559737333 1957634996128871864975375)
            ·
              refine ⟨2936452494193307797463063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1957634996128871864975375 2936452494193307797463063)
              ·
                refine ⟨4404678741289961696194595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2936452494193307797463063 4404678741289961696194595)
                ·
                  refine ⟨6607018111934942544291893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4404678741289961696194595 6607018111934942544291893)
                  ·
                    refine ⟨619407947993900863527365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6607018111934942544291893 619407947993900863527365)
                    ·
                      rfl

theorem cell22_1809439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 5, 1, 1, 1, 5].length) (baseStart_1809439 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1809439 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1809439 prefixEnd_1809439 := by exact prefixLift 1809439
  have htrace : WordTrace (prefixWord ++ tailWord_1809439) baseStart_1809439 baseEnd_1809439 := by
    simpa [prefixWord, tailWord_1809439, baseEnd_1809439] using wordTrace_append hprefix tailTrace_1809439
  have hstable : (prefixWord ++ tailWord_1809439).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1809439).length < 2 ^ (prefixWord ++ tailWord_1809439).sum := by decide
  have hdescent : baseEnd_1809439 < baseStart_1809439 := by decide
  rcases family_descends (prefixWord ++ tailWord_1809439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1809454 : List Nat := [4, 1, 3, 1, 1, 1, 2, 3, 2, 4]
def baseStart_1809454 : Nat := 118140960795 + 1809454 * 2 ^ 59
def prefixEnd_1809454 : Nat := 4983230072969 + 3 ^ 40 * 1809454 * 2
def baseEnd_1809454 : Nat := 619413082800445824402319

theorem tailTrace_1809454 : CollatzResearch.WordTrace tailWord_1809454 prefixEnd_1809454 619413082800445824402319 := by
  unfold tailWord_1809454
  simp only [CollatzResearch.WordTrace]
  refine ⟨8249526148333082873145427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43997472791109775323442277 8249526148333082873145427)
  ·
    refine ⟨12374289222499624309718141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8249526148333082873145427 12374289222499624309718141)
    ·
      refine ⟨4640358458437359116144303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12374289222499624309718141 4640358458437359116144303)
      ·
        refine ⟨6960537687656038674216455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4640358458437359116144303 6960537687656038674216455)
        ·
          refine ⟨10440806531484058011324683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6960537687656038674216455 10440806531484058011324683)
          ·
            refine ⟨15661209797226087016987025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10440806531484058011324683 15661209797226087016987025)
            ·
              refine ⟨11745907347919565262740269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15661209797226087016987025 11745907347919565262740269)
              ·
                refine ⟨4404715255469836973527601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11745907347919565262740269 4404715255469836973527601)
                ·
                  refine ⟨3303536441602377730145701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4404715255469836973527601 3303536441602377730145701)
                  ·
                    refine ⟨619413082800445824402319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3303536441602377730145701 619413082800445824402319)
                    ·
                      rfl

theorem cell22_1809454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 3, 2, 4].length) (baseStart_1809454 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1809454 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1809454 prefixEnd_1809454 := by exact prefixLift 1809454
  have htrace : WordTrace (prefixWord ++ tailWord_1809454) baseStart_1809454 baseEnd_1809454 := by
    simpa [prefixWord, tailWord_1809454, baseEnd_1809454] using wordTrace_append hprefix tailTrace_1809454
  have hstable : (prefixWord ++ tailWord_1809454).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1809454).length < 2 ^ (prefixWord ++ tailWord_1809454).sum := by decide
  have hdescent : baseEnd_1809454 < baseStart_1809454 := by decide
  rcases family_descends (prefixWord ++ tailWord_1809454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1809559 : List Nat := [1, 1, 3, 3, 3, 2, 1, 2, 6]
def baseStart_1809559 : Nat := 118140960795 + 1809559 * 2 ^ 59
def prefixEnd_1809559 : Nat := 4983230072969 + 3 ^ 40 * 1809559 * 2
def baseEnd_1809559 : Nat := 206483008815420183508999

theorem tailTrace_1809559 : CollatzResearch.WordTrace tailWord_1809559 prefixEnd_1809559 206483008815420183508999 := by
  unfold tailWord_1809559
  simp only [CollatzResearch.WordTrace]
  refine ⟨66000038851284265917735731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44000025900856177278490487 66000038851284265917735731)
  ·
    refine ⟨99000058276926398876603597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66000038851284265917735731 99000058276926398876603597)
    ·
      refine ⟨37125021853847399578726349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99000058276926398876603597 37125021853847399578726349)
      ·
        refine ⟨13921883195192774842022381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37125021853847399578726349 13921883195192774842022381)
        ·
          refine ⟨5220706198197290565758393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13921883195192774842022381 5220706198197290565758393)
          ·
            refine ⟨3915529648647967924318795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5220706198197290565758393 3915529648647967924318795)
            ·
              refine ⟨5873294472971951886478193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3915529648647967924318795 5873294472971951886478193)
              ·
                refine ⟨4404970854728963914858645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5873294472971951886478193 4404970854728963914858645)
                ·
                  refine ⟨206483008815420183508999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4404970854728963914858645 206483008815420183508999)
                  ·
                    rfl

theorem cell22_1809559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 1, 2, 6].length) (baseStart_1809559 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1809559 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1809559 prefixEnd_1809559 := by exact prefixLift 1809559
  have htrace : WordTrace (prefixWord ++ tailWord_1809559) baseStart_1809559 baseEnd_1809559 := by
    simpa [prefixWord, tailWord_1809559, baseEnd_1809559] using wordTrace_append hprefix tailTrace_1809559
  have hstable : (prefixWord ++ tailWord_1809559).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1809559).length < 2 ^ (prefixWord ++ tailWord_1809559).sum := by decide
  have hdescent : baseEnd_1809559 < baseStart_1809559 := by decide
  rcases family_descends (prefixWord ++ tailWord_1809559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1809578 : List Nat := [3, 1, 5, 1, 1, 2, 1, 3, 1, 4]
def baseStart_1809578 : Nat := 118140960795 + 1809578 * 2 ^ 59
def prefixEnd_1809578 : Nat := 4983230072969 + 3 ^ 40 * 1809578 * 2
def baseEnd_1809578 : Nat := 619455530534550834301939

theorem tailTrace_1809578 : CollatzResearch.WordTrace tailWord_1809578 prefixEnd_1809578 619455530534550834301939 := by
  unfold tailWord_1809578
  simp only [CollatzResearch.WordTrace]
  refine ⟨16500182959553858040669347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44000487892143621441784925 16500182959553858040669347)
  ·
    refine ⟨24750274439330787061004021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16500182959553858040669347 24750274439330787061004021)
    ·
      refine ⟨2320338228687261286969127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 24750274439330787061004021 2320338228687261286969127)
      ·
        refine ⟨3480507343030891930453691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2320338228687261286969127 3480507343030891930453691)
        ·
          refine ⟨5220761014546337895680537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3480507343030891930453691 5220761014546337895680537)
          ·
            refine ⟨3915570760909753421760403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5220761014546337895680537 3915570760909753421760403)
            ·
              refine ⟨5873356141364630132640605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3915570760909753421760403 5873356141364630132640605)
              ·
                refine ⟨2202508553011736299740227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5873356141364630132640605 2202508553011736299740227)
                ·
                  refine ⟨3303762829517604449610341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2202508553011736299740227 3303762829517604449610341)
                  ·
                    refine ⟨619455530534550834301939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3303762829517604449610341 619455530534550834301939)
                    ·
                      rfl

theorem cell22_1809578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 1, 3, 1, 4].length) (baseStart_1809578 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1809578 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1809578 prefixEnd_1809578 := by exact prefixLift 1809578
  have htrace : WordTrace (prefixWord ++ tailWord_1809578) baseStart_1809578 baseEnd_1809578 := by
    simpa [prefixWord, tailWord_1809578, baseEnd_1809578] using wordTrace_append hprefix tailTrace_1809578
  have hstable : (prefixWord ++ tailWord_1809578).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1809578).length < 2 ^ (prefixWord ++ tailWord_1809578).sum := by decide
  have hdescent : baseEnd_1809578 < baseStart_1809578 := by decide
  rcases family_descends (prefixWord ++ tailWord_1809578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1809621 : List Nat := [1, 3, 2, 4, 1, 1, 4, 6]
def baseStart_1809621 : Nat := 118140960795 + 1809621 * 2 ^ 59
def prefixEnd_1809621 : Nat := 4983230072969 + 3 ^ 40 * 1809621 * 2
def baseEnd_1809621 : Nat := 68830027812590339497423

theorem tailTrace_1809621 : CollatzResearch.WordTrace tailWord_1809621 prefixEnd_1809621 68830027812590339497423 := by
  unfold tailWord_1809621
  simp only [CollatzResearch.WordTrace]
  refine ⟨66002300177059650506492717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44001533451373100337661811 66002300177059650506492717)
  ·
    refine ⟨24750862566397368939934769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66002300177059650506492717 24750862566397368939934769)
    ·
      refine ⟨18563146924798026704951077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24750862566397368939934769 18563146924798026704951077)
      ·
        refine ⟨3480590048399630007178327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18563146924798026704951077 3480590048399630007178327)
        ·
          refine ⟨5220885072599445010767491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3480590048399630007178327 5220885072599445010767491)
          ·
            refine ⟨7831327608899167516151237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5220885072599445010767491 7831327608899167516151237)
            ·
              refine ⟨1468373926668593909278357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7831327608899167516151237 1468373926668593909278357)
              ·
                refine ⟨68830027812590339497423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1468373926668593909278357 68830027812590339497423)
                ·
                  rfl

theorem cell22_1809621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 4, 6].length) (baseStart_1809621 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1809621 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1809621 prefixEnd_1809621 := by exact prefixLift 1809621
  have htrace : WordTrace (prefixWord ++ tailWord_1809621) baseStart_1809621 baseEnd_1809621 := by
    simpa [prefixWord, tailWord_1809621, baseEnd_1809621] using wordTrace_append hprefix tailTrace_1809621
  have hstable : (prefixWord ++ tailWord_1809621).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1809621).length < 2 ^ (prefixWord ++ tailWord_1809621).sum := by decide
  have hdescent : baseEnd_1809621 < baseStart_1809621 := by decide
  rcases family_descends (prefixWord ++ tailWord_1809621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1809649 : List Nat := [1, 2, 2, 2, 2, 1, 1, 6, 5]
def baseStart_1809649 : Nat := 118140960795 + 1809649 * 2 ^ 59
def prefixEnd_1809649 : Nat := 4983230072969 + 3 ^ 40 * 1809649 * 2
def baseEnd_1809649 : Nat := 206493278428510105258907

theorem tailTrace_1809649 : CollatzResearch.WordTrace tailWord_1809649 prefixEnd_1809649 206493278428510105258907 := by
  unfold tailWord_1809649
  simp only [CollatzResearch.WordTrace]
  refine ⟨66003321420958211288512001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44002214280638807525674667 66003321420958211288512001)
  ·
    refine ⟨49502491065718658466384001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66003321420958211288512001 49502491065718658466384001)
    ·
      refine ⟨37126868299288993849788001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49502491065718658466384001 37126868299288993849788001)
      ·
        refine ⟨27845151224466745387341001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37126868299288993849788001 27845151224466745387341001)
        ·
          refine ⟨20883863418350059040505751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27845151224466745387341001 20883863418350059040505751)
          ·
            refine ⟨31325795127525088560758627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20883863418350059040505751 31325795127525088560758627)
            ·
              refine ⟨46988692691287632841137941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31325795127525088560758627 46988692691287632841137941)
              ·
                refine ⟨2202594969904107789428341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 46988692691287632841137941 2202594969904107789428341)
                ·
                  refine ⟨206493278428510105258907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2202594969904107789428341 206493278428510105258907)
                  ·
                    rfl

theorem cell22_1809649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 6, 5].length) (baseStart_1809649 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1809649 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1809649 prefixEnd_1809649 := by exact prefixLift 1809649
  have htrace : WordTrace (prefixWord ++ tailWord_1809649) baseStart_1809649 baseEnd_1809649 := by
    simpa [prefixWord, tailWord_1809649, baseEnd_1809649] using wordTrace_append hprefix tailTrace_1809649
  have hstable : (prefixWord ++ tailWord_1809649).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1809649).length < 2 ^ (prefixWord ++ tailWord_1809649).sum := by decide
  have hdescent : baseEnd_1809649 < baseStart_1809649 := by decide
  rcases family_descends (prefixWord ++ tailWord_1809649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1809760 : List Nat := [2, 1, 1, 3, 4, 3, 1, 2, 2, 3]
def baseStart_1809760 : Nat := 118140960795 + 1809760 * 2 ^ 59
def prefixEnd_1809760 : Nat := 4983230072969 + 3 ^ 40 * 1809760 * 2
def baseEnd_1809760 : Nat := 619517832853963026251381

theorem tailTrace_1809760 : CollatzResearch.WordTrace tailWord_1809760 prefixEnd_1809760 619517832853963026251381 := by
  unfold tailWord_1809760
  simp only [CollatzResearch.WordTrace]
  refine ⟨33003684961778038622901367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44004913282370718163868489 33003684961778038622901367)
  ·
    refine ⟨49505527442667057934352051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33003684961778038622901367 49505527442667057934352051)
    ·
      refine ⟨74258291164000586901528077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49505527442667057934352051 74258291164000586901528077)
      ·
        refine ⟨27846859186500220088073029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74258291164000586901528077 27846859186500220088073029)
        ·
          refine ⟨5221286097468791266513693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27846859186500220088073029 5221286097468791266513693)
          ·
            refine ⟨1957982286550796724942635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5221286097468791266513693 1957982286550796724942635)
            ·
              refine ⟨2936973429826195087413953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1957982286550796724942635 2936973429826195087413953)
              ·
                refine ⟨2202730072369646315560465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2936973429826195087413953 2202730072369646315560465)
                ·
                  refine ⟨1652047554277234736670349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2202730072369646315560465 1652047554277234736670349)
                  ·
                    refine ⟨619517832853963026251381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1652047554277234736670349 619517832853963026251381)
                    ·
                      rfl

theorem cell22_1809760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 3, 1, 2, 2, 3].length) (baseStart_1809760 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1809760 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1809760 prefixEnd_1809760 := by exact prefixLift 1809760
  have htrace : WordTrace (prefixWord ++ tailWord_1809760) baseStart_1809760 baseEnd_1809760 := by
    simpa [prefixWord, tailWord_1809760, baseEnd_1809760] using wordTrace_append hprefix tailTrace_1809760
  have hstable : (prefixWord ++ tailWord_1809760).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1809760).length < 2 ^ (prefixWord ++ tailWord_1809760).sum := by decide
  have hdescent : baseEnd_1809760 < baseStart_1809760 := by decide
  rcases family_descends (prefixWord ++ tailWord_1809760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1809769 : List Nat := [1, 2, 1, 1, 1, 3, 2, 3, 2, 6]
def baseStart_1809769 : Nat := 118140960795 + 1809769 * 2 ^ 59
def prefixEnd_1809769 : Nat := 4983230072969 + 3 ^ 40 * 1809769 * 2
def baseEnd_1809769 : Nat := 619520913737890002776353

theorem tailTrace_1809769 : CollatzResearch.WordTrace tailWord_1809769 prefixEnd_1809769 619520913737890002776353 := by
  unfold tailWord_1809769
  simp only [CollatzResearch.WordTrace]
  refine ⟨66007698180523471782880361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44005132120348981188586907 66007698180523471782880361)
  ·
    refine ⟨49505773635392603837160271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66007698180523471782880361 49505773635392603837160271)
    ·
      refine ⟨74258660453088905755740407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49505773635392603837160271 74258660453088905755740407)
      ·
        refine ⟨111387990679633358633610611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74258660453088905755740407 111387990679633358633610611)
        ·
          refine ⟨167081986019450037950415917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111387990679633358633610611 167081986019450037950415917)
          ·
            refine ⟨62655744757293764231405969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 167081986019450037950415917 62655744757293764231405969)
            ·
              refine ⟨46991808567970323173554477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62655744757293764231405969 46991808567970323173554477)
              ·
                refine ⟨17621928212988871190082929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46991808567970323173554477 17621928212988871190082929)
                ·
                  refine ⟨13216446159741653392562197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17621928212988871190082929 13216446159741653392562197)
                  ·
                    refine ⟨619520913737890002776353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13216446159741653392562197 619520913737890002776353)
                    ·
                      rfl

theorem cell22_1809769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 3, 2, 6].length) (baseStart_1809769 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1809769 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1809769 prefixEnd_1809769 := by exact prefixLift 1809769
  have htrace : WordTrace (prefixWord ++ tailWord_1809769) baseStart_1809769 baseEnd_1809769 := by
    simpa [prefixWord, tailWord_1809769, baseEnd_1809769] using wordTrace_append hprefix tailTrace_1809769
  have hstable : (prefixWord ++ tailWord_1809769).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1809769).length < 2 ^ (prefixWord ++ tailWord_1809769).sum := by decide
  have hdescent : baseEnd_1809769 < baseStart_1809769 := by decide
  rcases family_descends (prefixWord ++ tailWord_1809769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
