import V185TrunkScan23Chunk0735

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_4352343 : List Nat := [1, 1, 3, 2, 3, 1, 4, 1, 3, 1, 3]
def baseStart_4352343 : Nat := 118140960795 + 4352343 * 2 ^ 59
def prefixEnd_4352343 : Nat := 4983230072969 + 3 ^ 40 * 4352343 * 2
def baseEnd_4352343 : Nat := 2234843932231570171696445

theorem tailTrace_4352343 : CollatzResearch.WordTrace tailWord_4352343 prefixEnd_4352343 2234843932231570171696445 := by
  unfold tailWord_4352343
  simp only [CollatzResearch.WordTrace]
  refine ⟨158742990471212106850701683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105828660314141404567134455 158742990471212106850701683)
  ·
    refine ⟨238114485706818160276052525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158742990471212106850701683 238114485706818160276052525)
    ·
      refine ⟨89292932140056810103519697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 238114485706818160276052525 89292932140056810103519697)
      ·
        refine ⟨66969699105042607577639773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89292932140056810103519697 66969699105042607577639773)
        ·
          refine ⟨25113637164390977841614915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66969699105042607577639773 25113637164390977841614915)
          ·
            refine ⟨37670455746586466762422373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25113637164390977841614915 37670455746586466762422373)
            ·
              refine ⟨7063210452484962517954195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37670455746586466762422373 7063210452484962517954195)
              ·
                refine ⟨10594815678727443776931293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7063210452484962517954195 10594815678727443776931293)
                ·
                  refine ⟨3973055879522791416349235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10594815678727443776931293 3973055879522791416349235)
                  ·
                    refine ⟨5959583819284187124523853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3973055879522791416349235 5959583819284187124523853)
                    ·
                      refine ⟨2234843932231570171696445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5959583819284187124523853 2234843932231570171696445)
                      ·
                        rfl

theorem cell23_4352343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 4, 1, 3, 1, 3].length) (baseStart_4352343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4352343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4352343 prefixEnd_4352343 := by exact prefixLift 4352343
  have htrace : WordTrace (prefixWord ++ tailWord_4352343) baseStart_4352343 baseEnd_4352343 := by
    simpa [prefixWord, tailWord_4352343, baseEnd_4352343] using wordTrace_append hprefix tailTrace_4352343
  have hstable : (prefixWord ++ tailWord_4352343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4352343).length < 2 ^ (prefixWord ++ tailWord_4352343).sum := by decide
  have hdescent : baseEnd_4352343 < baseStart_4352343 := by decide
  rcases family_descends (prefixWord ++ tailWord_4352343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4352369 : List Nat := [1, 2, 2, 2, 1, 2, 1, 1, 5, 1, 5]
def baseStart_4352369 : Nat := 118140960795 + 4352369 * 2 ^ 59
def prefixEnd_4352369 : Nat := 4983230072969 + 3 ^ 40 * 4352369 * 2
def baseEnd_4352369 : Nat := 2234857282728587069971325

theorem tailTrace_4352369 : CollatzResearch.WordTrace tailWord_4352369 prefixEnd_4352369 2234857282728587069971325 := by
  unfold tailWord_4352369
  simp only [CollatzResearch.WordTrace]
  refine ⟨158743938769117913291148161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105829292512745275527432107 158743938769117913291148161)
  ·
    refine ⟨119057954076838434968361121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 158743938769117913291148161 119057954076838434968361121)
    ·
      refine ⟨89293465557628826226270841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119057954076838434968361121 89293465557628826226270841)
      ·
        refine ⟨66970099168221619669703131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89293465557628826226270841 66970099168221619669703131)
        ·
          refine ⟨100455148752332429504554697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66970099168221619669703131 100455148752332429504554697)
          ·
            refine ⟨75341361564249322128416023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 100455148752332429504554697 75341361564249322128416023)
            ·
              refine ⟨113012042346373983192624035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75341361564249322128416023 113012042346373983192624035)
              ·
                refine ⟨169518063519560974788936053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 113012042346373983192624035 169518063519560974788936053)
                ·
                  refine ⟨15892318454958841386462755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 169518063519560974788936053 15892318454958841386462755)
                  ·
                    refine ⟨23838477682438262079694133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15892318454958841386462755 23838477682438262079694133)
                    ·
                      refine ⟨2234857282728587069971325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23838477682438262079694133 2234857282728587069971325)
                      ·
                        rfl

theorem cell23_4352369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 1, 5, 1, 5].length) (baseStart_4352369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4352369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4352369 prefixEnd_4352369 := by exact prefixLift 4352369
  have htrace : WordTrace (prefixWord ++ tailWord_4352369) baseStart_4352369 baseEnd_4352369 := by
    simpa [prefixWord, tailWord_4352369, baseEnd_4352369] using wordTrace_append hprefix tailTrace_4352369
  have hstable : (prefixWord ++ tailWord_4352369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4352369).length < 2 ^ (prefixWord ++ tailWord_4352369).sum := by decide
  have hdescent : baseEnd_4352369 < baseStart_4352369 := by decide
  rcases family_descends (prefixWord ++ tailWord_4352369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4352394 : List Nat := [3, 1, 2, 5, 2, 1, 1, 1, 3, 1, 3]
def baseStart_4352394 : Nat := 118140960795 + 4352394 * 2 ^ 59
def prefixEnd_4352394 : Nat := 4983230072969 + 3 ^ 40 * 4352394 * 2
def baseEnd_4352394 : Nat := 2234870119744949472158711

theorem tailTrace_4352394 : CollatzResearch.WordTrace tailWord_4352394 prefixEnd_4352394 2234870119744949472158711 := by
  unfold tailWord_4352394
  simp only [CollatzResearch.WordTrace]
  refine ⟨39686212648506835640202059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105829900396018228373872157 39686212648506835640202059)
  ·
    refine ⟨59529318972760253460303089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39686212648506835640202059 59529318972760253460303089)
    ·
      refine ⟨44646989229570190095227317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59529318972760253460303089 44646989229570190095227317)
      ·
        refine ⟨4185655240272205321427561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 44646989229570190095227317 4185655240272205321427561)
        ·
          refine ⟨3139241430204153991070671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4185655240272205321427561 3139241430204153991070671)
          ·
            refine ⟨4708862145306230986606007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3139241430204153991070671 4708862145306230986606007)
            ·
              refine ⟨7063293217959346479909011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4708862145306230986606007 7063293217959346479909011)
              ·
                refine ⟨10594939826939019719863517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7063293217959346479909011 10594939826939019719863517)
                ·
                  refine ⟨3973102435102132394948819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10594939826939019719863517 3973102435102132394948819)
                  ·
                    refine ⟨5959653652653198592423229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3973102435102132394948819 5959653652653198592423229)
                    ·
                      refine ⟨2234870119744949472158711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5959653652653198592423229 2234870119744949472158711)
                      ·
                        rfl

theorem cell23_4352394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 1, 1, 1, 3, 1, 3].length) (baseStart_4352394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4352394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4352394 prefixEnd_4352394 := by exact prefixLift 4352394
  have htrace : WordTrace (prefixWord ++ tailWord_4352394) baseStart_4352394 baseEnd_4352394 := by
    simpa [prefixWord, tailWord_4352394, baseEnd_4352394] using wordTrace_append hprefix tailTrace_4352394
  have hstable : (prefixWord ++ tailWord_4352394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4352394).length < 2 ^ (prefixWord ++ tailWord_4352394).sum := by decide
  have hdescent : baseEnd_4352394 < baseStart_4352394 := by decide
  rcases family_descends (prefixWord ++ tailWord_4352394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4352409 : List Nat := [1, 2, 1, 2, 1, 4, 1, 1, 2, 2, 6]
def baseStart_4352409 : Nat := 118140960795 + 4352409 * 2 ^ 59
def prefixEnd_4352409 : Nat := 4983230072969 + 3 ^ 40 * 4352409 * 2
def baseEnd_4352409 : Nat := 2234877821954766913471141

theorem tailTrace_4352409 : CollatzResearch.WordTrace tailWord_4352409 prefixEnd_4352409 2234877821954766913471141 := by
  unfold tailWord_4352409
  simp only [CollatzResearch.WordTrace]
  refine ⟨158745397688973000122604281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105830265125982000081736187 158745397688973000122604281)
  ·
    refine ⟨119059048266729750091953211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 158745397688973000122604281 119059048266729750091953211)
    ·
      refine ⟨178588572400094625137929817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119059048266729750091953211 178588572400094625137929817)
      ·
        refine ⟨133941429300070968853447363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 178588572400094625137929817 133941429300070968853447363)
        ·
          refine ⟨200912143950106453280171045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 133941429300070968853447363 200912143950106453280171045)
          ·
            refine ⟨37671026990644959990032071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 200912143950106453280171045 37671026990644959990032071)
            ·
              refine ⟨56506540485967439985048107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37671026990644959990032071 56506540485967439985048107)
              ·
                refine ⟨84759810728951159977572161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56506540485967439985048107 84759810728951159977572161)
                ·
                  refine ⟨63569858046713369983179121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 84759810728951159977572161 63569858046713369983179121)
                  ·
                    refine ⟨47677393535035027487384341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 63569858046713369983179121 47677393535035027487384341)
                    ·
                      refine ⟨2234877821954766913471141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 47677393535035027487384341 2234877821954766913471141)
                      ·
                        rfl

theorem cell23_4352409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 1, 2, 2, 6].length) (baseStart_4352409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4352409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4352409 prefixEnd_4352409 := by exact prefixLift 4352409
  have htrace : WordTrace (prefixWord ++ tailWord_4352409) baseStart_4352409 baseEnd_4352409 := by
    simpa [prefixWord, tailWord_4352409, baseEnd_4352409] using wordTrace_append hprefix tailTrace_4352409
  have hstable : (prefixWord ++ tailWord_4352409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4352409).length < 2 ^ (prefixWord ++ tailWord_4352409).sum := by decide
  have hdescent : baseEnd_4352409 < baseStart_4352409 := by decide
  rcases family_descends (prefixWord ++ tailWord_4352409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4352410 : List Nat := [3, 1, 1, 4, 1, 2, 4, 1, 2, 4]
def baseStart_4352410 : Nat := 118140960795 + 4352410 * 2 ^ 59
def prefixEnd_4352410 : Nat := 4983230072969 + 3 ^ 40 * 4352410 * 2
def baseEnd_4352410 : Nat := 744959445145140469852879

theorem tailTrace_4352410 : CollatzResearch.WordTrace tailWord_4352410 prefixEnd_4352410 744959445145140469852879 := by
  unfold tailWord_4352410
  simp only [CollatzResearch.WordTrace]
  refine ⟨39686358540492344323347671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105830289441312918195593789 39686358540492344323347671)
  ·
    refine ⟨59529537810738516485021507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39686358540492344323347671 59529537810738516485021507)
    ·
      refine ⟨89294306716107774727532261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59529537810738516485021507 89294306716107774727532261)
      ·
        refine ⟨16742682509270207761412299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 89294306716107774727532261 16742682509270207761412299)
        ·
          refine ⟨25114023763905311642118449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16742682509270207761412299 25114023763905311642118449)
          ·
            refine ⟨18835517822928983731588837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25114023763905311642118449 18835517822928983731588837)
            ·
              refine ⟨3531659591799184449672907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18835517822928983731588837 3531659591799184449672907)
              ·
                refine ⟨5297489387698776674509361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3531659591799184449672907 5297489387698776674509361)
                ·
                  refine ⟨3973117040774082505882021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5297489387698776674509361 3973117040774082505882021)
                  ·
                    refine ⟨744959445145140469852879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3973117040774082505882021 744959445145140469852879)
                    ·
                      rfl

theorem cell23_4352410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 4, 1, 2, 4].length) (baseStart_4352410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4352410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4352410 prefixEnd_4352410 := by exact prefixLift 4352410
  have htrace : WordTrace (prefixWord ++ tailWord_4352410) baseStart_4352410 baseEnd_4352410 := by
    simpa [prefixWord, tailWord_4352410, baseEnd_4352410] using wordTrace_append hprefix tailTrace_4352410
  have hstable : (prefixWord ++ tailWord_4352410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4352410).length < 2 ^ (prefixWord ++ tailWord_4352410).sum := by decide
  have hdescent : baseEnd_4352410 < baseStart_4352410 := by decide
  rcases family_descends (prefixWord ++ tailWord_4352410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4352417 : List Nat := [1, 2, 3, 5, 1, 2, 1, 2, 1, 1, 4]
def baseStart_4352417 : Nat := 118140960795 + 4352417 * 2 ^ 59
def prefixEnd_4352417 : Nat := 4983230072969 + 3 ^ 40 * 4352417 * 2
def baseEnd_4352417 : Nat := 2234881929800002882171105

theorem tailTrace_4352417 : CollatzResearch.WordTrace tailWord_4352417 prefixEnd_4352417 2234881929800002882171105 := by
  unfold tailWord_4352417
  simp only [CollatzResearch.WordTrace]
  refine ⟨158745689472944017488895505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105830459648629344992597003 158745689472944017488895505)
  ·
    refine ⟨119059267104708013116671629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 158745689472944017488895505 119059267104708013116671629)
    ·
      refine ⟨44647225164265504918751861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 119059267104708013116671629 44647225164265504918751861)
      ·
        refine ⟨4185677359149891086132987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 44647225164265504918751861 4185677359149891086132987)
        ·
          refine ⟨6278516038724836629199481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4185677359149891086132987 6278516038724836629199481)
          ·
            refine ⟨4708887029043627471899611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6278516038724836629199481 4708887029043627471899611)
            ·
              refine ⟨7063330543565441207849417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4708887029043627471899611 7063330543565441207849417)
              ·
                refine ⟨5297497907674080905887063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7063330543565441207849417 5297497907674080905887063)
                ·
                  refine ⟨7946246861511121358830595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5297497907674080905887063 7946246861511121358830595)
                  ·
                    refine ⟨11919370292266682038245893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7946246861511121358830595 11919370292266682038245893)
                    ·
                      refine ⟨2234881929800002882171105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11919370292266682038245893 2234881929800002882171105)
                      ·
                        rfl

theorem cell23_4352417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 2, 1, 2, 1, 1, 4].length) (baseStart_4352417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4352417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4352417 prefixEnd_4352417 := by exact prefixLift 4352417
  have htrace : WordTrace (prefixWord ++ tailWord_4352417) baseStart_4352417 baseEnd_4352417 := by
    simpa [prefixWord, tailWord_4352417, baseEnd_4352417] using wordTrace_append hprefix tailTrace_4352417
  have hstable : (prefixWord ++ tailWord_4352417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4352417).length < 2 ^ (prefixWord ++ tailWord_4352417).sum := by decide
  have hdescent : baseEnd_4352417 < baseStart_4352417 := by decide
  rcases family_descends (prefixWord ++ tailWord_4352417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4352433 : List Nat := [1, 2, 2, 4, 1, 3, 1, 2, 1, 3, 3]
def baseStart_4352433 : Nat := 118140960795 + 4352433 * 2 ^ 59
def prefixEnd_4352433 : Nat := 4983230072969 + 3 ^ 40 * 4352433 * 2
def baseEnd_4352433 : Nat := 2234890145490474819571031

theorem tailTrace_4352433 : CollatzResearch.WordTrace tailWord_4352433 prefixEnd_4352433 2234890145490474819571031 := by
  unfold tailWord_4352433
  simp only [CollatzResearch.WordTrace]
  refine ⟨158746273040886052221477953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105830848693924034814318635 158746273040886052221477953)
  ·
    refine ⟨119059704780664539166108465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 158746273040886052221477953 119059704780664539166108465)
    ·
      refine ⟨89294778585498404374581349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119059704780664539166108465 89294778585498404374581349)
      ·
        refine ⟨16742770984780950820234003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 89294778585498404374581349 16742770984780950820234003)
        ·
          refine ⟨25114156477171426230351005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16742770984780950820234003 25114156477171426230351005)
          ·
            refine ⟨9417808678939284836381627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25114156477171426230351005 9417808678939284836381627)
            ·
              refine ⟨14126713018408927254572441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9417808678939284836381627 14126713018408927254572441)
              ·
                refine ⟨10595034763806695440929331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14126713018408927254572441 10595034763806695440929331)
                ·
                  refine ⟨15892552145710043161393997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10595034763806695440929331 15892552145710043161393997)
                  ·
                    refine ⟨5959707054641266185522749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15892552145710043161393997 5959707054641266185522749)
                    ·
                      refine ⟨2234890145490474819571031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5959707054641266185522749 2234890145490474819571031)
                      ·
                        rfl

theorem cell23_4352433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 1, 2, 1, 3, 3].length) (baseStart_4352433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4352433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4352433 prefixEnd_4352433 := by exact prefixLift 4352433
  have htrace : WordTrace (prefixWord ++ tailWord_4352433) baseStart_4352433 baseEnd_4352433 := by
    simpa [prefixWord, tailWord_4352433, baseEnd_4352433] using wordTrace_append hprefix tailTrace_4352433
  have hstable : (prefixWord ++ tailWord_4352433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4352433).length < 2 ^ (prefixWord ++ tailWord_4352433).sum := by decide
  have hdescent : baseEnd_4352433 < baseStart_4352433 := by decide
  rcases family_descends (prefixWord ++ tailWord_4352433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4352437 : List Nat := [1, 3, 3, 2, 3, 1, 3, 1, 1, 2, 3]
def baseStart_4352437 : Nat := 118140960795 + 4352437 * 2 ^ 59
def prefixEnd_4352437 : Nat := 4983230072969 + 3 ^ 40 * 4352437 * 2
def baseEnd_4352437 : Nat := 2234892199413092803921013

theorem tailTrace_4352437 : CollatzResearch.WordTrace tailWord_4352437 prefixEnd_4352437 2234892199413092803921013 := by
  unfold tailWord_4352437
  simp only [CollatzResearch.WordTrace]
  refine ⟨158746418932871560904623565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105830945955247707269749043 158746418932871560904623565)
  ·
    refine ⟨59529907099826835339233837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 158746418932871560904623565 59529907099826835339233837)
    ·
      refine ⟨22323715162435063252212689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59529907099826835339233837 22323715162435063252212689)
      ·
        refine ⟨16742786371826297439159517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22323715162435063252212689 16742786371826297439159517)
        ·
          refine ⟨6278544889434861539684819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16742786371826297439159517 6278544889434861539684819)
          ·
            refine ⟨9417817334152292309527229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6278544889434861539684819 9417817334152292309527229)
            ·
              refine ⟨3531681500307109616072711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9417817334152292309527229 3531681500307109616072711)
              ·
                refine ⟨5297522250460664424109067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3531681500307109616072711 5297522250460664424109067)
                ·
                  refine ⟨7946283375690996636163601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5297522250460664424109067 7946283375690996636163601)
                  ·
                    refine ⟨5959712531768247477122701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7946283375690996636163601 5959712531768247477122701)
                    ·
                      refine ⟨2234892199413092803921013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5959712531768247477122701 2234892199413092803921013)
                      ·
                        rfl

theorem cell23_4352437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 3, 1, 1, 2, 3].length) (baseStart_4352437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4352437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4352437 prefixEnd_4352437 := by exact prefixLift 4352437
  have htrace : WordTrace (prefixWord ++ tailWord_4352437) baseStart_4352437 baseEnd_4352437 := by
    simpa [prefixWord, tailWord_4352437, baseEnd_4352437] using wordTrace_append hprefix tailTrace_4352437
  have hstable : (prefixWord ++ tailWord_4352437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4352437).length < 2 ^ (prefixWord ++ tailWord_4352437).sum := by decide
  have hdescent : baseEnd_4352437 < baseStart_4352437 := by decide
  rcases family_descends (prefixWord ++ tailWord_4352437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4352446 : List Nat := [4, 2, 1, 1, 1, 1, 2, 2, 2, 2, 5]
def baseStart_4352446 : Nat := 118140960795 + 4352446 * 2 ^ 59
def prefixEnd_4352446 : Nat := 4983230072969 + 3 ^ 40 * 4352446 * 2
def baseEnd_4352446 : Nat := 2234896820738983268708471

theorem tailTrace_4352446 : CollatzResearch.WordTrace tailWord_4352446 prefixEnd_4352446 2234896820738983268708471 := by
  unfold tailWord_4352446
  simp only [CollatzResearch.WordTrace]
  refine ⟨19843343398729869430212649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 105831164793225970294467461 19843343398729869430212649)
  ·
    refine ⟨14882507549047402072659487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19843343398729869430212649 14882507549047402072659487)
    ·
      refine ⟨22323761323571103108989231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14882507549047402072659487 22323761323571103108989231)
      ·
        refine ⟨33485641985356654663483847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22323761323571103108989231 33485641985356654663483847)
        ·
          refine ⟨50228462978034981995225771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33485641985356654663483847 50228462978034981995225771)
          ·
            refine ⟨75342694467052472992838657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50228462978034981995225771 75342694467052472992838657)
            ·
              refine ⟨56507020850289354744628993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75342694467052472992838657 56507020850289354744628993)
              ·
                refine ⟨42380265637717016058471745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56507020850289354744628993 42380265637717016058471745)
                ·
                  refine ⟨31785199228287762043853809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42380265637717016058471745 31785199228287762043853809)
                  ·
                    refine ⟨23838899421215821532890357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 31785199228287762043853809 23838899421215821532890357)
                    ·
                      refine ⟨2234896820738983268708471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23838899421215821532890357 2234896820738983268708471)
                      ·
                        rfl

theorem cell23_4352446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 2, 2, 2, 5].length) (baseStart_4352446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4352446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4352446 prefixEnd_4352446 := by exact prefixLift 4352446
  have htrace : WordTrace (prefixWord ++ tailWord_4352446) baseStart_4352446 baseEnd_4352446 := by
    simpa [prefixWord, tailWord_4352446, baseEnd_4352446] using wordTrace_append hprefix tailTrace_4352446
  have hstable : (prefixWord ++ tailWord_4352446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4352446).length < 2 ^ (prefixWord ++ tailWord_4352446).sum := by decide
  have hdescent : baseEnd_4352446 < baseStart_4352446 := by decide
  rcases family_descends (prefixWord ++ tailWord_4352446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4352456 : List Nat := [2, 1, 3, 1, 3, 2, 1, 1, 2, 3, 4]
def baseStart_4352456 : Nat := 118140960795 + 4352456 * 2 ^ 59
def prefixEnd_4352456 : Nat := 4983230072969 + 3 ^ 40 * 4352456 * 2
def baseEnd_4352456 : Nat := 2234901955545528229583425

theorem tailTrace_4352456 : CollatzResearch.WordTrace tailWord_4352456 prefixEnd_4352456 2234901955545528229583425 := by
  unfold tailWord_4352456
  simp only [CollatzResearch.WordTrace]
  refine ⟨79373555959901363574782611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105831407946535151433043481 79373555959901363574782611)
  ·
    refine ⟨119060333939852045362173917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79373555959901363574782611 119060333939852045362173917)
    ·
      refine ⟨44647625227444517010815219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 119060333939852045362173917 44647625227444517010815219)
      ·
        refine ⟨66971437841166775516222829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44647625227444517010815219 66971437841166775516222829)
        ·
          refine ⟨25114289190437540818583561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66971437841166775516222829 25114289190437540818583561)
          ·
            refine ⟨18835716892828155613937671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25114289190437540818583561 18835716892828155613937671)
            ·
              refine ⟨28253575339242233420906507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18835716892828155613937671 28253575339242233420906507)
              ·
                refine ⟨42380363008863350131359761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28253575339242233420906507 42380363008863350131359761)
                ·
                  refine ⟨31785272256647512598519821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42380363008863350131359761 31785272256647512598519821)
                  ·
                    refine ⟨11919477096242817224444933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 31785272256647512598519821 11919477096242817224444933)
                    ·
                      refine ⟨2234901955545528229583425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11919477096242817224444933 2234901955545528229583425)
                      ·
                        rfl

theorem cell23_4352456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 1, 2, 3, 4].length) (baseStart_4352456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4352456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4352456 prefixEnd_4352456 := by exact prefixLift 4352456
  have htrace : WordTrace (prefixWord ++ tailWord_4352456) baseStart_4352456 baseEnd_4352456 := by
    simpa [prefixWord, tailWord_4352456, baseEnd_4352456] using wordTrace_append hprefix tailTrace_4352456
  have hstable : (prefixWord ++ tailWord_4352456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4352456).length < 2 ^ (prefixWord ++ tailWord_4352456).sum := by decide
  have hdescent : baseEnd_4352456 < baseStart_4352456 := by decide
  rcases family_descends (prefixWord ++ tailWord_4352456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4352490 : List Nat := [3, 1, 3, 1, 3, 1, 2, 2, 1, 4, 2]
def baseStart_4352490 : Nat := 118140960795 + 4352490 * 2 ^ 59
def prefixEnd_4352490 : Nat := 4983230072969 + 3 ^ 40 * 4352490 * 2
def baseEnd_4352490 : Nat := 2234919413887781096558269

theorem tailTrace_4352490 : CollatzResearch.WordTrace tailWord_4352490 prefixEnd_4352490 2234919413887781096558269 := by
  unfold tailWord_4352490
  simp only [CollatzResearch.WordTrace]
  refine ⟨39687088000419887739075731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105832234667786367304201949 39687088000419887739075731)
  ·
    refine ⟨59530632000629831608613597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39687088000419887739075731 59530632000629831608613597)
    ·
      refine ⟨22323987000236186853230099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59530632000629831608613597 22323987000236186853230099)
      ·
        refine ⟨33485980500354280279845149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22323987000236186853230099 33485980500354280279845149)
        ·
          refine ⟨12557242687632855104941931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33485980500354280279845149 12557242687632855104941931)
          ·
            refine ⟨18835864031449282657412897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12557242687632855104941931 18835864031449282657412897)
            ·
              refine ⟨14126898023586961993059673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18835864031449282657412897 14126898023586961993059673)
              ·
                refine ⟨10595173517690221494794755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14126898023586961993059673 10595173517690221494794755)
                ·
                  refine ⟨15892760276535332242192133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10595173517690221494794755 15892760276535332242192133)
                  ·
                    refine ⟨2979892551850374795411025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15892760276535332242192133 2979892551850374795411025)
                    ·
                      refine ⟨2234919413887781096558269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2979892551850374795411025 2234919413887781096558269)
                      ·
                        rfl

theorem cell23_4352490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 2, 2, 1, 4, 2].length) (baseStart_4352490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4352490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4352490 prefixEnd_4352490 := by exact prefixLift 4352490
  have htrace : WordTrace (prefixWord ++ tailWord_4352490) baseStart_4352490 baseEnd_4352490 := by
    simpa [prefixWord, tailWord_4352490, baseEnd_4352490] using wordTrace_append hprefix tailTrace_4352490
  have hstable : (prefixWord ++ tailWord_4352490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4352490).length < 2 ^ (prefixWord ++ tailWord_4352490).sum := by decide
  have hdescent : baseEnd_4352490 < baseStart_4352490 := by decide
  rcases family_descends (prefixWord ++ tailWord_4352490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4352494 : List Nat := [4, 1, 2, 1, 2, 4, 2, 1, 1, 3, 2]
def baseStart_4352494 : Nat := 118140960795 + 4352494 * 2 ^ 59
def prefixEnd_4352494 : Nat := 4983230072969 + 3 ^ 40 * 4352494 * 2
def baseEnd_4352494 : Nat := 2234921467810399080908251

theorem tailTrace_4352494 : CollatzResearch.WordTrace tailWord_4352494 prefixEnd_4352494 2234921467810399080908251 := by
  unfold tailWord_4352494
  simp only [CollatzResearch.WordTrace]
  refine ⟨19843562236708132454931067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 105832331929110039759632357 19843562236708132454931067)
  ·
    refine ⟨29765343355062198682396601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19843562236708132454931067 29765343355062198682396601)
    ·
      refine ⟨22324007516296649011797451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29765343355062198682396601 22324007516296649011797451)
      ·
        refine ⟨33486011274444973517696177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22324007516296649011797451 33486011274444973517696177)
        ·
          refine ⟨25114508455833730138272133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33486011274444973517696177 25114508455833730138272133)
          ·
            refine ⟨4708970335468824400926025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25114508455833730138272133 4708970335468824400926025)
            ·
              refine ⟨3531727751601618300694519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4708970335468824400926025 3531727751601618300694519)
              ·
                refine ⟨5297591627402427451041779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3531727751601618300694519 5297591627402427451041779)
                ·
                  refine ⟨7946387441103641176562669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5297591627402427451041779 7946387441103641176562669)
                  ·
                    refine ⟨2979895290413865441211001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7946387441103641176562669 2979895290413865441211001)
                    ·
                      refine ⟨2234921467810399080908251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2979895290413865441211001 2234921467810399080908251)
                      ·
                        rfl

theorem cell23_4352494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 4, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 4, 2, 1, 1, 3, 2].length) (baseStart_4352494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4352494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4352494 prefixEnd_4352494 := by exact prefixLift 4352494
  have htrace : WordTrace (prefixWord ++ tailWord_4352494) baseStart_4352494 baseEnd_4352494 := by
    simpa [prefixWord, tailWord_4352494, baseEnd_4352494] using wordTrace_append hprefix tailTrace_4352494
  have hstable : (prefixWord ++ tailWord_4352494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4352494).length < 2 ^ (prefixWord ++ tailWord_4352494).sum := by decide
  have hdescent : baseEnd_4352494 < baseStart_4352494 := by decide
  rcases family_descends (prefixWord ++ tailWord_4352494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4352501 : List Nat := [1, 3, 5, 1, 3, 1, 1, 2, 2, 1, 3]
def baseStart_4352501 : Nat := 118140960795 + 4352501 * 2 ^ 59
def prefixEnd_4352501 : Nat := 4983230072969 + 3 ^ 40 * 4352501 * 2
def baseEnd_4352501 : Nat := 2234925062174980553520719

theorem tailTrace_4352501 : CollatzResearch.WordTrace tailWord_4352501 prefixEnd_4352501 2234925062174980553520719 := by
  unfold tailWord_4352501
  simp only [CollatzResearch.WordTrace]
  refine ⟨158748753204639699834953357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105832502136426466556635571 158748753204639699834953357)
  ·
    refine ⟨59530782451739887438107509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 158748753204639699834953357 59530782451739887438107509)
    ·
      refine ⟨5581010854850614447322579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 59530782451739887438107509 5581010854850614447322579)
      ·
        refine ⟨8371516282275921670983869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5581010854850614447322579 8371516282275921670983869)
        ·
          refine ⟨3139318605853470626618951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8371516282275921670983869 3139318605853470626618951)
          ·
            refine ⟨4708977908780205939928427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3139318605853470626618951 4708977908780205939928427)
            ·
              refine ⟨7063466863170308909892641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4708977908780205939928427 7063466863170308909892641)
              ·
                refine ⟨5297600147377731682419481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7063466863170308909892641 5297600147377731682419481)
                ·
                  refine ⟨3973200110533298761814611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5297600147377731682419481 3973200110533298761814611)
                  ·
                    refine ⟨5959800165799948142721917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3973200110533298761814611 5959800165799948142721917)
                    ·
                      refine ⟨2234925062174980553520719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5959800165799948142721917 2234925062174980553520719)
                      ·
                        rfl

theorem cell23_4352501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 1, 1, 2, 2, 1, 3].length) (baseStart_4352501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4352501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4352501 prefixEnd_4352501 := by exact prefixLift 4352501
  have htrace : WordTrace (prefixWord ++ tailWord_4352501) baseStart_4352501 baseEnd_4352501 := by
    simpa [prefixWord, tailWord_4352501, baseEnd_4352501] using wordTrace_append hprefix tailTrace_4352501
  have hstable : (prefixWord ++ tailWord_4352501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4352501).length < 2 ^ (prefixWord ++ tailWord_4352501).sum := by decide
  have hdescent : baseEnd_4352501 < baseStart_4352501 := by decide
  rcases family_descends (prefixWord ++ tailWord_4352501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4352513 : List Nat := [1, 2, 4, 1, 3, 2, 2, 1, 7]
def baseStart_4352513 : Nat := 118140960795 + 4352513 * 2 ^ 59
def prefixEnd_4352513 : Nat := 4983230072969 + 3 ^ 40 * 4352513 * 2
def baseEnd_4352513 : Nat := 248325691549203834063407

theorem tailTrace_4352513 : CollatzResearch.WordTrace tailWord_4352513 prefixEnd_4352513 248325691549203834063407 := by
  unfold tailWord_4352513
  simp only [CollatzResearch.WordTrace]
  refine ⟨158749190880596225884390193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105832793920397483922926795 158749190880596225884390193)
  ·
    refine ⟨119061893160447169413292645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 158749190880596225884390193 119061893160447169413292645)
    ·
      refine ⟨22324104967583844264992371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 119061893160447169413292645 22324104967583844264992371)
      ·
        refine ⟨33486157451375766397488557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22324104967583844264992371 33486157451375766397488557)
        ·
          refine ⟨12557309044265912399058209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33486157451375766397488557 12557309044265912399058209)
          ·
            refine ⟨9417981783199434299293657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12557309044265912399058209 9417981783199434299293657)
            ·
              refine ⟨7063486337399575724470243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9417981783199434299293657 7063486337399575724470243)
              ·
                refine ⟨10595229506099363586705365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7063486337399575724470243 10595229506099363586705365)
                ·
                  refine ⟨248325691549203834063407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10595229506099363586705365 248325691549203834063407)
                  ·
                    rfl

theorem cell23_4352513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 2, 1, 7].length) (baseStart_4352513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4352513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4352513 prefixEnd_4352513 := by exact prefixLift 4352513
  have htrace : WordTrace (prefixWord ++ tailWord_4352513) baseStart_4352513 baseEnd_4352513 := by
    simpa [prefixWord, tailWord_4352513, baseEnd_4352513] using wordTrace_append hprefix tailTrace_4352513
  have hstable : (prefixWord ++ tailWord_4352513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4352513).length < 2 ^ (prefixWord ++ tailWord_4352513).sum := by decide
  have hdescent : baseEnd_4352513 < baseStart_4352513 := by decide
  rcases family_descends (prefixWord ++ tailWord_4352513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4352518 : List Nat := [6, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3]
def baseStart_4352518 : Nat := 118140960795 + 4352518 * 2 ^ 59
def prefixEnd_4352518 : Nat := 4983230072969 + 3 ^ 40 * 4352518 * 2
def baseEnd_4352518 : Nat := 2234933791346106987008141

theorem tailTrace_4352518 : CollatzResearch.WordTrace tailWord_4352518 prefixEnd_4352518 2234933791346106987008141 := by
  unfold tailWord_4352518
  simp only [CollatzResearch.WordTrace]
  refine ⟨4960917913924315991822569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 105832915497052074492214805 4960917913924315991822569)
  ·
    refine ⟨3720688435443236993866927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4960917913924315991822569 3720688435443236993866927)
    ·
      refine ⟨5581032653164855490800391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3720688435443236993866927 5581032653164855490800391)
      ·
        refine ⟨8371548979747283236200587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5581032653164855490800391 8371548979747283236200587)
        ·
          refine ⟨12557323469620924854300881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8371548979747283236200587 12557323469620924854300881)
          ·
            refine ⟨9417992602215693640725661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12557323469620924854300881 9417992602215693640725661)
            ·
              refine ⟨3531747225830885115272123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9417992602215693640725661 3531747225830885115272123)
              ·
                refine ⟨5297620838746327672908185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3531747225830885115272123 5297620838746327672908185)
                ·
                  refine ⟨3973215629059745754681139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5297620838746327672908185 3973215629059745754681139)
                  ·
                    refine ⟨5959823443589618632021709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3973215629059745754681139 5959823443589618632021709)
                    ·
                      refine ⟨2234933791346106987008141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5959823443589618632021709 2234933791346106987008141)
                      ·
                        rfl

theorem cell23_4352518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3].length) (baseStart_4352518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4352518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4352518 prefixEnd_4352518 := by exact prefixLift 4352518
  have htrace : WordTrace (prefixWord ++ tailWord_4352518) baseStart_4352518 baseEnd_4352518 := by
    simpa [prefixWord, tailWord_4352518, baseEnd_4352518] using wordTrace_append hprefix tailTrace_4352518
  have hstable : (prefixWord ++ tailWord_4352518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4352518).length < 2 ^ (prefixWord ++ tailWord_4352518).sum := by decide
  have hdescent : baseEnd_4352518 < baseStart_4352518 := by decide
  rcases family_descends (prefixWord ++ tailWord_4352518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4352523 : List Nat := [1, 1, 1, 1, 7, 1, 2, 1, 2, 3, 3]
def baseStart_4352523 : Nat := 118140960795 + 4352523 * 2 ^ 59
def prefixEnd_4352523 : Nat := 4983230072969 + 3 ^ 40 * 4352523 * 2
def baseEnd_4352523 : Nat := 2234936358749379467445617

theorem tailTrace_4352523 : CollatzResearch.WordTrace tailWord_4352523 prefixEnd_4352523 2234936358749379467445617 := by
  unfold tailWord_4352523
  simp only [CollatzResearch.WordTrace]
  refine ⟨158749555610559997592254223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105833037073706665061502815 158749555610559997592254223)
  ·
    refine ⟨238124333415839996388381335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158749555610559997592254223 238124333415839996388381335)
    ·
      refine ⟨357186500123759994582572003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 238124333415839996388381335 357186500123759994582572003)
      ·
        refine ⟨535779750185639991873858005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 357186500123759994582572003 535779750185639991873858005)
        ·
          refine ⟨12557337894975937309543547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 535779750185639991873858005 12557337894975937309543547)
          ·
            refine ⟨18836006842463905964315321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12557337894975937309543547 18836006842463905964315321)
            ·
              refine ⟨14127005131847929473236491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18836006842463905964315321 14127005131847929473236491)
              ·
                refine ⟨21190507697771894209854737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14127005131847929473236491 21190507697771894209854737)
                ·
                  refine ⟨15892880773328920657391053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21190507697771894209854737 15892880773328920657391053)
                  ·
                    refine ⟨5959830289998345246521645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15892880773328920657391053 5959830289998345246521645)
                    ·
                      refine ⟨2234936358749379467445617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5959830289998345246521645 2234936358749379467445617)
                      ·
                        rfl

theorem cell23_4352523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 2, 1, 2, 3, 3].length) (baseStart_4352523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4352523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4352523 prefixEnd_4352523 := by exact prefixLift 4352523
  have htrace : WordTrace (prefixWord ++ tailWord_4352523) baseStart_4352523 baseEnd_4352523 := by
    simpa [prefixWord, tailWord_4352523, baseEnd_4352523] using wordTrace_append hprefix tailTrace_4352523
  have hstable : (prefixWord ++ tailWord_4352523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4352523).length < 2 ^ (prefixWord ++ tailWord_4352523).sum := by decide
  have hdescent : baseEnd_4352523 < baseStart_4352523 := by decide
  rcases family_descends (prefixWord ++ tailWord_4352523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4352524 : List Nat := [2, 2, 1, 2, 4, 2, 3, 1, 2, 2, 2]
def baseStart_4352524 : Nat := 118140960795 + 4352524 * 2 ^ 59
def prefixEnd_4352524 : Nat := 4983230072969 + 3 ^ 40 * 4352524 * 2
def baseEnd_4352524 : Nat := 2234936872230033963533113

theorem tailTrace_4352524 : CollatzResearch.WordTrace tailWord_4352524 prefixEnd_4352524 2234936872230033963533113 := by
  unfold tailWord_4352524
  simp only [CollatzResearch.WordTrace]
  refine ⟨79374796041778187381520313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105833061389037583175360417 79374796041778187381520313)
  ·
    refine ⟨59531097031333640536140235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79374796041778187381520313 59531097031333640536140235)
    ·
      refine ⟨89296645547000460804210353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59531097031333640536140235 89296645547000460804210353)
      ·
        refine ⟨66972484160250345603157765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89296645547000460804210353 66972484160250345603157765)
        ·
          refine ⟨12557340780046939800592081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 66972484160250345603157765 12557340780046939800592081)
          ·
            refine ⟨9418005585035204850444061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12557340780046939800592081 9418005585035204850444061)
            ·
              refine ⟨3531752094388201818916523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9418005585035204850444061 3531752094388201818916523)
              ·
                refine ⟨5297628141582302728374785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3531752094388201818916523 5297628141582302728374785)
                ·
                  refine ⟨3973221106186727046281089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5297628141582302728374785 3973221106186727046281089)
                  ·
                    refine ⟨2979915829640045284710817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3973221106186727046281089 2979915829640045284710817)
                    ·
                      refine ⟨2234936872230033963533113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2979915829640045284710817 2234936872230033963533113)
                      ·
                        rfl

theorem cell23_4352524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 3, 1, 2, 2, 2].length) (baseStart_4352524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4352524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4352524 prefixEnd_4352524 := by exact prefixLift 4352524
  have htrace : WordTrace (prefixWord ++ tailWord_4352524) baseStart_4352524 baseEnd_4352524 := by
    simpa [prefixWord, tailWord_4352524, baseEnd_4352524] using wordTrace_append hprefix tailTrace_4352524
  have hstable : (prefixWord ++ tailWord_4352524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4352524).length < 2 ^ (prefixWord ++ tailWord_4352524).sum := by decide
  have hdescent : baseEnd_4352524 < baseStart_4352524 := by decide
  rcases family_descends (prefixWord ++ tailWord_4352524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4352563 : List Nat := [1, 1, 1, 2, 4, 2, 3, 2, 2, 1, 4]
def baseStart_4352563 : Nat := 118140960795 + 4352563 * 2 ^ 59
def prefixEnd_4352563 : Nat := 4983230072969 + 3 ^ 40 * 4352563 * 2
def baseEnd_4352563 : Nat := 2234956897975559310945433

theorem tailTrace_4352563 : CollatzResearch.WordTrace tailWord_4352563 prefixEnd_4352563 2234956897975559310945433 := by
  unfold tailWord_4352563
  simp only [CollatzResearch.WordTrace]
  refine ⟨158751014530415084423710343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105834009686943389615806895 158751014530415084423710343)
  ·
    refine ⟨238126521795622626635565515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158751014530415084423710343 238126521795622626635565515)
    ·
      refine ⟨357189782693433939953348273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 238126521795622626635565515 357189782693433939953348273)
      ·
        refine ⟨267892337020075454965011205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 357189782693433939953348273 267892337020075454965011205)
        ·
          refine ⟨50229813191264147805939601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 267892337020075454965011205 50229813191264147805939601)
          ·
            refine ⟨37672359893448110854454701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50229813191264147805939601 37672359893448110854454701)
            ·
              refine ⟨14127134960043041570420513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37672359893448110854454701 14127134960043041570420513)
              ·
                refine ⟨10595351220032281177815385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14127134960043041570420513 10595351220032281177815385)
                ·
                  refine ⟨7946513415024210883361539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10595351220032281177815385 7946513415024210883361539)
                  ·
                    refine ⟨11919770122536316325042309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7946513415024210883361539 11919770122536316325042309)
                    ·
                      refine ⟨2234956897975559310945433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11919770122536316325042309 2234956897975559310945433)
                      ·
                        rfl

theorem cell23_4352563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 3, 2, 2, 1, 4].length) (baseStart_4352563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4352563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4352563 prefixEnd_4352563 := by exact prefixLift 4352563
  have htrace : WordTrace (prefixWord ++ tailWord_4352563) baseStart_4352563 baseEnd_4352563 := by
    simpa [prefixWord, tailWord_4352563, baseEnd_4352563] using wordTrace_append hprefix tailTrace_4352563
  have hstable : (prefixWord ++ tailWord_4352563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4352563).length < 2 ^ (prefixWord ++ tailWord_4352563).sum := by decide
  have hdescent : baseEnd_4352563 < baseStart_4352563 := by decide
  rcases family_descends (prefixWord ++ tailWord_4352563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4352564 : List Nat := [2, 5, 1, 3, 2, 1, 1, 1, 7]
def baseStart_4352564 : Nat := 118140960795 + 4352564 * 2 ^ 59
def prefixEnd_4352564 : Nat := 4983230072969 + 3 ^ 40 * 4352564 * 2
def baseEnd_4352564 : Nat := 248328601272912645225881

theorem tailTrace_4352564 : CollatzResearch.WordTrace tailWord_4352564 prefixEnd_4352564 248328601272912645225881 := by
  unfold tailWord_4352564
  simp only [CollatzResearch.WordTrace]
  refine ⟨79375525501705730797248373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105834034002274307729664497 79375525501705730797248373)
  ·
    refine ⟨7441455515784912262242035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 79375525501705730797248373 7441455515784912262242035)
    ·
      refine ⟨11162183273677368393363053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7441455515784912262242035 11162183273677368393363053)
      ·
        refine ⟨4185818727629013147511145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11162183273677368393363053 4185818727629013147511145)
        ·
          refine ⟨3139364045721759860633359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4185818727629013147511145 3139364045721759860633359)
          ·
            refine ⟨4709046068582639790950039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3139364045721759860633359 4709046068582639790950039)
            ·
              refine ⟨7063569102873959686425059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4709046068582639790950039 7063569102873959686425059)
              ·
                refine ⟨10595353654310939529637589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7063569102873959686425059 10595353654310939529637589)
                ·
                  refine ⟨248328601272912645225881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10595353654310939529637589 248328601272912645225881)
                  ·
                    rfl

theorem cell23_4352564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 1, 1, 1, 7].length) (baseStart_4352564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4352564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4352564 prefixEnd_4352564 := by exact prefixLift 4352564
  have htrace : WordTrace (prefixWord ++ tailWord_4352564) baseStart_4352564 baseEnd_4352564 := by
    simpa [prefixWord, tailWord_4352564, baseEnd_4352564] using wordTrace_append hprefix tailTrace_4352564
  have hstable : (prefixWord ++ tailWord_4352564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4352564).length < 2 ^ (prefixWord ++ tailWord_4352564).sum := by decide
  have hdescent : baseEnd_4352564 < baseStart_4352564 := by decide
  rcases family_descends (prefixWord ++ tailWord_4352564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4352576 : List Nat := [2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 6]
def baseStart_4352576 : Nat := 118140960795 + 4352576 * 2 ^ 59
def prefixEnd_4352576 : Nat := 4983230072969 + 3 ^ 40 * 4352576 * 2
def baseEnd_4352576 : Nat := 2234963573224067760082873

theorem tailTrace_4352576 : CollatzResearch.WordTrace tailWord_4352576 prefixEnd_4352576 2234963573224067760082873 := by
  unfold tailWord_4352576
  simp only [CollatzResearch.WordTrace]
  refine ⟨79375744339683993821966791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105834325786245325095955721 79375744339683993821966791)
  ·
    refine ⟨119063616509525990732950187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79375744339683993821966791 119063616509525990732950187)
    ·
      refine ⟨178595424764288986099425281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119063616509525990732950187 178595424764288986099425281)
      ·
        refine ⟨133946568573216739574568961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 178595424764288986099425281 133946568573216739574568961)
        ·
          refine ⟨100459926429912554680926721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 133946568573216739574568961 100459926429912554680926721)
          ·
            refine ⟨75344944822434416010695041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 100459926429912554680926721 75344944822434416010695041)
            ·
              refine ⟨56508708616825812008021281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75344944822434416010695041 56508708616825812008021281)
              ·
                refine ⟨42381531462619359006015961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56508708616825812008021281 42381531462619359006015961)
                ·
                  refine ⟨31786148596964519254511971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42381531462619359006015961 31786148596964519254511971)
                  ·
                    refine ⟨47679222895446778881767957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 31786148596964519254511971 47679222895446778881767957)
                    ·
                      refine ⟨2234963573224067760082873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 47679222895446778881767957 2234963573224067760082873)
                      ·
                        rfl

theorem cell23_4352576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 6].length) (baseStart_4352576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4352576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4352576 prefixEnd_4352576 := by exact prefixLift 4352576
  have htrace : WordTrace (prefixWord ++ tailWord_4352576) baseStart_4352576 baseEnd_4352576 := by
    simpa [prefixWord, tailWord_4352576, baseEnd_4352576] using wordTrace_append hprefix tailTrace_4352576
  have hstable : (prefixWord ++ tailWord_4352576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4352576).length < 2 ^ (prefixWord ++ tailWord_4352576).sum := by decide
  have hdescent : baseEnd_4352576 < baseStart_4352576 := by decide
  rcases family_descends (prefixWord ++ tailWord_4352576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4352633 : List Nat := [1, 2, 1, 3, 3, 2, 1, 2, 3, 5]
def baseStart_4352633 : Nat := 118140960795 + 4352633 * 2 ^ 59
def prefixEnd_4352633 : Nat := 4983230072969 + 3 ^ 40 * 4352633 * 2
def baseEnd_4352633 : Nat := 744997613873791345690037

theorem tailTrace_4352633 : CollatzResearch.WordTrace tailWord_4352633 prefixEnd_4352633 744997613873791345690037 := by
  unfold tailWord_4352633
  simp only [CollatzResearch.WordTrace]
  refine ⟨158753567640161486378758553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105835711760107657585839035 158753567640161486378758553)
  ·
    refine ⟨119065175730121114784068915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 158753567640161486378758553 119065175730121114784068915)
    ·
      refine ⟨178597763595181672176103373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119065175730121114784068915 178597763595181672176103373)
      ·
        refine ⟨66974161348193127066038765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 178597763595181672176103373 66974161348193127066038765)
        ·
          refine ⟨25115310505572422649764537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66974161348193127066038765 25115310505572422649764537)
          ·
            refine ⟨18836482879179316987323403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25115310505572422649764537 18836482879179316987323403)
            ·
              refine ⟨28254724318768975480985105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18836482879179316987323403 28254724318768975480985105)
              ·
                refine ⟨21191043239076731610738829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28254724318768975480985105 21191043239076731610738829)
                ·
                  refine ⟨7946641214653774354027061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21191043239076731610738829 7946641214653774354027061)
                  ·
                    refine ⟨744997613873791345690037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7946641214653774354027061 744997613873791345690037)
                    ·
                      rfl

theorem cell23_4352633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 2, 3, 5].length) (baseStart_4352633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4352633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4352633 prefixEnd_4352633 := by exact prefixLift 4352633
  have htrace : WordTrace (prefixWord ++ tailWord_4352633) baseStart_4352633 baseEnd_4352633 := by
    simpa [prefixWord, tailWord_4352633, baseEnd_4352633] using wordTrace_append hprefix tailTrace_4352633
  have hstable : (prefixWord ++ tailWord_4352633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4352633).length < 2 ^ (prefixWord ++ tailWord_4352633).sum := by decide
  have hdescent : baseEnd_4352633 < baseStart_4352633 := by decide
  rcases family_descends (prefixWord ++ tailWord_4352633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4352663 : List Nat := [1, 1, 3, 3, 2, 1, 1, 4, 1, 6]
def baseStart_4352663 : Nat := 118140960795 + 4352663 * 2 ^ 59
def prefixEnd_4352663 : Nat := 4983230072969 + 3 ^ 40 * 4352663 * 2
def baseEnd_4352663 : Nat := 745002748680336306564991

theorem tailTrace_4352663 : CollatzResearch.WordTrace tailWord_4352663 prefixEnd_4352663 745002748680336306564991 := by
  unfold tailWord_4352663
  simp only [CollatzResearch.WordTrace]
  refine ⟨158754661830052801502350643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105836441220035201001567095 158754661830052801502350643)
  ·
    refine ⟨238131992745079202253525965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158754661830052801502350643 238131992745079202253525965)
    ·
      refine ⟨89299497279404700845072237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 238131992745079202253525965 89299497279404700845072237)
      ·
        refine ⟨33487311479776762816902089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 89299497279404700845072237 33487311479776762816902089)
        ·
          refine ⟨25115483609832572112676567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33487311479776762816902089 25115483609832572112676567)
          ·
            refine ⟨37673225414748858169014851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25115483609832572112676567 37673225414748858169014851)
            ·
              refine ⟨56509838122123287253522277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37673225414748858169014851 56509838122123287253522277)
              ·
                refine ⟨10595594647898116360035427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 56509838122123287253522277 10595594647898116360035427)
                ·
                  refine ⟨15893391971847174540053141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10595594647898116360035427 15893391971847174540053141)
                  ·
                    refine ⟨745002748680336306564991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15893391971847174540053141 745002748680336306564991)
                    ·
                      rfl

theorem cell23_4352663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 4, 1, 6].length) (baseStart_4352663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4352663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4352663 prefixEnd_4352663 := by exact prefixLift 4352663
  have htrace : WordTrace (prefixWord ++ tailWord_4352663) baseStart_4352663 baseEnd_4352663 := by
    simpa [prefixWord, tailWord_4352663, baseEnd_4352663] using wordTrace_append hprefix tailTrace_4352663
  have hstable : (prefixWord ++ tailWord_4352663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4352663).length < 2 ^ (prefixWord ++ tailWord_4352663).sum := by decide
  have hdescent : baseEnd_4352663 < baseStart_4352663 := by decide
  rcases family_descends (prefixWord ++ tailWord_4352663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4352664 : List Nat := [2, 1, 2, 4, 1, 1, 4, 3, 1, 1, 3]
def baseStart_4352664 : Nat := 118140960795 + 4352664 * 2 ^ 59
def prefixEnd_4352664 : Nat := 4983230072969 + 3 ^ 40 * 4352664 * 2
def baseEnd_4352664 : Nat := 2235008759521663415782469

theorem tailTrace_4352664 : CollatzResearch.WordTrace tailWord_4352664 prefixEnd_4352664 2235008759521663415782469 := by
  unfold tailWord_4352664
  simp only [CollatzResearch.WordTrace]
  refine ⟨79377349151524589336568523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105836465535366119115424697 79377349151524589336568523)
  ·
    refine ⟨119066023727286884004852785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79377349151524589336568523 119066023727286884004852785)
    ·
      refine ⟨89299517795465163003639589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119066023727286884004852785 89299517795465163003639589)
      ·
        refine ⟨16743659586649718063182423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 89299517795465163003639589 16743659586649718063182423)
        ·
          refine ⟨25115489379974577094773635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16743659586649718063182423 25115489379974577094773635)
          ·
            refine ⟨37673234069961865642160453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25115489379974577094773635 37673234069961865642160453)
            ·
              refine ⟨7063731388117849807905085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37673234069961865642160453 7063731388117849807905085)
              ·
                refine ⟨2648899270544193677964407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7063731388117849807905085 2648899270544193677964407)
                ·
                  refine ⟨3973348905816290516946611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2648899270544193677964407 3973348905816290516946611)
                  ·
                    refine ⟨5960023358724435775419917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3973348905816290516946611 5960023358724435775419917)
                    ·
                      refine ⟨2235008759521663415782469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5960023358724435775419917 2235008759521663415782469)
                      ·
                        rfl

theorem cell23_4352664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 4, 3, 1, 1, 3].length) (baseStart_4352664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4352664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4352664 prefixEnd_4352664 := by exact prefixLift 4352664
  have htrace : WordTrace (prefixWord ++ tailWord_4352664) baseStart_4352664 baseEnd_4352664 := by
    simpa [prefixWord, tailWord_4352664, baseEnd_4352664] using wordTrace_append hprefix tailTrace_4352664
  have hstable : (prefixWord ++ tailWord_4352664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4352664).length < 2 ^ (prefixWord ++ tailWord_4352664).sum := by decide
  have hdescent : baseEnd_4352664 < baseStart_4352664 := by decide
  rcases family_descends (prefixWord ++ tailWord_4352664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4352687 : List Nat := [1, 1, 2, 1, 2, 5, 1, 3, 3, 2, 2]
def baseStart_4352687 : Nat := 118140960795 + 4352687 * 2 ^ 59
def prefixEnd_4352687 : Nat := 4983230072969 + 3 ^ 40 * 4352687 * 2
def baseEnd_4352687 : Nat := 2235020569576716825794863

theorem tailTrace_4352687 : CollatzResearch.WordTrace tailWord_4352687 prefixEnd_4352687 2235020569576716825794863 := by
  unfold tailWord_4352687
  simp only [CollatzResearch.WordTrace]
  refine ⟨158755537181965853601224315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105837024787977235734149543 158755537181965853601224315)
  ·
    refine ⟨238133305772948780401836473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158755537181965853601224315 238133305772948780401836473)
    ·
      refine ⟨178599979329711585301377355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 238133305772948780401836473 178599979329711585301377355)
      ·
        refine ⟨267899968994567377952066033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 178599979329711585301377355 267899968994567377952066033)
        ·
          refine ⟨200924976745925533464049525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 267899968994567377952066033 200924976745925533464049525)
          ·
            refine ⟨18836716569930518762254643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 200924976745925533464049525 18836716569930518762254643)
            ·
              refine ⟨28255074854895778143381965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18836716569930518762254643 28255074854895778143381965)
              ·
                refine ⟨10595653070585916803768237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28255074854895778143381965 10595653070585916803768237)
                ·
                  refine ⟨3973369901469718801413089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10595653070585916803768237 3973369901469718801413089)
                  ·
                    refine ⟨2980027426102289101059817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3973369901469718801413089 2980027426102289101059817)
                    ·
                      refine ⟨2235020569576716825794863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2980027426102289101059817 2235020569576716825794863)
                      ·
                        rfl

theorem cell23_4352687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 3, 3, 2, 2].length) (baseStart_4352687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4352687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4352687 prefixEnd_4352687 := by exact prefixLift 4352687
  have htrace : WordTrace (prefixWord ++ tailWord_4352687) baseStart_4352687 baseEnd_4352687 := by
    simpa [prefixWord, tailWord_4352687, baseEnd_4352687] using wordTrace_append hprefix tailTrace_4352687
  have hstable : (prefixWord ++ tailWord_4352687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4352687).length < 2 ^ (prefixWord ++ tailWord_4352687).sum := by decide
  have hdescent : baseEnd_4352687 < baseStart_4352687 := by decide
  rcases family_descends (prefixWord ++ tailWord_4352687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4352737 : List Nat := [1, 2, 3, 1, 4, 1, 2, 1, 4, 1, 3]
def baseStart_4352737 : Nat := 118140960795 + 4352737 * 2 ^ 59
def prefixEnd_4352737 : Nat := 4983230072969 + 3 ^ 40 * 4352737 * 2
def baseEnd_4352737 : Nat := 2235046243609441630169633

theorem tailTrace_4352737 : CollatzResearch.WordTrace tailWord_4352737 prefixEnd_4352737 2235046243609441630169633 := by
  unfold tailWord_4352737
  simp only [CollatzResearch.WordTrace]
  refine ⟨158757360831784712140544465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105838240554523141427029643 158757360831784712140544465)
  ·
    refine ⟨119068020623838534105408349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 158757360831784712140544465 119068020623838534105408349)
    ·
      refine ⟨44650507733939450289528131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 119068020623838534105408349 44650507733939450289528131)
      ·
        refine ⟨66975761600909175434292197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44650507733939450289528131 66975761600909175434292197)
        ·
          refine ⟨12557955300170470393929787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 66975761600909175434292197 12557955300170470393929787)
          ·
            refine ⟨18836932950255705590894681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12557955300170470393929787 18836932950255705590894681)
            ·
              refine ⟨14127699712691779193171011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18836932950255705590894681 14127699712691779193171011)
              ·
                refine ⟨21191549569037668789756517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14127699712691779193171011 21191549569037668789756517)
                ·
                  refine ⟨3973415544194562898079347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21191549569037668789756517 3973415544194562898079347)
                  ·
                    refine ⟨5960123316291844347119021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3973415544194562898079347 5960123316291844347119021)
                    ·
                      refine ⟨2235046243609441630169633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5960123316291844347119021 2235046243609441630169633)
                      ·
                        rfl

theorem cell23_4352737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 2, 1, 4, 1, 3].length) (baseStart_4352737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4352737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4352737 prefixEnd_4352737 := by exact prefixLift 4352737
  have htrace : WordTrace (prefixWord ++ tailWord_4352737) baseStart_4352737 baseEnd_4352737 := by
    simpa [prefixWord, tailWord_4352737, baseEnd_4352737] using wordTrace_append hprefix tailTrace_4352737
  have hstable : (prefixWord ++ tailWord_4352737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4352737).length < 2 ^ (prefixWord ++ tailWord_4352737).sum := by decide
  have hdescent : baseEnd_4352737 < baseStart_4352737 := by decide
  rcases family_descends (prefixWord ++ tailWord_4352737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4352753 : List Nat := [1, 2, 2, 2, 2, 2, 2, 1, 1, 8]
def baseStart_4352753 : Nat := 118140960795 + 4352753 * 2 ^ 59
def prefixEnd_4352753 : Nat := 4983230072969 + 3 ^ 40 * 4352753 * 2
def baseEnd_4352753 : Nat := 745018153099971189189853

theorem tailTrace_4352753 : CollatzResearch.WordTrace tailWord_4352753 prefixEnd_4352753 745018153099971189189853 := by
  unfold tailWord_4352753
  simp only [CollatzResearch.WordTrace]
  refine ⟨158757944399726746873126913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105838629599817831248751275 158757944399726746873126913)
  ·
    refine ⟨119068458299795060154845185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 158757944399726746873126913 119068458299795060154845185)
    ·
      refine ⟨89301343724846295116133889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119068458299795060154845185 89301343724846295116133889)
      ·
        refine ⟨66976007793634721337100417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89301343724846295116133889 66976007793634721337100417)
        ·
          refine ⟨50232005845226041002825313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66976007793634721337100417 50232005845226041002825313)
          ·
            refine ⟨37674004383919530752118985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50232005845226041002825313 37674004383919530752118985)
            ·
              refine ⟨28255503287939648064089239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37674004383919530752118985 28255503287939648064089239)
              ·
                refine ⟨42383254931909472096133859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28255503287939648064089239 42383254931909472096133859)
                ·
                  refine ⟨63574882397864208144200789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42383254931909472096133859 63574882397864208144200789)
                  ·
                    refine ⟨745018153099971189189853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 63574882397864208144200789 745018153099971189189853)
                    ·
                      rfl

theorem cell23_4352753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 1, 1, 8].length) (baseStart_4352753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4352753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4352753 prefixEnd_4352753 := by exact prefixLift 4352753
  have htrace : WordTrace (prefixWord ++ tailWord_4352753) baseStart_4352753 baseEnd_4352753 := by
    simpa [prefixWord, tailWord_4352753, baseEnd_4352753] using wordTrace_append hprefix tailTrace_4352753
  have hstable : (prefixWord ++ tailWord_4352753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4352753).length < 2 ^ (prefixWord ++ tailWord_4352753).sum := by decide
  have hdescent : baseEnd_4352753 < baseStart_4352753 := by decide
  rcases family_descends (prefixWord ++ tailWord_4352753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4352754 : List Nat := [3, 2, 1, 3, 1, 3, 1, 3, 2, 1, 3]
def baseStart_4352754 : Nat := 118140960795 + 4352754 * 2 ^ 59
def prefixEnd_4352754 : Nat := 4983230072969 + 3 ^ 40 * 4352754 * 2
def baseEnd_4352754 : Nat := 2235054972780568063657055

theorem tailTrace_4352754 : CollatzResearch.WordTrace tailWord_4352754 prefixEnd_4352754 2235054972780568063657055 := by
  unfold tailWord_4352754
  simp only [CollatzResearch.WordTrace]
  refine ⟨39689495218180781010978329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105838653915148749362608877 39689495218180781010978329)
  ·
    refine ⟨29767121413635585758233747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39689495218180781010978329 29767121413635585758233747)
    ·
      refine ⟨44650682120453378637350621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29767121413635585758233747 44650682120453378637350621)
      ·
        refine ⟨16744005795170016989006483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44650682120453378637350621 16744005795170016989006483)
        ·
          refine ⟨25116008692755025483509725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16744005795170016989006483 25116008692755025483509725)
          ·
            refine ⟨9418503259783134556316147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25116008692755025483509725 9418503259783134556316147)
            ·
              refine ⟨14127754889674701834474221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9418503259783134556316147 14127754889674701834474221)
              ·
                refine ⟨5297908083628013187927833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14127754889674701834474221 5297908083628013187927833)
                ·
                  refine ⟨3973431062721009890945875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5297908083628013187927833 3973431062721009890945875)
                  ·
                    refine ⟨5960146594081514836418813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3973431062721009890945875 5960146594081514836418813)
                    ·
                      refine ⟨2235054972780568063657055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5960146594081514836418813 2235054972780568063657055)
                      ·
                        rfl

theorem cell23_4352754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 1, 3, 2, 1, 3].length) (baseStart_4352754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4352754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4352754 prefixEnd_4352754 := by exact prefixLift 4352754
  have htrace : WordTrace (prefixWord ++ tailWord_4352754) baseStart_4352754 baseEnd_4352754 := by
    simpa [prefixWord, tailWord_4352754, baseEnd_4352754] using wordTrace_append hprefix tailTrace_4352754
  have hstable : (prefixWord ++ tailWord_4352754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4352754).length < 2 ^ (prefixWord ++ tailWord_4352754).sum := by decide
  have hdescent : baseEnd_4352754 < baseStart_4352754 := by decide
  rcases family_descends (prefixWord ++ tailWord_4352754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4352764 : List Nat := [2, 2, 2, 1, 3, 2, 3, 2, 1, 3, 2]
def baseStart_4352764 : Nat := 118140960795 + 4352764 * 2 ^ 59
def prefixEnd_4352764 : Nat := 4983230072969 + 3 ^ 40 * 4352764 * 2
def baseEnd_4352764 : Nat := 2235060107587113024532009

theorem tailTrace_4352764 : CollatzResearch.WordTrace tailWord_4352764 prefixEnd_4352764 2235060107587113024532009 := by
  unfold tailWord_4352764
  simp only [CollatzResearch.WordTrace]
  refine ⟨79379172801343447875888673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105838897068457930501184897 79379172801343447875888673)
  ·
    refine ⟨59534379601007585906916505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79379172801343447875888673 59534379601007585906916505)
    ·
      refine ⟨44650784700755689430187379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59534379601007585906916505 44650784700755689430187379)
      ·
        refine ⟨66976177051133534145281069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44650784700755689430187379 66976177051133534145281069)
        ·
          refine ⟨25116066394175075304480401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66976177051133534145281069 25116066394175075304480401)
          ·
            refine ⟨18837049795631306478360301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25116066394175075304480401 18837049795631306478360301)
            ·
              refine ⟨7063893673361739929385113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18837049795631306478360301 7063893673361739929385113)
              ·
                refine ⟨5297920255021304947038835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7063893673361739929385113 5297920255021304947038835)
                ·
                  refine ⟨7946880382531957420558253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5297920255021304947038835 7946880382531957420558253)
                  ·
                    refine ⟨2980080143449484032709345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7946880382531957420558253 2980080143449484032709345)
                    ·
                      refine ⟨2235060107587113024532009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2980080143449484032709345 2235060107587113024532009)
                      ·
                        rfl

theorem cell23_4352764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 3, 2, 1, 3, 2].length) (baseStart_4352764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4352764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4352764 prefixEnd_4352764 := by exact prefixLift 4352764
  have htrace : WordTrace (prefixWord ++ tailWord_4352764) baseStart_4352764 baseEnd_4352764 := by
    simpa [prefixWord, tailWord_4352764, baseEnd_4352764] using wordTrace_append hprefix tailTrace_4352764
  have hstable : (prefixWord ++ tailWord_4352764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4352764).length < 2 ^ (prefixWord ++ tailWord_4352764).sum := by decide
  have hdescent : baseEnd_4352764 < baseStart_4352764 := by decide
  rcases family_descends (prefixWord ++ tailWord_4352764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4352777 : List Nat := [1, 2, 1, 1, 3, 2, 2, 1, 6, 2, 2]
def baseStart_4352777 : Nat := 118140960795 + 4352777 * 2 ^ 59
def prefixEnd_4352777 : Nat := 4983230072969 + 3 ^ 40 * 4352777 * 2
def baseEnd_4352777 : Nat := 2235066782835621473669449

theorem tailTrace_4352777 : CollatzResearch.WordTrace tailWord_4352777 prefixEnd_4352777 2235066782835621473669449 := by
  unfold tailWord_4352777
  simp only [CollatzResearch.WordTrace]
  refine ⟨158758819751639798972000585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105839213167759865981333723 158758819751639798972000585)
  ·
    refine ⟨119069114813729849229000439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 158758819751639798972000585 119069114813729849229000439)
    ·
      refine ⟨178603672220594773843500659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119069114813729849229000439 178603672220594773843500659)
      ·
        refine ⟨267905508330892160765250989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 178603672220594773843500659 267905508330892160765250989)
        ·
          refine ⟨100464565624084560286969121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 267905508330892160765250989 100464565624084560286969121)
          ·
            refine ⟨75348424218063420215226841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 100464565624084560286969121 75348424218063420215226841)
            ·
              refine ⟨56511318163547565161420131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75348424218063420215226841 56511318163547565161420131)
              ·
                refine ⟨84766977245321347742130197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56511318163547565161420131 84766977245321347742130197)
                ·
                  refine ⟨3973452058374438175412353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 84766977245321347742130197 3973452058374438175412353)
                  ·
                    refine ⟨2980089043780828631559265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3973452058374438175412353 2980089043780828631559265)
                    ·
                      refine ⟨2235066782835621473669449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2980089043780828631559265 2235066782835621473669449)
                      ·
                        rfl

theorem cell23_4352777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 1, 6, 2, 2].length) (baseStart_4352777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4352777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4352777 prefixEnd_4352777 := by exact prefixLift 4352777
  have htrace : WordTrace (prefixWord ++ tailWord_4352777) baseStart_4352777 baseEnd_4352777 := by
    simpa [prefixWord, tailWord_4352777, baseEnd_4352777] using wordTrace_append hprefix tailTrace_4352777
  have hstable : (prefixWord ++ tailWord_4352777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4352777).length < 2 ^ (prefixWord ++ tailWord_4352777).sum := by decide
  have hdescent : baseEnd_4352777 < baseStart_4352777 := by decide
  rcases family_descends (prefixWord ++ tailWord_4352777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4352803 : List Nat := [1, 1, 1, 4, 2, 1, 1, 1, 2, 1, 8]
def baseStart_4352803 : Nat := 118140960795 + 4352803 * 2 ^ 59
def prefixEnd_4352803 : Nat := 4983230072969 + 3 ^ 40 * 4352803 * 2
def baseEnd_4352803 : Nat := 2235080133332638371944329

theorem tailTrace_4352803 : CollatzResearch.WordTrace tailWord_4352803 prefixEnd_4352803 2235080133332638371944329 := by
  unfold tailWord_4352803
  simp only [CollatzResearch.WordTrace]
  refine ⟨158759768049545605412447063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105839845366363736941631375 158759768049545605412447063)
  ·
    refine ⟨238139652074318408118670595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158759768049545605412447063 238139652074318408118670595)
    ·
      refine ⟨357209478111477612178005893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 238139652074318408118670595 357209478111477612178005893)
      ·
        refine ⟨66976777145902052283376105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 357209478111477612178005893 66976777145902052283376105)
        ·
          refine ⟨50232582859426539212532079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66976777145902052283376105 50232582859426539212532079)
          ·
            refine ⟨75348874289139808818798119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50232582859426539212532079 75348874289139808818798119)
            ·
              refine ⟨113023311433709713228197179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75348874289139808818798119 113023311433709713228197179)
              ·
                refine ⟨169534967150564569842295769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 113023311433709713228197179 169534967150564569842295769)
                ·
                  refine ⟨127151225362923427381721827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 169534967150564569842295769 127151225362923427381721827)
                  ·
                    refine ⟨190726838044385141072582741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 127151225362923427381721827 190726838044385141072582741)
                    ·
                      refine ⟨2235080133332638371944329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 190726838044385141072582741 2235080133332638371944329)
                      ·
                        rfl

theorem cell23_4352803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 1, 2, 1, 8].length) (baseStart_4352803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4352803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4352803 prefixEnd_4352803 := by exact prefixLift 4352803
  have htrace : WordTrace (prefixWord ++ tailWord_4352803) baseStart_4352803 baseEnd_4352803 := by
    simpa [prefixWord, tailWord_4352803, baseEnd_4352803] using wordTrace_append hprefix tailTrace_4352803
  have hstable : (prefixWord ++ tailWord_4352803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4352803).length < 2 ^ (prefixWord ++ tailWord_4352803).sum := by decide
  have hdescent : baseEnd_4352803 < baseStart_4352803 := by decide
  rcases family_descends (prefixWord ++ tailWord_4352803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4352843 : List Nat := [1, 1, 1, 1, 3, 1, 1, 1, 3, 10]
def baseStart_4352843 : Nat := 118140960795 + 4352843 * 2 ^ 59
def prefixEnd_4352843 : Nat := 4983230072969 + 3 ^ 40 * 4352843 * 2
def baseEnd_4352843 : Nat := 745033557519606071814715

theorem tailTrace_4352843 : CollatzResearch.WordTrace tailWord_4352843 prefixEnd_4352843 745033557519606071814715 := by
  unfold tailWord_4352843
  simp only [CollatzResearch.WordTrace]
  refine ⟨158761226969400692243903183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105840817979600461495935455 158761226969400692243903183)
  ·
    refine ⟨238141840454101038365854775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158761226969400692243903183 238141840454101038365854775)
    ·
      refine ⟨357212760681151557548782163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 238141840454101038365854775 357212760681151557548782163)
      ·
        refine ⟨535819141021727336323173245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 357212760681151557548782163 535819141021727336323173245)
        ·
          refine ⟨200932177883147751121189967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 535819141021727336323173245 200932177883147751121189967)
          ·
            refine ⟨301398266824721626681784951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 200932177883147751121189967 301398266824721626681784951)
            ·
              refine ⟨452097400237082440022677427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 301398266824721626681784951 452097400237082440022677427)
              ·
                refine ⟨678146100355623660034016141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 452097400237082440022677427 678146100355623660034016141)
                ·
                  refine ⟨254304787633358872512756053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 678146100355623660034016141 254304787633358872512756053)
                  ·
                    refine ⟨745033557519606071814715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 254304787633358872512756053 745033557519606071814715)
                    ·
                      rfl

theorem cell23_4352843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 3, 10].length) (baseStart_4352843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4352843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4352843 prefixEnd_4352843 := by exact prefixLift 4352843
  have htrace : WordTrace (prefixWord ++ tailWord_4352843) baseStart_4352843 baseEnd_4352843 := by
    simpa [prefixWord, tailWord_4352843, baseEnd_4352843] using wordTrace_append hprefix tailTrace_4352843
  have hstable : (prefixWord ++ tailWord_4352843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4352843).length < 2 ^ (prefixWord ++ tailWord_4352843).sum := by decide
  have hdescent : baseEnd_4352843 < baseStart_4352843 := by decide
  rcases family_descends (prefixWord ++ tailWord_4352843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4352845 : List Nat := [1, 6, 1, 2, 2, 2, 1, 2, 2, 2, 2]
def baseStart_4352845 : Nat := 118140960795 + 4352845 * 2 ^ 59
def prefixEnd_4352845 : Nat := 4983230072969 + 3 ^ 40 * 4352845 * 2
def baseEnd_4352845 : Nat := 2235101699520127207619137

theorem tailTrace_4352845 : CollatzResearch.WordTrace tailWord_4352845 prefixEnd_4352845 2235101699520127207619137 := by
  unfold tailWord_4352845
  simp only [CollatzResearch.WordTrace]
  refine ⟨158761299915393446585475989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105840866610262297723650659 158761299915393446585475989)
  ·
    refine ⟨7441935933534067808694187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 158761299915393446585475989 7441935933534067808694187)
    ·
      refine ⟨11162903900301101713041281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7441935933534067808694187 11162903900301101713041281)
      ·
        refine ⟨8372177925225826284780961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11162903900301101713041281 8372177925225826284780961)
        ·
          refine ⟨6279133443919369713585721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8372177925225826284780961 6279133443919369713585721)
          ·
            refine ⟨4709350082939527285189291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6279133443919369713585721 4709350082939527285189291)
            ·
              refine ⟨7064025124409290927783937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4709350082939527285189291 7064025124409290927783937)
              ·
                refine ⟨5298018843306968195837953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7064025124409290927783937 5298018843306968195837953)
                ·
                  refine ⟨3973514132480226146878465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5298018843306968195837953 3973514132480226146878465)
                  ·
                    refine ⟨2980135599360169610158849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3973514132480226146878465 2980135599360169610158849)
                    ·
                      refine ⟨2235101699520127207619137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2980135599360169610158849 2235101699520127207619137)
                      ·
                        rfl

theorem cell23_4352845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 2, 1, 2, 2, 2, 2].length) (baseStart_4352845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4352845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4352845 prefixEnd_4352845 := by exact prefixLift 4352845
  have htrace : WordTrace (prefixWord ++ tailWord_4352845) baseStart_4352845 baseEnd_4352845 := by
    simpa [prefixWord, tailWord_4352845, baseEnd_4352845] using wordTrace_append hprefix tailTrace_4352845
  have hstable : (prefixWord ++ tailWord_4352845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4352845).length < 2 ^ (prefixWord ++ tailWord_4352845).sum := by decide
  have hdescent : baseEnd_4352845 < baseStart_4352845 := by decide
  rcases family_descends (prefixWord ++ tailWord_4352845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4352904 : List Nat := [2, 1, 3, 3, 2, 2, 1, 2, 2, 2, 3]
def baseStart_4352904 : Nat := 118140960795 + 4352904 * 2 ^ 59
def prefixEnd_4352904 : Nat := 4983230072969 + 3 ^ 40 * 4352904 * 2
def baseEnd_4352904 : Nat := 2235131994878742476781365

theorem tailTrace_4352904 : CollatzResearch.WordTrace tailWord_4352904 prefixEnd_4352904 2235131994878742476781365 := by
  unfold tailWord_4352904
  simp only [CollatzResearch.WordTrace]
  refine ⟨79381725911089849830936883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105842301214786466441249177 79381725911089849830936883)
  ·
    refine ⟨119072588866634774746405325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79381725911089849830936883 119072588866634774746405325)
    ·
      refine ⟨44652220824988040529901997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 119072588866634774746405325 44652220824988040529901997)
      ·
        refine ⟨16744582809370515198713249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44652220824988040529901997 16744582809370515198713249)
        ·
          refine ⟨12558437107027886399034937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16744582809370515198713249 12558437107027886399034937)
          ·
            refine ⟨9418827830270914799276203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12558437107027886399034937 9418827830270914799276203)
            ·
              refine ⟨14128241745406372198914305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9418827830270914799276203 14128241745406372198914305)
              ·
                refine ⟨10596181309054779149185729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14128241745406372198914305 10596181309054779149185729)
                ·
                  refine ⟨7947135981791084361889297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10596181309054779149185729 7947135981791084361889297)
                  ·
                    refine ⟨5960351986343313271416973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7947135981791084361889297 5960351986343313271416973)
                    ·
                      refine ⟨2235131994878742476781365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5960351986343313271416973 2235131994878742476781365)
                      ·
                        rfl

theorem cell23_4352904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 1, 2, 2, 2, 3].length) (baseStart_4352904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4352904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4352904 prefixEnd_4352904 := by exact prefixLift 4352904
  have htrace : WordTrace (prefixWord ++ tailWord_4352904) baseStart_4352904 baseEnd_4352904 := by
    simpa [prefixWord, tailWord_4352904, baseEnd_4352904] using wordTrace_append hprefix tailTrace_4352904
  have hstable : (prefixWord ++ tailWord_4352904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4352904).length < 2 ^ (prefixWord ++ tailWord_4352904).sum := by decide
  have hdescent : baseEnd_4352904 < baseStart_4352904 := by decide
  rcases family_descends (prefixWord ++ tailWord_4352904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4352924 : List Nat := [2, 2, 3, 3, 2, 1, 1, 3, 6]
def baseStart_4352924 : Nat := 118140960795 + 4352924 * 2 ^ 59
def prefixEnd_4352924 : Nat := 4983230072969 + 3 ^ 40 * 4352924 * 2
def baseEnd_4352924 : Nat := 248349140499092488725697

theorem tailTrace_4352924 : CollatzResearch.WordTrace tailWord_4352924 prefixEnd_4352924 248349140499092488725697 := by
  unfold tailWord_4352924
  simp only [CollatzResearch.WordTrace]
  refine ⟨79382090641053621538800913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105842787521404828718401217 79382090641053621538800913)
  ·
    refine ⟨59536567980790216154100685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79382090641053621538800913 59536567980790216154100685)
    ·
      refine ⟨22326212992796331057787757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59536567980790216154100685 22326212992796331057787757)
      ·
        refine ⟨8372329872298624146670409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22326212992796331057787757 8372329872298624146670409)
        ·
          refine ⟨6279247404223968110002807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8372329872298624146670409 6279247404223968110002807)
          ·
            refine ⟨9418871106335952165004211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6279247404223968110002807 9418871106335952165004211)
            ·
              refine ⟨14128306659503928247506317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9418871106335952165004211 14128306659503928247506317)
              ·
                refine ⟨5298114997313973092814869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14128306659503928247506317 5298114997313973092814869)
                ·
                  refine ⟨248349140499092488725697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5298114997313973092814869 248349140499092488725697)
                  ·
                    rfl

theorem cell23_4352924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 1, 3, 6].length) (baseStart_4352924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4352924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4352924 prefixEnd_4352924 := by exact prefixLift 4352924
  have htrace : WordTrace (prefixWord ++ tailWord_4352924) baseStart_4352924 baseEnd_4352924 := by
    simpa [prefixWord, tailWord_4352924, baseEnd_4352924] using wordTrace_append hprefix tailTrace_4352924
  have hstable : (prefixWord ++ tailWord_4352924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4352924).length < 2 ^ (prefixWord ++ tailWord_4352924).sum := by decide
  have hdescent : baseEnd_4352924 < baseStart_4352924 := by decide
  rcases family_descends (prefixWord ++ tailWord_4352924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4352940 : List Nat := [2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 4]
def baseStart_4352940 : Nat := 118140960795 + 4352940 * 2 ^ 59
def prefixEnd_4352940 : Nat := 4983230072969 + 3 ^ 40 * 4352940 * 2
def baseEnd_4352940 : Nat := 2235150480182304335931199

theorem tailTrace_4352940 : CollatzResearch.WordTrace tailWord_4352940 prefixEnd_4352940 2235150480182304335931199 := by
  unfold tailWord_4352940
  simp only [CollatzResearch.WordTrace]
  refine ⟨79382382425024638905092137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105843176566699518540122849 79382382425024638905092137)
  ·
    refine ⟨59536786818768479178819103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79382382425024638905092137 59536786818768479178819103)
    ·
      refine ⟨89305180228152718768228655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59536786818768479178819103 89305180228152718768228655)
      ·
        refine ⟨133957770342229078152342983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89305180228152718768228655 133957770342229078152342983)
        ·
          refine ⟨200936655513343617228514475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 133957770342229078152342983 200936655513343617228514475)
          ·
            refine ⟨301404983270015425842771713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 200936655513343617228514475 301404983270015425842771713)
            ·
              refine ⟨226053737452511569382078785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 301404983270015425842771713 226053737452511569382078785)
              ·
                refine ⟨169540303089383677036559089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 226053737452511569382078785 169540303089383677036559089)
                ·
                  refine ⟨127155227317037757777419317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 169540303089383677036559089 127155227317037757777419317)
                  ·
                    refine ⟨11920802560972289791633061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 127155227317037757777419317 11920802560972289791633061)
                    ·
                      refine ⟨2235150480182304335931199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11920802560972289791633061 2235150480182304335931199)
                      ·
                        rfl

theorem cell23_4352940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 4].length) (baseStart_4352940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4352940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4352940 prefixEnd_4352940 := by exact prefixLift 4352940
  have htrace : WordTrace (prefixWord ++ tailWord_4352940) baseStart_4352940 baseEnd_4352940 := by
    simpa [prefixWord, tailWord_4352940, baseEnd_4352940] using wordTrace_append hprefix tailTrace_4352940
  have hstable : (prefixWord ++ tailWord_4352940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4352940).length < 2 ^ (prefixWord ++ tailWord_4352940).sum := by decide
  have hdescent : baseEnd_4352940 < baseStart_4352940 := by decide
  rcases family_descends (prefixWord ++ tailWord_4352940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4352954 : List Nat := [3, 1, 1, 1, 2, 1, 7, 1, 1, 5]
def baseStart_4352954 : Nat := 118140960795 + 4352954 * 2 ^ 59
def prefixEnd_4352954 : Nat := 4983230072969 + 3 ^ 40 * 4352954 * 2
def baseEnd_4352954 : Nat := 745052556303822427052045

theorem tailTrace_4352954 : CollatzResearch.WordTrace tailWord_4352954 prefixEnd_4352954 745052556303822427052045 := by
  unfold tailWord_4352954
  simp only [CollatzResearch.WordTrace]
  refine ⟨39691318867999639550298479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105843516981332372134129277 39691318867999639550298479)
  ·
    refine ⟨59536978301999459325447719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39691318867999639550298479 59536978301999459325447719)
    ·
      refine ⟨89305467452999188988171579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59536978301999459325447719 89305467452999188988171579)
      ·
        refine ⟨133958201179498783482257369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89305467452999188988171579 133958201179498783482257369)
        ·
          refine ⟨100468650884624087611693027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 133958201179498783482257369 100468650884624087611693027)
          ·
            refine ⟨150702976326936131417539541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100468650884624087611693027 150702976326936131417539541)
            ·
              refine ⟨3532101007662565580098583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 150702976326936131417539541 3532101007662565580098583)
              ·
                refine ⟨5298151511493848370147875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3532101007662565580098583 5298151511493848370147875)
                ·
                  refine ⟨7947227267240772555221813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5298151511493848370147875 7947227267240772555221813)
                  ·
                    refine ⟨745052556303822427052045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7947227267240772555221813 745052556303822427052045)
                    ·
                      rfl

theorem cell23_4352954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 7, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 7, 1, 1, 5].length) (baseStart_4352954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4352954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4352954 prefixEnd_4352954 := by exact prefixLift 4352954
  have htrace : WordTrace (prefixWord ++ tailWord_4352954) baseStart_4352954 baseEnd_4352954 := by
    simpa [prefixWord, tailWord_4352954, baseEnd_4352954] using wordTrace_append hprefix tailTrace_4352954
  have hstable : (prefixWord ++ tailWord_4352954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4352954).length < 2 ^ (prefixWord ++ tailWord_4352954).sum := by decide
  have hdescent : baseEnd_4352954 < baseStart_4352954 := by decide
  rcases family_descends (prefixWord ++ tailWord_4352954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4352967 : List Nat := [1, 1, 4, 1, 1, 2, 2, 3, 4, 4]
def baseStart_4352967 : Nat := 118140960795 + 4352967 * 2 ^ 59
def prefixEnd_4352967 : Nat := 4983230072969 + 3 ^ 40 * 4352967 * 2
def baseEnd_4352967 : Nat := 745054781386658576764525

theorem tailTrace_4352967 : CollatzResearch.WordTrace tailWord_4352967 prefixEnd_4352967 745054781386658576764525 := by
  unfold tailWord_4352967
  simp only [CollatzResearch.WordTrace]
  refine ⟨158765749620951461421417155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105843833080634307614278103 158765749620951461421417155)
  ·
    refine ⟨238148624431427192132125733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158765749620951461421417155 238148624431427192132125733)
    ·
      refine ⟨44652867080892598524773575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 238148624431427192132125733 44652867080892598524773575)
      ·
        refine ⟨66979300621338897787160363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44652867080892598524773575 66979300621338897787160363)
        ·
          refine ⟨100468950932008346680740545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66979300621338897787160363 100468950932008346680740545)
          ·
            refine ⟨75351713199006260010555409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 100468950932008346680740545 75351713199006260010555409)
            ·
              refine ⟨56513784899254695007916557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75351713199006260010555409 56513784899254695007916557)
              ·
                refine ⟨21192669337220510627968709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56513784899254695007916557 21192669337220510627968709)
                ·
                  refine ⟨3973625500728845742744133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21192669337220510627968709 3973625500728845742744133)
                  ·
                    refine ⟨745054781386658576764525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3973625500728845742744133 745054781386658576764525)
                    ·
                      rfl

theorem cell23_4352967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 3, 4, 4].length) (baseStart_4352967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4352967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4352967 prefixEnd_4352967 := by exact prefixLift 4352967
  have htrace : WordTrace (prefixWord ++ tailWord_4352967) baseStart_4352967 baseEnd_4352967 := by
    simpa [prefixWord, tailWord_4352967, baseEnd_4352967] using wordTrace_append hprefix tailTrace_4352967
  have hstable : (prefixWord ++ tailWord_4352967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4352967).length < 2 ^ (prefixWord ++ tailWord_4352967).sum := by decide
  have hdescent : baseEnd_4352967 < baseStart_4352967 := by decide
  rcases family_descends (prefixWord ++ tailWord_4352967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4352968 : List Nat := [2, 1, 3, 1, 5, 1, 1, 4, 1, 1, 3]
def baseStart_4352968 : Nat := 118140960795 + 4352968 * 2 ^ 59
def prefixEnd_4352968 : Nat := 4983230072969 + 3 ^ 40 * 4352968 * 2
def baseEnd_4352968 : Nat := 2235164857640630226381071

theorem tailTrace_4352968 : CollatzResearch.WordTrace tailWord_4352968 prefixEnd_4352968 2235164857640630226381071 := by
  unfold tailWord_4352968
  simp only [CollatzResearch.WordTrace]
  refine ⟨79382893046973919296101779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105843857395965225728135705 79382893046973919296101779)
  ·
    refine ⟨119074339570460878944152669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79382893046973919296101779 119074339570460878944152669)
    ·
      refine ⟨44652877338922829604057251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 119074339570460878944152669 44652877338922829604057251)
      ·
        refine ⟨66979316008384244406085877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44652877338922829604057251 66979316008384244406085877)
        ·
          refine ⟨6279310875786022913070551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 66979316008384244406085877 6279310875786022913070551)
          ·
            refine ⟨9418966313679034369605827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6279310875786022913070551 9418966313679034369605827)
            ·
              refine ⟨14128449470518551554408741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9418966313679034369605827 14128449470518551554408741)
              ·
                refine ⟨2649084275722228416451639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14128449470518551554408741 2649084275722228416451639)
                ·
                  refine ⟨3973626413583342624677459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2649084275722228416451639 3973626413583342624677459)
                  ·
                    refine ⟨5960439620375013937016189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3973626413583342624677459 5960439620375013937016189)
                    ·
                      refine ⟨2235164857640630226381071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5960439620375013937016189 2235164857640630226381071)
                      ·
                        rfl

theorem cell23_4352968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 1, 4, 1, 1, 3].length) (baseStart_4352968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4352968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4352968 prefixEnd_4352968 := by exact prefixLift 4352968
  have htrace : WordTrace (prefixWord ++ tailWord_4352968) baseStart_4352968 baseEnd_4352968 := by
    simpa [prefixWord, tailWord_4352968, baseEnd_4352968] using wordTrace_append hprefix tailTrace_4352968
  have hstable : (prefixWord ++ tailWord_4352968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4352968).length < 2 ^ (prefixWord ++ tailWord_4352968).sum := by decide
  have hdescent : baseEnd_4352968 < baseStart_4352968 := by decide
  rcases family_descends (prefixWord ++ tailWord_4352968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4352977 : List Nat := [1, 2, 2, 1, 2, 1, 3, 1, 5, 2, 3]
def baseStart_4352977 : Nat := 118140960795 + 4352977 * 2 ^ 59
def prefixEnd_4352977 : Nat := 4983230072969 + 3 ^ 40 * 4352977 * 2
def baseEnd_4352977 : Nat := 2235169478966520691168529

theorem tailTrace_4352977 : CollatzResearch.WordTrace tailWord_4352977 prefixEnd_4352977 2235169478966520691168529 := by
  unfold tailWord_4352977
  simp only [CollatzResearch.WordTrace]
  refine ⟨158766114350915233129281185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105844076233943488752854123 158766114350915233129281185)
  ·
    refine ⟨119074585763186424846960889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 158766114350915233129281185 119074585763186424846960889)
    ·
      refine ⟨89305939322389818635220667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119074585763186424846960889 89305939322389818635220667)
      ·
        refine ⟨133958908983584727952831001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89305939322389818635220667 133958908983584727952831001)
        ·
          refine ⟨100469181737688545964623251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 133958908983584727952831001 100469181737688545964623251)
          ·
            refine ⟨150703772606532818946934877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100469181737688545964623251 150703772606532818946934877)
            ·
              refine ⟨56513914727449807105100579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 150703772606532818946934877 56513914727449807105100579)
              ·
                refine ⟨84770872091174710657650869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56513914727449807105100579 84770872091174710657650869)
                ·
                  refine ⟨7947269258547629124154769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 84770872091174710657650869 7947269258547629124154769)
                  ·
                    refine ⟨5960451943910721843116077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7947269258547629124154769 5960451943910721843116077)
                    ·
                      refine ⟨2235169478966520691168529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5960451943910721843116077 2235169478966520691168529)
                      ·
                        rfl

theorem cell23_4352977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 1, 5, 2, 3].length) (baseStart_4352977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4352977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4352977 prefixEnd_4352977 := by exact prefixLift 4352977
  have htrace : WordTrace (prefixWord ++ tailWord_4352977) baseStart_4352977 baseEnd_4352977 := by
    simpa [prefixWord, tailWord_4352977, baseEnd_4352977] using wordTrace_append hprefix tailTrace_4352977
  have hstable : (prefixWord ++ tailWord_4352977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4352977).length < 2 ^ (prefixWord ++ tailWord_4352977).sum := by decide
  have hdescent : baseEnd_4352977 < baseStart_4352977 := by decide
  rcases family_descends (prefixWord ++ tailWord_4352977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4352984 : List Nat := [2, 1, 2, 2, 2, 3, 2, 3, 2, 4]
def baseStart_4352984 : Nat := 118140960795 + 4352984 * 2 ^ 59
def prefixEnd_4352984 : Nat := 4983230072969 + 3 ^ 40 * 4352984 * 2
def baseEnd_4352984 : Nat := 745057691110367387926999

theorem tailTrace_4352984 : CollatzResearch.WordTrace tailWord_4352984 prefixEnd_4352984 745057691110367387926999 := by
  unfold tailWord_4352984
  simp only [CollatzResearch.WordTrace]
  refine ⟨79383184830944936662393003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105844246441259915549857337 79383184830944936662393003)
  ·
    refine ⟨119074777246417404993589505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79383184830944936662393003 119074777246417404993589505)
    ·
      refine ⟨89306082934813053745192129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119074777246417404993589505 89306082934813053745192129)
      ·
        refine ⟨66979562201109790308894097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89306082934813053745192129 66979562201109790308894097)
        ·
          refine ⟨50234671650832342731670573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66979562201109790308894097 50234671650832342731670573)
          ·
            refine ⟨18838001869062128524376465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50234671650832342731670573 18838001869062128524376465)
            ·
              refine ⟨14128501401796596393282349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18838001869062128524376465 14128501401796596393282349)
              ·
                refine ⟨5298188025673723647480881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14128501401796596393282349 5298188025673723647480881)
                ·
                  refine ⟨3973641019255292735610661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5298188025673723647480881 3973641019255292735610661)
                  ·
                    refine ⟨745057691110367387926999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3973641019255292735610661 745057691110367387926999)
                    ·
                      rfl

theorem cell23_4352984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 2, 3, 2, 4].length) (baseStart_4352984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4352984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4352984 prefixEnd_4352984 := by exact prefixLift 4352984
  have htrace : WordTrace (prefixWord ++ tailWord_4352984) baseStart_4352984 baseEnd_4352984 := by
    simpa [prefixWord, tailWord_4352984, baseEnd_4352984] using wordTrace_append hprefix tailTrace_4352984
  have hstable : (prefixWord ++ tailWord_4352984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4352984).length < 2 ^ (prefixWord ++ tailWord_4352984).sum := by decide
  have hdescent : baseEnd_4352984 < baseStart_4352984 := by decide
  rcases family_descends (prefixWord ++ tailWord_4352984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4353067 : List Nat := [1, 1, 1, 1, 2, 1, 7, 1, 2, 1, 5]
def baseStart_4353067 : Nat := 118140960795 + 4353067 * 2 ^ 59
def prefixEnd_4353067 : Nat := 4983230072969 + 3 ^ 40 * 4353067 * 2
def baseEnd_4353067 : Nat := 2235215692225425339043115

theorem tailTrace_4353067 : CollatzResearch.WordTrace tailWord_4353067 prefixEnd_4353067 2235215692225425339043115 := by
  unfold tailWord_4353067
  simp only [CollatzResearch.WordTrace]
  refine ⟨158769396920589178500057455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105846264613726119000038303 158769396920589178500057455)
  ·
    refine ⟨238154095380883767750086183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158769396920589178500057455 238154095380883767750086183)
    ·
      refine ⟨357231143071325651625129275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 238154095380883767750086183 357231143071325651625129275)
      ·
        refine ⟨535846714606988477437693913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 357231143071325651625129275 535846714606988477437693913)
        ·
          refine ⟨401885035955241358078270435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 535846714606988477437693913 401885035955241358078270435)
          ·
            refine ⟨602827553932862037117405653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 401885035955241358078270435 602827553932862037117405653)
            ·
              refine ⟨14128770795301453994939195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 602827553932862037117405653 14128770795301453994939195)
              ·
                refine ⟨21193156192952180992408793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14128770795301453994939195 21193156192952180992408793)
                ·
                  refine ⟨15894867144714135744306595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21193156192952180992408793 15894867144714135744306595)
                  ·
                    refine ⟨23842300717071203616459893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15894867144714135744306595 23842300717071203616459893)
                    ·
                      refine ⟨2235215692225425339043115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23842300717071203616459893 2235215692225425339043115)
                      ·
                        rfl

theorem cell23_4353067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 7, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 7, 1, 2, 1, 5].length) (baseStart_4353067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4353067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4353067 prefixEnd_4353067 := by exact prefixLift 4353067
  have htrace : WordTrace (prefixWord ++ tailWord_4353067) baseStart_4353067 baseEnd_4353067 := by
    simpa [prefixWord, tailWord_4353067, baseEnd_4353067] using wordTrace_append hprefix tailTrace_4353067
  have hstable : (prefixWord ++ tailWord_4353067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4353067).length < 2 ^ (prefixWord ++ tailWord_4353067).sum := by decide
  have hdescent : baseEnd_4353067 < baseStart_4353067 := by decide
  rcases family_descends (prefixWord ++ tailWord_4353067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4353118 : List Nat := [4, 4, 1, 1, 1, 1, 2, 1, 2, 1, 5]
def baseStart_4353118 : Nat := 118140960795 + 4353118 * 2 ^ 59
def prefixEnd_4353118 : Nat := 4983230072969 + 3 ^ 40 * 4353118 * 2
def baseEnd_4353118 : Nat := 2235241879738804639505381

theorem tailTrace_4353118 : CollatzResearch.WordTrace tailWord_4353118 prefixEnd_4353118 2235241879738804639505381 := by
  unfold tailWord_4353118
  simp only [CollatzResearch.WordTrace]
  refine ⟨19846407130425551776270501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 105847504695602942806776005 19846407130425551776270501)
  ·
    refine ⟨3721201336954790958050719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19846407130425551776270501 3721201336954790958050719)
    ·
      refine ⟨5581802005432186437076079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3721201336954790958050719 5581802005432186437076079)
      ·
        refine ⟨8372703008148279655614119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5581802005432186437076079 8372703008148279655614119)
        ·
          refine ⟨12559054512222419483421179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8372703008148279655614119 12559054512222419483421179)
          ·
            refine ⟨18838581768333629225131769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12559054512222419483421179 18838581768333629225131769)
            ·
              refine ⟨14128936326250221918848827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18838581768333629225131769 14128936326250221918848827)
              ·
                refine ⟨21193404489375332878273241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14128936326250221918848827 21193404489375332878273241)
                ·
                  refine ⟨15895053367031499658704931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21193404489375332878273241 15895053367031499658704931)
                  ·
                    refine ⟨23842580050547249488057397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15895053367031499658704931 23842580050547249488057397)
                    ·
                      refine ⟨2235241879738804639505381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23842580050547249488057397 2235241879738804639505381)
                      ·
                        rfl

theorem cell23_4353118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 2, 1, 2, 1, 5].length) (baseStart_4353118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4353118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4353118 prefixEnd_4353118 := by exact prefixLift 4353118
  have htrace : WordTrace (prefixWord ++ tailWord_4353118) baseStart_4353118 baseEnd_4353118 := by
    simpa [prefixWord, tailWord_4353118, baseEnd_4353118] using wordTrace_append hprefix tailTrace_4353118
  have hstable : (prefixWord ++ tailWord_4353118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4353118).length < 2 ^ (prefixWord ++ tailWord_4353118).sum := by decide
  have hdescent : baseEnd_4353118 < baseStart_4353118 := by decide
  rcases family_descends (prefixWord ++ tailWord_4353118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4353224 : List Nat := [2, 1, 3, 1, 2, 1, 2, 3, 3, 5]
def baseStart_4353224 : Nat := 118140960795 + 4353224 * 2 ^ 59
def prefixEnd_4353224 : Nat := 4983230072969 + 3 ^ 40 * 4353224 * 2
def baseEnd_4353224 : Nat := 745098769562727074926631

theorem tailTrace_4353224 : CollatzResearch.WordTrace tailWord_4353224 prefixEnd_4353224 745098769562727074926631 := by
  unfold tailWord_4353224
  simp only [CollatzResearch.WordTrace]
  refine ⟨79387561590510197156761363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105850082120680262875681817 79387561590510197156761363)
  ·
    refine ⟨119081342385765295735142045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79387561590510197156761363 119081342385765295735142045)
    ·
      refine ⟨44655503394661985900678267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 119081342385765295735142045 44655503394661985900678267)
      ·
        refine ⟨66983255091992978851017401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44655503394661985900678267 66983255091992978851017401)
        ·
          refine ⟨50237441318994734138263051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66983255091992978851017401 50237441318994734138263051)
          ·
            refine ⟨75356161978492101207394577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50237441318994734138263051 75356161978492101207394577)
            ·
              refine ⟨56517121483869075905545933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75356161978492101207394577 56517121483869075905545933)
              ·
                refine ⟨21193920556450903464579725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56517121483869075905545933 21193920556450903464579725)
                ·
                  refine ⟨7947720208669088799217397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21193920556450903464579725 7947720208669088799217397)
                  ·
                    refine ⟨745098769562727074926631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7947720208669088799217397 745098769562727074926631)
                    ·
                      rfl

theorem cell23_4353224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 3, 3, 5].length) (baseStart_4353224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4353224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4353224 prefixEnd_4353224 := by exact prefixLift 4353224
  have htrace : WordTrace (prefixWord ++ tailWord_4353224) baseStart_4353224 baseEnd_4353224 := by
    simpa [prefixWord, tailWord_4353224, baseEnd_4353224] using wordTrace_append hprefix tailTrace_4353224
  have hstable : (prefixWord ++ tailWord_4353224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4353224).length < 2 ^ (prefixWord ++ tailWord_4353224).sum := by decide
  have hdescent : baseEnd_4353224 < baseStart_4353224 := by decide
  rcases family_descends (prefixWord ++ tailWord_4353224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4353248 : List Nat := [2, 1, 1, 3, 1, 5, 1, 2, 2, 3, 2]
def baseStart_4353248 : Nat := 118140960795 + 4353248 * 2 ^ 59
def prefixEnd_4353248 : Nat := 4983230072969 + 3 ^ 40 * 4353248 * 2
def baseEnd_4353248 : Nat := 2235308632223889130879783

theorem tailTrace_4353248 : CollatzResearch.WordTrace tailWord_4353248 prefixEnd_4353248 2235308632223889130879783 := by
  unfold tailWord_4353248
  simp only [CollatzResearch.WordTrace]
  refine ⟨79387999266466723206198199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105850665688622297608264265 79387999266466723206198199)
  ·
    refine ⟨119081998899700084809297299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79387999266466723206198199 119081998899700084809297299)
    ·
      refine ⟨178622998349550127213945949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119081998899700084809297299 178622998349550127213945949)
      ·
        refine ⟨66983624381081297705229731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 178622998349550127213945949 66983624381081297705229731)
        ·
          refine ⟨100475436571621946557844597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66983624381081297705229731 100475436571621946557844597)
          ·
            refine ⟨9419572178589557489797931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 100475436571621946557844597 9419572178589557489797931)
            ·
              refine ⟨14129358267884336234696897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9419572178589557489797931 14129358267884336234696897)
              ·
                refine ⟨10597018700913252176022673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14129358267884336234696897 10597018700913252176022673)
                ·
                  refine ⟨7947764025684939132017005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10597018700913252176022673 7947764025684939132017005)
                  ·
                    refine ⟨2980411509631852174506377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7947764025684939132017005 2980411509631852174506377)
                    ·
                      refine ⟨2235308632223889130879783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2980411509631852174506377 2235308632223889130879783)
                      ·
                        rfl

theorem cell23_4353248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 1, 2, 2, 3, 2].length) (baseStart_4353248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4353248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4353248 prefixEnd_4353248 := by exact prefixLift 4353248
  have htrace : WordTrace (prefixWord ++ tailWord_4353248) baseStart_4353248 baseEnd_4353248 := by
    simpa [prefixWord, tailWord_4353248, baseEnd_4353248] using wordTrace_append hprefix tailTrace_4353248
  have hstable : (prefixWord ++ tailWord_4353248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4353248).length < 2 ^ (prefixWord ++ tailWord_4353248).sum := by decide
  have hdescent : baseEnd_4353248 < baseStart_4353248 := by decide
  rcases family_descends (prefixWord ++ tailWord_4353248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4353264 : List Nat := [2, 1, 1, 1, 3, 1, 1, 1, 1, 8, 3]
def baseStart_4353264 : Nat := 118140960795 + 4353264 * 2 ^ 59
def prefixEnd_4353264 : Nat := 4983230072969 + 3 ^ 40 * 4353264 * 2
def baseEnd_4353264 : Nat := 2235316847914361068279709

theorem tailTrace_4353264 : CollatzResearch.WordTrace tailWord_4353264 prefixEnd_4353264 2235316847914361068279709 := by
  unfold tailWord_4353264
  simp only [CollatzResearch.WordTrace]
  refine ⟨79388291050437740572489423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105851054733916987429985897 79388291050437740572489423)
  ·
    refine ⟨119082436575656610858734135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79388291050437740572489423 119082436575656610858734135)
    ·
      refine ⟨178623654863484916288101203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119082436575656610858734135 178623654863484916288101203)
      ·
        refine ⟨267935482295227374432151805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 178623654863484916288101203 267935482295227374432151805)
        ·
          refine ⟨100475805860710265412056927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 267935482295227374432151805 100475805860710265412056927)
          ·
            refine ⟨150713708791065398118085391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100475805860710265412056927 150713708791065398118085391)
            ·
              refine ⟨226070563186598097177128087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 150713708791065398118085391 226070563186598097177128087)
              ·
                refine ⟨339105844779897145765692131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 226070563186598097177128087 339105844779897145765692131)
                ·
                  refine ⟨508658767169845718648538197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 339105844779897145765692131 508658767169845718648538197)
                  ·
                    refine ⟨5960844927771629515412557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 508658767169845718648538197 5960844927771629515412557)
                    ·
                      refine ⟨2235316847914361068279709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5960844927771629515412557 2235316847914361068279709)
                      ·
                        rfl

theorem cell23_4353264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 1, 8, 3].length) (baseStart_4353264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4353264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4353264 prefixEnd_4353264 := by exact prefixLift 4353264
  have htrace : WordTrace (prefixWord ++ tailWord_4353264) baseStart_4353264 baseEnd_4353264 := by
    simpa [prefixWord, tailWord_4353264, baseEnd_4353264] using wordTrace_append hprefix tailTrace_4353264
  have hstable : (prefixWord ++ tailWord_4353264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4353264).length < 2 ^ (prefixWord ++ tailWord_4353264).sum := by decide
  have hdescent : baseEnd_4353264 < baseStart_4353264 := by decide
  rcases family_descends (prefixWord ++ tailWord_4353264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4353271 : List Nat := [1, 1, 3, 1, 1, 1, 2, 7, 2, 4]
def baseStart_4353271 : Nat := 118140960795 + 4353271 * 2 ^ 59
def prefixEnd_4353271 : Nat := 4983230072969 + 3 ^ 40 * 4353271 * 2
def baseEnd_4353271 : Nat := 745106814092980846964059

theorem tailTrace_4353271 : CollatzResearch.WordTrace tailWord_4353271 prefixEnd_4353271 745106814092980846964059 := by
  unfold tailWord_4353271
  simp only [CollatzResearch.WordTrace]
  refine ⟨158776837411850121340483667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105851224941233414226989111 158776837411850121340483667)
  ·
    refine ⟨238165256117775182010725501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158776837411850121340483667 238165256117775182010725501)
    ·
      refine ⟨89311971044165693254022063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 238165256117775182010725501 89311971044165693254022063)
      ·
        refine ⟨133967956566248539881033095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89311971044165693254022063 133967956566248539881033095)
        ·
          refine ⟨200951934849372809821549643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 133967956566248539881033095 200951934849372809821549643)
          ·
            refine ⟨301427902274059214732324465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 200951934849372809821549643 301427902274059214732324465)
            ·
              refine ⟨226070926705544411049243349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 301427902274059214732324465 226070926705544411049243349)
              ·
                refine ⟨5298537344661197133966641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 226070926705544411049243349 5298537344661197133966641)
                ·
                  refine ⟨3973903008495897850474981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5298537344661197133966641 3973903008495897850474981)
                  ·
                    refine ⟨745106814092980846964059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3973903008495897850474981 745106814092980846964059)
                    ·
                      rfl

theorem cell23_4353271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 7, 2, 4].length) (baseStart_4353271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4353271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4353271 prefixEnd_4353271 := by exact prefixLift 4353271
  have htrace : WordTrace (prefixWord ++ tailWord_4353271) baseStart_4353271 baseEnd_4353271 := by
    simpa [prefixWord, tailWord_4353271, baseEnd_4353271] using wordTrace_append hprefix tailTrace_4353271
  have hstable : (prefixWord ++ tailWord_4353271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4353271).length < 2 ^ (prefixWord ++ tailWord_4353271).sum := by decide
  have hdescent : baseEnd_4353271 < baseStart_4353271 := by decide
  rcases family_descends (prefixWord ++ tailWord_4353271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4353274 : List Nat := [3, 1, 1, 1, 1, 4, 1, 3, 1, 1, 6]
def baseStart_4353274 : Nat := 118140960795 + 4353274 * 2 ^ 59
def prefixEnd_4353274 : Nat := 4983230072969 + 3 ^ 40 * 4353274 * 2
def baseEnd_4353274 : Nat := 2235321982720906029154663

theorem tailTrace_4353274 : CollatzResearch.WordTrace tailWord_4353274 prefixEnd_4353274 2235321982720906029154663 := by
  unfold tailWord_4353274
  simp only [CollatzResearch.WordTrace]
  refine ⟨39694236707709813213210719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105851297887226168568561917 39694236707709813213210719)
  ·
    refine ⟨59541355061564719819816079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39694236707709813213210719 59541355061564719819816079)
    ·
      refine ⟨89312032592347079729724119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59541355061564719819816079 89312032592347079729724119)
      ·
        refine ⟨133968048888520619594586179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89312032592347079729724119 133968048888520619594586179)
        ·
          refine ⟨200952073332780929391879269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 133968048888520619594586179 200952073332780929391879269)
          ·
            refine ⟨37678513749896424260977363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 200952073332780929391879269 37678513749896424260977363)
            ·
              refine ⟨56517770624844636391466045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37678513749896424260977363 56517770624844636391466045)
              ·
                refine ⟨21194163984316738646799767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56517770624844636391466045 21194163984316738646799767)
                ·
                  refine ⟨31791245976475107970199651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21194163984316738646799767 31791245976475107970199651)
                  ·
                    refine ⟨47686868964712661955299477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 31791245976475107970199651 47686868964712661955299477)
                    ·
                      refine ⟨2235321982720906029154663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 47686868964712661955299477 2235321982720906029154663)
                      ·
                        rfl

theorem cell23_4353274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 3, 1, 1, 6].length) (baseStart_4353274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4353274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4353274 prefixEnd_4353274 := by exact prefixLift 4353274
  have htrace : WordTrace (prefixWord ++ tailWord_4353274) baseStart_4353274 baseEnd_4353274 := by
    simpa [prefixWord, tailWord_4353274, baseEnd_4353274] using wordTrace_append hprefix tailTrace_4353274
  have hstable : (prefixWord ++ tailWord_4353274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4353274).length < 2 ^ (prefixWord ++ tailWord_4353274).sum := by decide
  have hdescent : baseEnd_4353274 < baseStart_4353274 := by decide
  rcases family_descends (prefixWord ++ tailWord_4353274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4353278 : List Nat := [4, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4]
def baseStart_4353278 : Nat := 118140960795 + 4353278 * 2 ^ 59
def prefixEnd_4353278 : Nat := 4983230072969 + 3 ^ 40 * 4353278 * 2
def baseEnd_4353278 : Nat := 2235324036643524013504645

theorem tailTrace_4353278 : CollatzResearch.WordTrace tailWord_4353278 prefixEnd_4353278 2235324036643524013504645 := by
  unfold tailWord_4353278
  simp only [CollatzResearch.WordTrace]
  refine ⟨19847136590353095191998561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 105851395148549841023992325 19847136590353095191998561)
  ·
    refine ⟨14885352442764821393998921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19847136590353095191998561 14885352442764821393998921)
    ·
      refine ⟨11164014332073616045499191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14885352442764821393998921 11164014332073616045499191)
      ·
        refine ⟨16746021498110424068248787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11164014332073616045499191 16746021498110424068248787)
        ·
          refine ⟨25119032247165636102373181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16746021498110424068248787 25119032247165636102373181)
          ·
            refine ⟨9419637092687113538389943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25119032247165636102373181 9419637092687113538389943)
            ·
              refine ⟨14129455639030670307584915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9419637092687113538389943 14129455639030670307584915)
              ·
                refine ⟨21194183458546005461377373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14129455639030670307584915 21194183458546005461377373)
                ·
                  refine ⟨7947818796954752048016515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21194183458546005461377373 7947818796954752048016515)
                  ·
                    refine ⟨11921728195432128072024773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7947818796954752048016515 11921728195432128072024773)
                    ·
                      refine ⟨2235324036643524013504645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11921728195432128072024773 2235324036643524013504645)
                      ·
                        rfl

theorem cell23_4353278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4].length) (baseStart_4353278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4353278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4353278 prefixEnd_4353278 := by exact prefixLift 4353278
  have htrace : WordTrace (prefixWord ++ tailWord_4353278) baseStart_4353278 baseEnd_4353278 := by
    simpa [prefixWord, tailWord_4353278, baseEnd_4353278] using wordTrace_append hprefix tailTrace_4353278
  have hstable : (prefixWord ++ tailWord_4353278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4353278).length < 2 ^ (prefixWord ++ tailWord_4353278).sum := by decide
  have hdescent : baseEnd_4353278 < baseStart_4353278 := by decide
  rcases family_descends (prefixWord ++ tailWord_4353278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4353282 : List Nat := [3, 4, 1, 1, 3, 1, 2, 1, 2, 3, 2]
def baseStart_4353282 : Nat := 118140960795 + 4353282 * 2 ^ 59
def prefixEnd_4353282 : Nat := 4983230072969 + 3 ^ 40 * 4353282 * 2
def baseEnd_4353282 : Nat := 2235326090566141997854627

theorem tailTrace_4353282 : CollatzResearch.WordTrace tailWord_4353282 prefixEnd_4353282 2235326090566141997854627 := by
  unfold tailWord_4353282
  simp only [CollatzResearch.WordTrace]
  refine ⟨39694309653702567554783525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105851492409873513479422733 39694309653702567554783525)
  ·
    refine ⟨7442683060069231416521911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39694309653702567554783525 7442683060069231416521911)
    ·
      refine ⟨11164024590103847124782867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7442683060069231416521911 11164024590103847124782867)
      ·
        refine ⟨16746036885155770687174301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11164024590103847124782867 16746036885155770687174301)
        ·
          refine ⟨6279763831933414007690363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16746036885155770687174301 6279763831933414007690363)
          ·
            refine ⟨9419645747900121011535545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6279763831933414007690363 9419645747900121011535545)
            ·
              refine ⟨7064734310925090758651659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9419645747900121011535545 7064734310925090758651659)
              ·
                refine ⟨10597101466387636137977489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7064734310925090758651659 10597101466387636137977489)
                ·
                  refine ⟨7947826099790727103483117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10597101466387636137977489 7947826099790727103483117)
                  ·
                    refine ⟨2980434787421522663806169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7947826099790727103483117 2980434787421522663806169)
                    ·
                      refine ⟨2235326090566141997854627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2980434787421522663806169 2235326090566141997854627)
                      ·
                        rfl

theorem cell23_4353282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 2, 1, 2, 3, 2].length) (baseStart_4353282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4353282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4353282 prefixEnd_4353282 := by exact prefixLift 4353282
  have htrace : WordTrace (prefixWord ++ tailWord_4353282) baseStart_4353282 baseEnd_4353282 := by
    simpa [prefixWord, tailWord_4353282, baseEnd_4353282] using wordTrace_append hprefix tailTrace_4353282
  have hstable : (prefixWord ++ tailWord_4353282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4353282).length < 2 ^ (prefixWord ++ tailWord_4353282).sum := by decide
  have hdescent : baseEnd_4353282 < baseStart_4353282 := by decide
  rcases family_descends (prefixWord ++ tailWord_4353282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4353291 : List Nat := [1, 1, 1, 1, 5, 4, 1, 2, 1, 2, 4]
def baseStart_4353291 : Nat := 118140960795 + 4353291 * 2 ^ 59
def prefixEnd_4353291 : Nat := 4983230072969 + 3 ^ 40 * 4353291 * 2
def baseEnd_4353291 : Nat := 2235330711892032462642085

theorem tailTrace_4353291 : CollatzResearch.WordTrace tailWord_4353291 prefixEnd_4353291 2235330711892032462642085 := by
  unfold tailWord_4353291
  simp only [CollatzResearch.WordTrace]
  refine ⟨158777566871777664756211727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105851711247851776504141151 158777566871777664756211727)
  ·
    refine ⟨238166350307666497134317591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158777566871777664756211727 238166350307666497134317591)
    ·
      refine ⟨357249525461499745701476387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 238166350307666497134317591 357249525461499745701476387)
      ·
        refine ⟨535874288192249618552214581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 357249525461499745701476387 535874288192249618552214581)
        ·
          refine ⟨50238214518023401739270117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 535874288192249618552214581 50238214518023401739270117)
          ·
            refine ⟨9419665222129387826113147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 50238214518023401739270117 9419665222129387826113147)
            ·
              refine ⟨14129497833194081739169721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9419665222129387826113147 14129497833194081739169721)
              ·
                refine ⟨10597123374895561304377291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14129497833194081739169721 10597123374895561304377291)
                ·
                  refine ⟨15895685062343341956565937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10597123374895561304377291 15895685062343341956565937)
                  ·
                    refine ⟨11921763796757506467424453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15895685062343341956565937 11921763796757506467424453)
                    ·
                      refine ⟨2235330711892032462642085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11921763796757506467424453 2235330711892032462642085)
                      ·
                        rfl

theorem cell23_4353291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 1, 2, 1, 2, 4].length) (baseStart_4353291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4353291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4353291 prefixEnd_4353291 := by exact prefixLift 4353291
  have htrace : WordTrace (prefixWord ++ tailWord_4353291) baseStart_4353291 baseEnd_4353291 := by
    simpa [prefixWord, tailWord_4353291, baseEnd_4353291] using wordTrace_append hprefix tailTrace_4353291
  have hstable : (prefixWord ++ tailWord_4353291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4353291).length < 2 ^ (prefixWord ++ tailWord_4353291).sum := by decide
  have hdescent : baseEnd_4353291 < baseStart_4353291 := by decide
  rcases family_descends (prefixWord ++ tailWord_4353291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4353324 : List Nat := [2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 5]
def baseStart_4353324 : Nat := 118140960795 + 4353324 * 2 ^ 59
def prefixEnd_4353324 : Nat := 4983230072969 + 3 ^ 40 * 4353324 * 2
def baseEnd_4353324 : Nat := 2235347656753630833529433

theorem tailTrace_4353324 : CollatzResearch.WordTrace tailWord_4353324 prefixEnd_4353324 2235347656753630833529433 := by
  unfold tailWord_4353324
  simp only [CollatzResearch.WordTrace]
  refine ⟨79389385240329055696081513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105852513653772074261442017 79389385240329055696081513)
  ·
    refine ⟨59542038930246791772061135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79389385240329055696081513 59542038930246791772061135)
    ·
      refine ⟨89313058395370187658091703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59542038930246791772061135 89313058395370187658091703)
      ·
        refine ⟨133969587593055281487137555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89313058395370187658091703 133969587593055281487137555)
        ·
          refine ⟨200954381389582922230706333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 133969587593055281487137555 200954381389582922230706333)
          ·
            refine ⟨75357893021093595836514875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 200954381389582922230706333 75357893021093595836514875)
            ·
              refine ⟨113036839531640393754772313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75357893021093595836514875 113036839531640393754772313)
              ·
                refine ⟨84777629648730295316079235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 113036839531640393754772313 84777629648730295316079235)
                ·
                  refine ⟨127166444473095442974118853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 84777629648730295316079235 127166444473095442974118853)
                  ·
                    refine ⟨23843708338705395557647285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 127166444473095442974118853 23843708338705395557647285)
                    ·
                      refine ⟨2235347656753630833529433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23843708338705395557647285 2235347656753630833529433)
                      ·
                        rfl

theorem cell23_4353324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 5].length) (baseStart_4353324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4353324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4353324 prefixEnd_4353324 := by exact prefixLift 4353324
  have htrace : WordTrace (prefixWord ++ tailWord_4353324) baseStart_4353324 baseEnd_4353324 := by
    simpa [prefixWord, tailWord_4353324, baseEnd_4353324] using wordTrace_append hprefix tailTrace_4353324
  have hstable : (prefixWord ++ tailWord_4353324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4353324).length < 2 ^ (prefixWord ++ tailWord_4353324).sum := by decide
  have hdescent : baseEnd_4353324 < baseStart_4353324 := by decide
  rcases family_descends (prefixWord ++ tailWord_4353324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4353325 : List Nat := [1, 5, 3, 1, 1, 2, 2, 1, 1, 2, 4]
def baseStart_4353325 : Nat := 118140960795 + 4353325 * 2 ^ 59
def prefixEnd_4353325 : Nat := 4983230072969 + 3 ^ 40 * 4353325 * 2
def baseEnd_4353325 : Nat := 2235348170234285329616929

theorem tailTrace_4353325 : CollatzResearch.WordTrace tailWord_4353325 prefixEnd_4353325 2235348170234285329616929 := by
  unfold tailWord_4353325
  simp only [CollatzResearch.WordTrace]
  refine ⟨158778806953654488562949429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105852537969102992375299619 158778806953654488562949429)
  ·
    refine ⟨14885513151905108302776509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 158778806953654488562949429 14885513151905108302776509)
    ·
      refine ⟨5582067431964415613541191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14885513151905108302776509 5582067431964415613541191)
      ·
        refine ⟨8373101147946623420311787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5582067431964415613541191 8373101147946623420311787)
        ·
          refine ⟨12559651721919935130467681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8373101147946623420311787 12559651721919935130467681)
          ·
            refine ⟨9419738791439951347850761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12559651721919935130467681 9419738791439951347850761)
            ·
              refine ⟨7064804093579963510888071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9419738791439951347850761 7064804093579963510888071)
              ·
                refine ⟨10597206140369945266332107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7064804093579963510888071 10597206140369945266332107)
                ·
                  refine ⟨15895809210554917899498161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10597206140369945266332107 15895809210554917899498161)
                  ·
                    refine ⟨11921856907916188424623621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15895809210554917899498161 11921856907916188424623621)
                    ·
                      refine ⟨2235348170234285329616929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11921856907916188424623621 2235348170234285329616929)
                      ·
                        rfl

theorem cell23_4353325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 2, 1, 1, 2, 4].length) (baseStart_4353325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4353325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4353325 prefixEnd_4353325 := by exact prefixLift 4353325
  have htrace : WordTrace (prefixWord ++ tailWord_4353325) baseStart_4353325 baseEnd_4353325 := by
    simpa [prefixWord, tailWord_4353325, baseEnd_4353325] using wordTrace_append hprefix tailTrace_4353325
  have hstable : (prefixWord ++ tailWord_4353325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4353325).length < 2 ^ (prefixWord ++ tailWord_4353325).sum := by decide
  have hdescent : baseEnd_4353325 < baseStart_4353325 := by decide
  rcases family_descends (prefixWord ++ tailWord_4353325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4353328 : List Nat := [2, 1, 1, 1, 2, 2, 3, 5, 2, 1, 3]
def baseStart_4353328 : Nat := 118140960795 + 4353328 * 2 ^ 59
def prefixEnd_4353328 : Nat := 4983230072969 + 3 ^ 40 * 4353328 * 2
def baseEnd_4353328 : Nat := 2235349710676248817879415

theorem tailTrace_4353328 : CollatzResearch.WordTrace tailWord_4353328 prefixEnd_4353328 2235349710676248817879415 := by
  unfold tailWord_4353328
  simp only [CollatzResearch.WordTrace]
  refine ⟨79389458186321810037654319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105852610915095746716872425 79389458186321810037654319)
  ·
    refine ⟨119084187279482715056481479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79389458186321810037654319 119084187279482715056481479)
    ·
      refine ⟨178626280919224072584722219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119084187279482715056481479 178626280919224072584722219)
      ·
        refine ⟨267939421378836108877083329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 178626280919224072584722219 267939421378836108877083329)
        ·
          refine ⟨200954566034127081657812497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 267939421378836108877083329 200954566034127081657812497)
          ·
            refine ⟨150715924525595311243359373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 200954566034127081657812497 150715924525595311243359373)
            ·
              refine ⟨56518471697098241716259765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 150715924525595311243359373 56518471697098241716259765)
              ·
                refine ⟨5298606721602960160899353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 56518471697098241716259765 5298606721602960160899353)
                ·
                  refine ⟨3973955041202220120674515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5298606721602960160899353 3973955041202220120674515)
                  ·
                    refine ⟨5960932561803330181011773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3973955041202220120674515 5960932561803330181011773)
                    ·
                      refine ⟨2235349710676248817879415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5960932561803330181011773 2235349710676248817879415)
                      ·
                        rfl

theorem cell23_4353328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 5, 2, 1, 3].length) (baseStart_4353328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4353328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4353328 prefixEnd_4353328 := by exact prefixLift 4353328
  have htrace : WordTrace (prefixWord ++ tailWord_4353328) baseStart_4353328 baseEnd_4353328 := by
    simpa [prefixWord, tailWord_4353328, baseEnd_4353328] using wordTrace_append hprefix tailTrace_4353328
  have hstable : (prefixWord ++ tailWord_4353328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4353328).length < 2 ^ (prefixWord ++ tailWord_4353328).sum := by decide
  have hdescent : baseEnd_4353328 < baseStart_4353328 := by decide
  rcases family_descends (prefixWord ++ tailWord_4353328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4353338 : List Nat := [3, 1, 1, 1, 4, 1, 1, 3, 3, 3, 2]
def baseStart_4353338 : Nat := 118140960795 + 4353338 * 2 ^ 59
def prefixEnd_4353338 : Nat := 4983230072969 + 3 ^ 40 * 4353338 * 2
def baseEnd_4353338 : Nat := 2235354845482793778754369

theorem tailTrace_4353338 : CollatzResearch.WordTrace tailWord_4353338 prefixEnd_4353338 2235354845482793778754369 := by
  unfold tailWord_4353338
  simp only [CollatzResearch.WordTrace]
  refine ⟨39694820275651847945793167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105852854068404927855448445 39694820275651847945793167)
  ·
    refine ⟨59542230413477771918689751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39694820275651847945793167 59542230413477771918689751)
    ·
      refine ⟨89313345620216657878034627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59542230413477771918689751 89313345620216657878034627)
      ·
        refine ⟨133970018430324986817051941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89313345620216657878034627 133970018430324986817051941)
        ·
          refine ⟨25119378455685935028197239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 133970018430324986817051941 25119378455685935028197239)
          ·
            refine ⟨37679067683528902542295859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25119378455685935028197239 37679067683528902542295859)
            ·
              refine ⟨56518601525293353813443789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37679067683528902542295859 56518601525293353813443789)
              ·
                refine ⟨21194475571985007680041421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56518601525293353813443789 21194475571985007680041421)
                ·
                  refine ⟨7947928339494377880015533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21194475571985007680041421 7947928339494377880015533)
                  ·
                    refine ⟨2980473127310391705005825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7947928339494377880015533 2980473127310391705005825)
                    ·
                      refine ⟨2235354845482793778754369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2980473127310391705005825 2235354845482793778754369)
                      ·
                        rfl

theorem cell23_4353338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 3, 3, 3, 2].length) (baseStart_4353338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4353338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4353338 prefixEnd_4353338 := by exact prefixLift 4353338
  have htrace : WordTrace (prefixWord ++ tailWord_4353338) baseStart_4353338 baseEnd_4353338 := by
    simpa [prefixWord, tailWord_4353338, baseEnd_4353338] using wordTrace_append hprefix tailTrace_4353338
  have hstable : (prefixWord ++ tailWord_4353338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4353338).length < 2 ^ (prefixWord ++ tailWord_4353338).sum := by decide
  have hdescent : baseEnd_4353338 < baseStart_4353338 := by decide
  rcases family_descends (prefixWord ++ tailWord_4353338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4353344 : List Nat := [2, 1, 1, 2, 2, 1, 3, 2, 1, 8]
def baseStart_4353344 : Nat := 118140960795 + 4353344 * 2 ^ 59
def prefixEnd_4353344 : Nat := 4983230072969 + 3 ^ 40 * 4353344 * 2
def baseEnd_4353344 : Nat := 745119308788906918426447

theorem tailTrace_4353344 : CollatzResearch.WordTrace tailWord_4353344 prefixEnd_4353344 745119308788906918426447 := by
  unfold tailWord_4353344
  simp only [CollatzResearch.WordTrace]
  refine ⟨79389749970292827403945543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105852999960390436538594057 79389749970292827403945543)
  ·
    refine ⟨119084624955439241105918315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79389749970292827403945543 119084624955439241105918315)
    ·
      refine ⟨178626937433158861658877473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119084624955439241105918315 178626937433158861658877473)
      ·
        refine ⟨133970203074869146244158105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 178626937433158861658877473 133970203074869146244158105)
        ·
          refine ⟨100477652306151859683118579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 133970203074869146244158105 100477652306151859683118579)
          ·
            refine ⟨150716478459227789524677869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100477652306151859683118579 150716478459227789524677869)
            ·
              refine ⟨56518679422210421071754201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 150716478459227789524677869 56518679422210421071754201)
              ·
                refine ⟨42389009566657815803815651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56518679422210421071754201 42389009566657815803815651)
                ·
                  refine ⟨63583514349986723705723477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42389009566657815803815651 63583514349986723705723477)
                  ·
                    refine ⟨745119308788906918426447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 63583514349986723705723477 745119308788906918426447)
                    ·
                      rfl

theorem cell23_4353344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 2, 1, 8].length) (baseStart_4353344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4353344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4353344 prefixEnd_4353344 := by exact prefixLift 4353344
  have htrace : WordTrace (prefixWord ++ tailWord_4353344) baseStart_4353344 baseEnd_4353344 := by
    simpa [prefixWord, tailWord_4353344, baseEnd_4353344] using wordTrace_append hprefix tailTrace_4353344
  have hstable : (prefixWord ++ tailWord_4353344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4353344).length < 2 ^ (prefixWord ++ tailWord_4353344).sum := by decide
  have hdescent : baseEnd_4353344 < baseStart_4353344 := by decide
  rcases family_descends (prefixWord ++ tailWord_4353344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4353381 : List Nat := [1, 3, 1, 3, 1, 2, 1, 3, 2, 2, 4]
def baseStart_4353381 : Nat := 118140960795 + 4353381 * 2 ^ 59
def prefixEnd_4353381 : Nat := 4983230072969 + 3 ^ 40 * 4353381 * 2
def baseEnd_4353381 : Nat := 2235376925150937110516671

theorem tailTrace_4353381 : CollatzResearch.WordTrace tailWord_4353381 prefixEnd_4353381 2235376925150937110516671 := by
  unfold tailWord_4353381
  simp only [CollatzResearch.WordTrace]
  refine ⟨158780849441451610126987997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105853899627634406751325331 158780849441451610126987997)
  ·
    refine ⟨59542818540544353797620499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 158780849441451610126987997 59542818540544353797620499)
    ·
      refine ⟨89314227810816530696430749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59542818540544353797620499 89314227810816530696430749)
      ·
        refine ⟨33492835429056199011161531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 89314227810816530696430749 33492835429056199011161531)
        ·
          refine ⟨50239253143584298516742297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33492835429056199011161531 50239253143584298516742297)
          ·
            refine ⟨37679439857688223887556723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50239253143584298516742297 37679439857688223887556723)
            ·
              refine ⟨56519159786532335831335085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37679439857688223887556723 56519159786532335831335085)
              ·
                refine ⟨21194684919949625936750657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56519159786532335831335085 21194684919949625936750657)
                ·
                  refine ⟨15896013689962219452562993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21194684919949625936750657 15896013689962219452562993)
                  ·
                    refine ⟨11922010267471664589422245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15896013689962219452562993 11922010267471664589422245)
                    ·
                      refine ⟨2235376925150937110516671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11922010267471664589422245 2235376925150937110516671)
                      ·
                        rfl

theorem cell23_4353381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 3, 2, 2, 4].length) (baseStart_4353381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4353381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4353381 prefixEnd_4353381 := by exact prefixLift 4353381
  have htrace : WordTrace (prefixWord ++ tailWord_4353381) baseStart_4353381 baseEnd_4353381 := by
    simpa [prefixWord, tailWord_4353381, baseEnd_4353381] using wordTrace_append hprefix tailTrace_4353381
  have hstable : (prefixWord ++ tailWord_4353381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4353381).length < 2 ^ (prefixWord ++ tailWord_4353381).sum := by decide
  have hdescent : baseEnd_4353381 < baseStart_4353381 := by decide
  rcases family_descends (prefixWord ++ tailWord_4353381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4353401 : List Nat := [1, 2, 1, 3, 2, 1, 2, 2, 1, 5, 3]
def baseStart_4353401 : Nat := 118140960795 + 4353401 * 2 ^ 59
def prefixEnd_4353401 : Nat := 4983230072969 + 3 ^ 40 * 4353401 * 2
def baseEnd_4353401 : Nat := 2235387194764027032266579

theorem tailTrace_4353401 : CollatzResearch.WordTrace tailWord_4353401 prefixEnd_4353401 2235387194764027032266579 := by
  unfold tailWord_4353401
  simp only [CollatzResearch.WordTrace]
  refine ⟨158781578901379153542716057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105854385934252769028477371 158781578901379153542716057)
  ·
    refine ⟨119086184176034365157037043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 158781578901379153542716057 119086184176034365157037043)
    ·
      refine ⟨178629276264051547735555565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119086184176034365157037043 178629276264051547735555565)
      ·
        refine ⟨66985978599019330400833337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 178629276264051547735555565 66985978599019330400833337)
        ·
          refine ⟨50239483949264497800625003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66985978599019330400833337 50239483949264497800625003)
          ·
            refine ⟨75359225923896746700937505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50239483949264497800625003 75359225923896746700937505)
            ·
              refine ⟨56519419442922560025703129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75359225923896746700937505 56519419442922560025703129)
              ·
                refine ⟨42389564582191920019277347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56519419442922560025703129 42389564582191920019277347)
                ·
                  refine ⟨63584346873287880028916021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42389564582191920019277347 63584346873287880028916021)
                  ·
                    refine ⟨5961032519370738752710877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 63584346873287880028916021 5961032519370738752710877)
                    ·
                      refine ⟨2235387194764027032266579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5961032519370738752710877 2235387194764027032266579)
                      ·
                        rfl

theorem cell23_4353401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 2, 1, 5, 3].length) (baseStart_4353401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4353401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4353401 prefixEnd_4353401 := by exact prefixLift 4353401
  have htrace : WordTrace (prefixWord ++ tailWord_4353401) baseStart_4353401 baseEnd_4353401 := by
    simpa [prefixWord, tailWord_4353401, baseEnd_4353401] using wordTrace_append hprefix tailTrace_4353401
  have hstable : (prefixWord ++ tailWord_4353401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4353401).length < 2 ^ (prefixWord ++ tailWord_4353401).sum := by decide
  have hdescent : baseEnd_4353401 < baseStart_4353401 := by decide
  rcases family_descends (prefixWord ++ tailWord_4353401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4353458 : List Nat := [3, 2, 1, 1, 1, 1, 2, 1, 3, 6, 2]
def baseStart_4353458 : Nat := 118140960795 + 4353458 * 2 ^ 59
def prefixEnd_4353458 : Nat := 4983230072969 + 3 ^ 40 * 4353458 * 2
def baseEnd_4353458 : Nat := 2235416463161333309253817

theorem tailTrace_4353458 : CollatzResearch.WordTrace tailWord_4353458 prefixEnd_4353458 2235416463161333309253817 := by
  unfold tailWord_4353458
  simp only [CollatzResearch.WordTrace]
  refine ⟨39695914465543163069385257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105855771908115101518360685 39695914465543163069385257)
  ·
    refine ⟨29771935849157372302038943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39695914465543163069385257 29771935849157372302038943)
    ·
      refine ⟨44657903773736058453058415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29771935849157372302038943 44657903773736058453058415)
      ·
        refine ⟨66986855660604087679587623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44657903773736058453058415 66986855660604087679587623)
        ·
          refine ⟨100480283490906131519381435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66986855660604087679587623 100480283490906131519381435)
          ·
            refine ⟨150720425236359197279072153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100480283490906131519381435 150720425236359197279072153)
            ·
              refine ⟨113040318927269397959304115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 150720425236359197279072153 113040318927269397959304115)
              ·
                refine ⟨169560478390904096938956173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 113040318927269397959304115 169560478390904096938956173)
                ·
                  refine ⟨63585179396589036352108565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 169560478390904096938956173 63585179396589036352108565)
                  ·
                    refine ⟨2980555284215111079005089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 63585179396589036352108565 2980555284215111079005089)
                    ·
                      refine ⟨2235416463161333309253817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2980555284215111079005089 2235416463161333309253817)
                      ·
                        rfl

theorem cell23_4353458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 1, 3, 6, 2].length) (baseStart_4353458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4353458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4353458 prefixEnd_4353458 := by exact prefixLift 4353458
  have htrace : WordTrace (prefixWord ++ tailWord_4353458) baseStart_4353458 baseEnd_4353458 := by
    simpa [prefixWord, tailWord_4353458, baseEnd_4353458] using wordTrace_append hprefix tailTrace_4353458
  have hstable : (prefixWord ++ tailWord_4353458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4353458).length < 2 ^ (prefixWord ++ tailWord_4353458).sum := by decide
  have hdescent : baseEnd_4353458 < baseStart_4353458 := by decide
  rcases family_descends (prefixWord ++ tailWord_4353458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4353492 : List Nat := [2, 4, 1, 2, 3, 1, 1, 1, 2, 4, 2]
def baseStart_4353492 : Nat := 118140960795 + 4353492 * 2 ^ 59
def prefixEnd_4353492 : Nat := 4983230072969 + 3 ^ 40 * 4353492 * 2
def baseEnd_4353492 : Nat := 2235433921503586176228661

theorem tailTrace_4353492 : CollatzResearch.WordTrace tailWord_4353492 prefixEnd_4353492 2235433921503586176228661 := by
  unfold tailWord_4353492
  simp only [CollatzResearch.WordTrace]
  refine ⟨79392448972024738042139365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105856598629366317389519153 79392448972024738042139365)
  ·
    refine ⟨14886084182254638382901131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 79392448972024738042139365 14886084182254638382901131)
    ·
      refine ⟨22329126273381957574351697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14886084182254638382901131 22329126273381957574351697)
      ·
        refine ⟨16746844705036468180763773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22329126273381957574351697 16746844705036468180763773)
        ·
          refine ⟨6280066764388675567786415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16746844705036468180763773 6280066764388675567786415)
          ·
            refine ⟨9420100146583013351679623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6280066764388675567786415 9420100146583013351679623)
            ·
              refine ⟨14130150219874520027519435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9420100146583013351679623 14130150219874520027519435)
              ·
                refine ⟨21195225329811780041279153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14130150219874520027519435 21195225329811780041279153)
                ·
                  refine ⟨15896418997358835030959365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21195225329811780041279153 15896418997358835030959365)
                  ·
                    refine ⟨2980578562004781568304881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15896418997358835030959365 2980578562004781568304881)
                    ·
                      refine ⟨2235433921503586176228661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2980578562004781568304881 2235433921503586176228661)
                      ·
                        rfl

theorem cell23_4353492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 1, 1, 2, 4, 2].length) (baseStart_4353492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4353492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4353492 prefixEnd_4353492 := by exact prefixLift 4353492
  have htrace : WordTrace (prefixWord ++ tailWord_4353492) baseStart_4353492 baseEnd_4353492 := by
    simpa [prefixWord, tailWord_4353492, baseEnd_4353492] using wordTrace_append hprefix tailTrace_4353492
  have hstable : (prefixWord ++ tailWord_4353492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4353492).length < 2 ^ (prefixWord ++ tailWord_4353492).sum := by decide
  have hdescent : baseEnd_4353492 < baseStart_4353492 := by decide
  rcases family_descends (prefixWord ++ tailWord_4353492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4353498 : List Nat := [3, 1, 1, 2, 3, 2, 2, 3, 6]
def baseStart_4353498 : Nat := 118140960795 + 4353498 * 2 ^ 59
def prefixEnd_4353498 : Nat := 4983230072969 + 3 ^ 40 * 4353498 * 2
def baseEnd_4353498 : Nat := 248381889154168128083737

theorem tailTrace_4353498 : CollatzResearch.WordTrace tailWord_4353498 prefixEnd_4353498 248381889154168128083737 := by
  unfold tailWord_4353498
  simp only [CollatzResearch.WordTrace]
  refine ⟨39696279195506934777249287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105856744521351826072664765 39696279195506934777249287)
  ·
    refine ⟨59544418793260402165873931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39696279195506934777249287 59544418793260402165873931)
    ·
      refine ⟨89316628189890603248810897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59544418793260402165873931 89316628189890603248810897)
      ·
        refine ⟨66987471142417952436608173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89316628189890603248810897 66987471142417952436608173)
        ·
          refine ⟨25120301678406732163728065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66987471142417952436608173 25120301678406732163728065)
          ·
            refine ⟨18840226258805049122796049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25120301678406732163728065 18840226258805049122796049)
            ·
              refine ⟨14130169694103786842097037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18840226258805049122796049 14130169694103786842097037)
              ·
                refine ⟨5298813635288920065786389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14130169694103786842097037 5298813635288920065786389)
                ·
                  refine ⟨248381889154168128083737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5298813635288920065786389 248381889154168128083737)
                  ·
                    rfl

theorem cell23_4353498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 2, 3, 6].length) (baseStart_4353498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4353498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4353498 prefixEnd_4353498 := by exact prefixLift 4353498
  have htrace : WordTrace (prefixWord ++ tailWord_4353498) baseStart_4353498 baseEnd_4353498 := by
    simpa [prefixWord, tailWord_4353498, baseEnd_4353498] using wordTrace_append hprefix tailTrace_4353498
  have hstable : (prefixWord ++ tailWord_4353498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4353498).length < 2 ^ (prefixWord ++ tailWord_4353498).sum := by decide
  have hdescent : baseEnd_4353498 < baseStart_4353498 := by decide
  rcases family_descends (prefixWord ++ tailWord_4353498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4353551 : List Nat := [1, 1, 2, 1, 1, 1, 2, 2, 2, 5, 5]
def baseStart_4353551 : Nat := 118140960795 + 4353551 * 2 ^ 59
def prefixEnd_4353551 : Nat := 4983230072969 + 3 ^ 40 * 4353551 * 2
def baseEnd_4353551 : Nat := 2235464216862201445390889

theorem tailTrace_4353551 : CollatzResearch.WordTrace tailWord_4353551 prefixEnd_4353551 2235464216862201445390889 := by
  unfold tailWord_4353551
  simp only [CollatzResearch.WordTrace]
  refine ⟨158787049850835729160676507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105858033233890486107117671 158787049850835729160676507)
  ·
    refine ⟨238180574776253593741014761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158787049850835729160676507 238180574776253593741014761)
    ·
      refine ⟨178635431082190195305761071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 238180574776253593741014761 178635431082190195305761071)
      ·
        refine ⟨267953146623285292958641607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 178635431082190195305761071 267953146623285292958641607)
        ·
          refine ⟨401929719934927939437962411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 267953146623285292958641607 401929719934927939437962411)
          ·
            refine ⟨602894579902391909156943617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 401929719934927939437962411 602894579902391909156943617)
            ·
              refine ⟨452170934926793931867707713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 602894579902391909156943617 452170934926793931867707713)
              ·
                refine ⟨339128201195095448900780785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 452170934926793931867707713 339128201195095448900780785)
                ·
                  refine ⟨254346150896321586675585589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 339128201195095448900780785 254346150896321586675585589)
                  ·
                    refine ⟨23844951646530148750836149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 254346150896321586675585589 23844951646530148750836149)
                    ·
                      refine ⟨2235464216862201445390889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23844951646530148750836149 2235464216862201445390889)
                      ·
                        rfl

theorem cell23_4353551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 2, 2, 5, 5].length) (baseStart_4353551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4353551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4353551 prefixEnd_4353551 := by exact prefixLift 4353551
  have htrace : WordTrace (prefixWord ++ tailWord_4353551) baseStart_4353551 baseEnd_4353551 := by
    simpa [prefixWord, tailWord_4353551, baseEnd_4353551] using wordTrace_append hprefix tailTrace_4353551
  have hstable : (prefixWord ++ tailWord_4353551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4353551).length < 2 ^ (prefixWord ++ tailWord_4353551).sum := by decide
  have hdescent : baseEnd_4353551 < baseStart_4353551 := by decide
  rcases family_descends (prefixWord ++ tailWord_4353551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4353565 : List Nat := [1, 4, 2, 2, 1, 1, 1, 1, 2, 6, 2]
def baseStart_4353565 : Nat := 118140960795 + 4353565 * 2 ^ 59
def prefixEnd_4353565 : Nat := 4983230072969 + 3 ^ 40 * 4353565 * 2
def baseEnd_4353565 : Nat := 2235471405591364390615825

theorem tailTrace_4353565 : CollatzResearch.WordTrace tailWord_4353565 prefixEnd_4353565 2235471405591364390615825 := by
  unfold tailWord_4353565
  simp only [CollatzResearch.WordTrace]
  refine ⟨158787560472785009551686149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105858373648523339701124099 158787560472785009551686149)
  ·
    refine ⟨29772667588647189290941153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 158787560472785009551686149 29772667588647189290941153)
    ·
      refine ⟨22329500691485391968205865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29772667588647189290941153 22329500691485391968205865)
      ·
        refine ⟨16747125518614043976154399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22329500691485391968205865 16747125518614043976154399)
        ·
          refine ⟨25120688277921065964231599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16747125518614043976154399 25120688277921065964231599)
          ·
            refine ⟨37681032416881598946347399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25120688277921065964231599 37681032416881598946347399)
            ·
              refine ⟨56521548625322398419521099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37681032416881598946347399 56521548625322398419521099)
              ·
                refine ⟨84782322937983597629281649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56521548625322398419521099 84782322937983597629281649)
                ·
                  refine ⟨63586742203487698221961237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 84782322937983597629281649 63586742203487698221961237)
                  ·
                    refine ⟨2980628540788485854154433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 63586742203487698221961237 2980628540788485854154433)
                    ·
                      refine ⟨2235471405591364390615825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2980628540788485854154433 2235471405591364390615825)
                      ·
                        rfl

theorem cell23_4353565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 1, 2, 6, 2].length) (baseStart_4353565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4353565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4353565 prefixEnd_4353565 := by exact prefixLift 4353565
  have htrace : WordTrace (prefixWord ++ tailWord_4353565) baseStart_4353565 baseEnd_4353565 := by
    simpa [prefixWord, tailWord_4353565, baseEnd_4353565] using wordTrace_append hprefix tailTrace_4353565
  have hstable : (prefixWord ++ tailWord_4353565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4353565).length < 2 ^ (prefixWord ++ tailWord_4353565).sum := by decide
  have hdescent : baseEnd_4353565 < baseStart_4353565 := by decide
  rcases family_descends (prefixWord ++ tailWord_4353565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4353582 : List Nat := [4, 1, 3, 1, 2, 1, 2, 3, 1, 1, 4]
def baseStart_4353582 : Nat := 118140960795 + 4353582 * 2 ^ 59
def prefixEnd_4353582 : Nat := 4983230072969 + 3 ^ 40 * 4353582 * 2
def baseEnd_4353582 : Nat := 2235480134762490824103247

theorem tailTrace_4353582 : CollatzResearch.WordTrace tailWord_4353582 prefixEnd_4353582 2235480134762490824103247 := by
  unfold tailWord_4353582
  simp only [CollatzResearch.WordTrace]
  refine ⟨19848522564215427681881875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 105858787009148947636703333 19848522564215427681881875)
  ·
    refine ⟨29772783846323141522822813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19848522564215427681881875 29772783846323141522822813)
    ·
      refine ⟨11164793942371178071058555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29772783846323141522822813 11164793942371178071058555)
      ·
        refine ⟨16747190913556767106587833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11164793942371178071058555 16747190913556767106587833)
        ·
          refine ⟨12560393185167575329940875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16747190913556767106587833 12560393185167575329940875)
          ·
            refine ⟨18840589777751362994911313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12560393185167575329940875 18840589777751362994911313)
            ·
              refine ⟨14130442333313522246183485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18840589777751362994911313 14130442333313522246183485)
              ·
                refine ⟨5298915874992570842318807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14130442333313522246183485 5298915874992570842318807)
                ·
                  refine ⟨7948373812488856263478211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5298915874992570842318807 7948373812488856263478211)
                  ·
                    refine ⟨11922560718733284395217317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7948373812488856263478211 11922560718733284395217317)
                    ·
                      refine ⟨2235480134762490824103247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11922560718733284395217317 2235480134762490824103247)
                      ·
                        rfl

theorem cell23_4353582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 2, 3, 1, 1, 4].length) (baseStart_4353582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4353582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4353582 prefixEnd_4353582 := by exact prefixLift 4353582
  have htrace : WordTrace (prefixWord ++ tailWord_4353582) baseStart_4353582 baseEnd_4353582 := by
    simpa [prefixWord, tailWord_4353582, baseEnd_4353582] using wordTrace_append hprefix tailTrace_4353582
  have hstable : (prefixWord ++ tailWord_4353582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4353582).length < 2 ^ (prefixWord ++ tailWord_4353582).sum := by decide
  have hdescent : baseEnd_4353582 < baseStart_4353582 := by decide
  rcases family_descends (prefixWord ++ tailWord_4353582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4353599 : List Nat := [1, 1, 2, 2, 3, 5, 1, 1, 3, 2, 2]
def baseStart_4353599 : Nat := 118140960795 + 4353599 * 2 ^ 59
def prefixEnd_4353599 : Nat := 4983230072969 + 3 ^ 40 * 4353599 * 2
def baseEnd_4353599 : Nat := 2235488863933617257590669

theorem tailTrace_4353599 : CollatzResearch.WordTrace tailWord_4353599 prefixEnd_4353599 2235488863933617257590669 := by
  unfold tailWord_4353599
  simp only [CollatzResearch.WordTrace]
  refine ⟨158788800554661833358423851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105859200369774555572282567 158788800554661833358423851)
  ·
    refine ⟨238183200831992750037635777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158788800554661833358423851 238183200831992750037635777)
    ·
      refine ⟨178637400623994562528226833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 238183200831992750037635777 178637400623994562528226833)
      ·
        refine ⟨133978050467995921896170125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 178637400623994562528226833 133978050467995921896170125)
        ·
          refine ⟨50241768925498470711063797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 133978050467995921896170125 50241768925498470711063797)
          ·
            refine ⟨4710165836765481629162231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 50241768925498470711063797 4710165836765481629162231)
            ·
              refine ⟨7065248755148222443743347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4710165836765481629162231 7065248755148222443743347)
              ·
                refine ⟨10597873132722333665615021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7065248755148222443743347 10597873132722333665615021)
                ·
                  refine ⟨3974202424770875124605633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10597873132722333665615021 3974202424770875124605633)
                  ·
                    refine ⟨2980651818578156343454225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3974202424770875124605633 2980651818578156343454225)
                    ·
                      refine ⟨2235488863933617257590669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2980651818578156343454225 2235488863933617257590669)
                      ·
                        rfl

theorem cell23_4353599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 5, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 5, 1, 1, 3, 2, 2].length) (baseStart_4353599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4353599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4353599 prefixEnd_4353599 := by exact prefixLift 4353599
  have htrace : WordTrace (prefixWord ++ tailWord_4353599) baseStart_4353599 baseEnd_4353599 := by
    simpa [prefixWord, tailWord_4353599, baseEnd_4353599] using wordTrace_append hprefix tailTrace_4353599
  have hstable : (prefixWord ++ tailWord_4353599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4353599).length < 2 ^ (prefixWord ++ tailWord_4353599).sum := by decide
  have hdescent : baseEnd_4353599 < baseStart_4353599 := by decide
  rcases family_descends (prefixWord ++ tailWord_4353599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4353629 : List Nat := [1, 4, 4, 2, 1, 1, 1, 2, 1, 2, 4]
def baseStart_4353629 : Nat := 118140960795 + 4353629 * 2 ^ 59
def prefixEnd_4353629 : Nat := 4983230072969 + 3 ^ 40 * 4353629 * 2
def baseEnd_4353629 : Nat := 2235504268353252140215531

theorem tailTrace_4353629 : CollatzResearch.WordTrace tailWord_4353629 prefixEnd_4353629 2235504268353252140215531 := by
  unfold tailWord_4353629
  simp only [CollatzResearch.WordTrace]
  refine ⟨158789894744553148482015941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105859929829702098988010627 158789894744553148482015941)
  ·
    refine ⟨29773105264603715340377989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 158789894744553148482015941 29773105264603715340377989)
    ·
      refine ⟨5582457237113196626320873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29773105264603715340377989 5582457237113196626320873)
      ·
        refine ⟨4186842927834897469740655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5582457237113196626320873 4186842927834897469740655)
        ·
          refine ⟨6280264391752346204610983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4186842927834897469740655 6280264391752346204610983)
          ·
            refine ⟨9420396587628519306916475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6280264391752346204610983 9420396587628519306916475)
            ·
              refine ⟨14130594881442778960374713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9420396587628519306916475 14130594881442778960374713)
              ·
                refine ⟨10597946161082084220281035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14130594881442778960374713 10597946161082084220281035)
                ·
                  refine ⟨15896919241623126330421553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10597946161082084220281035 15896919241623126330421553)
                  ·
                    refine ⟨11922689431217344747816165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15896919241623126330421553 11922689431217344747816165)
                    ·
                      refine ⟨2235504268353252140215531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11922689431217344747816165 2235504268353252140215531)
                      ·
                        rfl

theorem cell23_4353629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 1, 2, 1, 2, 4].length) (baseStart_4353629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4353629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4353629 prefixEnd_4353629 := by exact prefixLift 4353629
  have htrace : WordTrace (prefixWord ++ tailWord_4353629) baseStart_4353629 baseEnd_4353629 := by
    simpa [prefixWord, tailWord_4353629, baseEnd_4353629] using wordTrace_append hprefix tailTrace_4353629
  have hstable : (prefixWord ++ tailWord_4353629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4353629).length < 2 ^ (prefixWord ++ tailWord_4353629).sum := by decide
  have hdescent : baseEnd_4353629 < baseStart_4353629 := by decide
  rcases family_descends (prefixWord ++ tailWord_4353629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4353655 : List Nat := [1, 1, 3, 1, 1, 3, 1, 1, 5, 4, 2]
def baseStart_4353655 : Nat := 118140960795 + 4353655 * 2 ^ 59
def prefixEnd_4353655 : Nat := 4983230072969 + 3 ^ 40 * 4353655 * 2
def baseEnd_4353655 : Nat := 2235517618850269038490411

theorem tailTrace_4353655 : CollatzResearch.WordTrace tailWord_4353655 prefixEnd_4353655 2235517618850269038490411 := by
  unfold tailWord_4353655
  simp only [CollatzResearch.WordTrace]
  refine ⟨158790843042458954922462419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105860562028305969948308279 158790843042458954922462419)
  ·
    refine ⟨238186264563688432383693629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158790843042458954922462419 238186264563688432383693629)
    ·
      refine ⟨89319849211383162143885111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 238186264563688432383693629 89319849211383162143885111)
      ·
        refine ⟨133979773817074743215827667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89319849211383162143885111 133979773817074743215827667)
        ·
          refine ⟨200969660725612114823741501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 133979773817074743215827667 200969660725612114823741501)
          ·
            refine ⟨75363622772104543058903063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 200969660725612114823741501 75363622772104543058903063)
            ·
              refine ⟨113045434158156814588354595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75363622772104543058903063 113045434158156814588354595)
              ·
                refine ⟨169568151237235221882531893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 113045434158156814588354595 169568151237235221882531893)
                ·
                  refine ⟨15897014178490802051487365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 169568151237235221882531893 15897014178490802051487365)
                  ·
                    refine ⟨2980690158467025384653881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15897014178490802051487365 2980690158467025384653881)
                    ·
                      refine ⟨2235517618850269038490411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2980690158467025384653881 2235517618850269038490411)
                      ·
                        rfl

theorem cell23_4353655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 1, 5, 4, 2].length) (baseStart_4353655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4353655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4353655 prefixEnd_4353655 := by exact prefixLift 4353655
  have htrace : WordTrace (prefixWord ++ tailWord_4353655) baseStart_4353655 baseEnd_4353655 := by
    simpa [prefixWord, tailWord_4353655, baseEnd_4353655] using wordTrace_append hprefix tailTrace_4353655
  have hstable : (prefixWord ++ tailWord_4353655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4353655).length < 2 ^ (prefixWord ++ tailWord_4353655).sum := by decide
  have hdescent : baseEnd_4353655 < baseStart_4353655 := by decide
  rcases family_descends (prefixWord ++ tailWord_4353655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4353658 : List Nat := [3, 1, 1, 1, 1, 1, 1, 4, 4, 1, 5]
def baseStart_4353658 : Nat := 118140960795 + 4353658 * 2 ^ 59
def prefixEnd_4353658 : Nat := 4983230072969 + 3 ^ 40 * 4353658 * 2
def baseEnd_4353658 : Nat := 2235519159292232526752897

theorem tailTrace_4353658 : CollatzResearch.WordTrace tailWord_4353658 prefixEnd_4353658 2235519159292232526752897 := by
  unfold tailWord_4353658
  simp only [CollatzResearch.WordTrace]
  refine ⟨39697738115362021608705407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105860634974298724289881085 39697738115362021608705407)
  ·
    refine ⟨59546607173043032413058111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39697738115362021608705407 59546607173043032413058111)
    ·
      refine ⟨89319910759564548619587167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59546607173043032413058111 89319910759564548619587167)
      ·
        refine ⟨133979866139346822929380751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89319910759564548619587167 133979866139346822929380751)
        ·
          refine ⟨200969799209020234394071127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 133979866139346822929380751 200969799209020234394071127)
          ·
            refine ⟨301454698813530351591106691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 200969799209020234394071127 301454698813530351591106691)
            ·
              refine ⟨452182048220295527386660037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 301454698813530351591106691 452182048220295527386660037)
              ·
                refine ⟨84784134041305411384998757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 452182048220295527386660037 84784134041305411384998757)
                ·
                  refine ⟨15897025132744764634687267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 84784134041305411384998757 15897025132744764634687267)
                  ·
                    refine ⟨23845537699117146952030901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15897025132744764634687267 23845537699117146952030901)
                    ·
                      refine ⟨2235519159292232526752897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23845537699117146952030901 2235519159292232526752897)
                      ·
                        rfl

theorem cell23_4353658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 4, 4, 1, 5].length) (baseStart_4353658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4353658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4353658 prefixEnd_4353658 := by exact prefixLift 4353658
  have htrace : WordTrace (prefixWord ++ tailWord_4353658) baseStart_4353658 baseEnd_4353658 := by
    simpa [prefixWord, tailWord_4353658, baseEnd_4353658] using wordTrace_append hprefix tailTrace_4353658
  have hstable : (prefixWord ++ tailWord_4353658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4353658).length < 2 ^ (prefixWord ++ tailWord_4353658).sum := by decide
  have hdescent : baseEnd_4353658 < baseStart_4353658 := by decide
  rcases family_descends (prefixWord ++ tailWord_4353658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4353665 : List Nat := [1, 2, 4, 2, 1, 3, 1, 1, 2, 6]
def baseStart_4353665 : Nat := 118140960795 + 4353665 * 2 ^ 59
def prefixEnd_4353665 : Nat := 4983230072969 + 3 ^ 40 * 4353665 * 2
def baseEnd_4353665 : Nat := 745174251218937999788455

theorem tailTrace_4353665 : CollatzResearch.WordTrace tailWord_4353665 prefixEnd_4353665 745174251218937999788455 := by
  unfold tailWord_4353665
  simp only [CollatzResearch.WordTrace]
  refine ⟨158791207772422726630326449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105860805181615151086884299 158791207772422726630326449)
  ·
    refine ⟨119093405829317044972744837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 158791207772422726630326449 119093405829317044972744837)
    ·
      refine ⟨22330013592996945932389657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 119093405829317044972744837 22330013592996945932389657)
      ·
        refine ⟨16747510194747709449292243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22330013592996945932389657 16747510194747709449292243)
        ·
          refine ⟨25121265292121564173938365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16747510194747709449292243 25121265292121564173938365)
          ·
            refine ⟨9420474484545586565226887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25121265292121564173938365 9420474484545586565226887)
            ·
              refine ⟨14130711726818379847840331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9420474484545586565226887 14130711726818379847840331)
              ·
                refine ⟨21196067590227569771760497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14130711726818379847840331 21196067590227569771760497)
                ·
                  refine ⟨15897050692670677328820373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21196067590227569771760497 15897050692670677328820373)
                  ·
                    refine ⟨745174251218937999788455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15897050692670677328820373 745174251218937999788455)
                    ·
                      rfl

theorem cell23_4353665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 1, 1, 2, 6].length) (baseStart_4353665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4353665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4353665 prefixEnd_4353665 := by exact prefixLift 4353665
  have htrace : WordTrace (prefixWord ++ tailWord_4353665) baseStart_4353665 baseEnd_4353665 := by
    simpa [prefixWord, tailWord_4353665, baseEnd_4353665] using wordTrace_append hprefix tailTrace_4353665
  have hstable : (prefixWord ++ tailWord_4353665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4353665).length < 2 ^ (prefixWord ++ tailWord_4353665).sum := by decide
  have hdescent : baseEnd_4353665 < baseStart_4353665 := by decide
  rcases family_descends (prefixWord ++ tailWord_4353665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4353745 : List Nat := [1, 2, 2, 1, 2, 4, 2, 1, 1, 3, 4]
def baseStart_4353745 : Nat := 118140960795 + 4353745 * 2 ^ 59
def prefixEnd_4353745 : Nat := 4983230072969 + 3 ^ 40 * 4353745 * 2
def baseEnd_4353745 : Nat := 2235563832109173686364997

theorem tailTrace_4353745 : CollatzResearch.WordTrace tailWord_4353745 prefixEnd_4353745 2235563832109173686364997 := by
  unfold tailWord_4353745
  simp only [CollatzResearch.WordTrace]
  refine ⟨158794125612132900293238689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105862750408088600195492459 158794125612132900293238689)
  ·
    refine ⟨119095594209099675219929017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 158794125612132900293238689 119095594209099675219929017)
    ·
      refine ⟨89321695656824756414946763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119095594209099675219929017 89321695656824756414946763)
      ·
        refine ⟨133982543485237134622420145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89321695656824756414946763 133982543485237134622420145)
        ·
          refine ⟨100486907613927850966815109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 133982543485237134622420145 100486907613927850966815109)
          ·
            refine ⟨18841295177611472056277833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 100486907613927850966815109 18841295177611472056277833)
            ·
              refine ⟨14130971383208604042208375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18841295177611472056277833 14130971383208604042208375)
              ·
                refine ⟨21196457074812906063312563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14130971383208604042208375 21196457074812906063312563)
                ·
                  refine ⟨31794685612219359094968845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21196457074812906063312563 31794685612219359094968845)
                  ·
                    refine ⟨11923007104582259660613317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 31794685612219359094968845 11923007104582259660613317)
                    ·
                      refine ⟨2235563832109173686364997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11923007104582259660613317 2235563832109173686364997)
                      ·
                        rfl

theorem cell23_4353745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 2, 1, 1, 3, 4].length) (baseStart_4353745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4353745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4353745 prefixEnd_4353745 := by exact prefixLift 4353745
  have htrace : WordTrace (prefixWord ++ tailWord_4353745) baseStart_4353745 baseEnd_4353745 := by
    simpa [prefixWord, tailWord_4353745, baseEnd_4353745] using wordTrace_append hprefix tailTrace_4353745
  have hstable : (prefixWord ++ tailWord_4353745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4353745).length < 2 ^ (prefixWord ++ tailWord_4353745).sum := by decide
  have hdescent : baseEnd_4353745 < baseStart_4353745 := by decide
  rcases family_descends (prefixWord ++ tailWord_4353745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4353772 : List Nat := [2, 2, 1, 1, 2, 2, 5, 1, 3, 4]
def baseStart_4353772 : Nat := 118140960795 + 4353772 * 2 ^ 59
def prefixEnd_4353772 : Nat := 4983230072969 + 3 ^ 40 * 4353772 * 2
def baseEnd_4353772 : Nat := 745192565362281693575791

theorem tailTrace_4353772 : CollatzResearch.WordTrace tailWord_4353772 prefixEnd_4353772 745192565362281693575791 := by
  unfold tailWord_4353772
  simp only [CollatzResearch.WordTrace]
  refine ⟨79397555191517541952235785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105863406922023389269647713 79397555191517541952235785)
  ·
    refine ⟨59548166393638156464176839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79397555191517541952235785 59548166393638156464176839)
    ·
      refine ⟨89322249590457234696265259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59548166393638156464176839 89322249590457234696265259)
      ·
        refine ⟨133983374385685852044397889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89322249590457234696265259 133983374385685852044397889)
        ·
          refine ⟨100487530789264389033298417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 133983374385685852044397889 100487530789264389033298417)
          ·
            refine ⟨75365648091948291774973813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 100487530789264389033298417 75365648091948291774973813)
            ·
              refine ⟨7065529508620152353903795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 75365648091948291774973813 7065529508620152353903795)
              ·
                refine ⟨10598294262930228530855693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7065529508620152353903795 10598294262930228530855693)
                ·
                  refine ⟨3974360348598835699070885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10598294262930228530855693 3974360348598835699070885)
                  ·
                    refine ⟨745192565362281693575791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3974360348598835699070885 745192565362281693575791)
                    ·
                      rfl

theorem cell23_4353772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 4].length) (baseStart_4353772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4353772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4353772 prefixEnd_4353772 := by exact prefixLift 4353772
  have htrace : WordTrace (prefixWord ++ tailWord_4353772) baseStart_4353772 baseEnd_4353772 := by
    simpa [prefixWord, tailWord_4353772, baseEnd_4353772] using wordTrace_append hprefix tailTrace_4353772
  have hstable : (prefixWord ++ tailWord_4353772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4353772).length < 2 ^ (prefixWord ++ tailWord_4353772).sum := by decide
  have hdescent : baseEnd_4353772 < baseStart_4353772 := by decide
  rcases family_descends (prefixWord ++ tailWord_4353772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4353795 : List Nat := [1, 1, 1, 3, 2, 2, 2, 1, 2, 5, 3]
def baseStart_4353795 : Nat := 118140960795 + 4353795 * 2 ^ 59
def prefixEnd_4353795 : Nat := 4983230072969 + 3 ^ 40 * 4353795 * 2
def baseEnd_4353795 : Nat := 2235589506141898490739767

theorem tailTrace_4353795 : CollatzResearch.WordTrace tailWord_4353795 prefixEnd_4353795 2235589506141898490739767 := by
  unfold tailWord_4353795
  simp only [CollatzResearch.WordTrace]
  refine ⟨158795949261951758832558839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105863966174634505888372559 158795949261951758832558839)
  ·
    refine ⟨238193923892927638248838259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158795949261951758832558839 238193923892927638248838259)
    ·
      refine ⟨357290885839391457373257389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 238193923892927638248838259 357290885839391457373257389)
      ·
        refine ⟨133984082189771796514971521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 357290885839391457373257389 133984082189771796514971521)
        ·
          refine ⟨100488061642328847386228641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 133984082189771796514971521 100488061642328847386228641)
          ·
            refine ⟨75366046231746635539671481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 100488061642328847386228641 75366046231746635539671481)
            ·
              refine ⟨56524534673809976654753611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75366046231746635539671481 56524534673809976654753611)
              ·
                refine ⟨84786802010714964982130417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56524534673809976654753611 84786802010714964982130417)
                ·
                  refine ⟨63590101508036223736597813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 84786802010714964982130417 63590101508036223736597813)
                  ·
                    refine ⟨5961572016378395975306045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 63590101508036223736597813 5961572016378395975306045)
                    ·
                      refine ⟨2235589506141898490739767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5961572016378395975306045 2235589506141898490739767)
                      ·
                        rfl

theorem cell23_4353795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 1, 2, 5, 3].length) (baseStart_4353795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4353795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4353795 prefixEnd_4353795 := by exact prefixLift 4353795
  have htrace : WordTrace (prefixWord ++ tailWord_4353795) baseStart_4353795 baseEnd_4353795 := by
    simpa [prefixWord, tailWord_4353795, baseEnd_4353795] using wordTrace_append hprefix tailTrace_4353795
  have hstable : (prefixWord ++ tailWord_4353795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4353795).length < 2 ^ (prefixWord ++ tailWord_4353795).sum := by decide
  have hdescent : baseEnd_4353795 < baseStart_4353795 := by decide
  rcases family_descends (prefixWord ++ tailWord_4353795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4353832 : List Nat := [2, 1, 5, 1, 1, 2, 1, 2, 3, 5]
def baseStart_4353832 : Nat := 118140960795 + 4353832 * 2 ^ 59
def prefixEnd_4353832 : Nat := 4983230072969 + 3 ^ 40 * 4353832 * 2
def baseEnd_4353832 : Nat := 745202834975371615325699

theorem tailTrace_4353832 : CollatzResearch.WordTrace tailWord_4353832 prefixEnd_4353832 745202834975371615325699 := by
  unfold tailWord_4353832
  simp only [CollatzResearch.WordTrace]
  refine ⟨79398649381408857075827875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105864865841878476101103833 79398649381408857075827875)
  ·
    refine ⟨119097974072113285613741813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79398649381408857075827875 119097974072113285613741813)
    ·
      refine ⟨11165435069260620526288295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 119097974072113285613741813 11165435069260620526288295)
      ·
        refine ⟨16748152603890930789432443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11165435069260620526288295 16748152603890930789432443)
        ·
          refine ⟨25122228905836396184148665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16748152603890930789432443 25122228905836396184148665)
          ·
            refine ⟨18841671679377297138111499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25122228905836396184148665 18841671679377297138111499)
            ·
              refine ⟨28262507519065945707167249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18841671679377297138111499 28262507519065945707167249)
              ·
                refine ⟨21196880639299459280375437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28262507519065945707167249 21196880639299459280375437)
                ·
                  refine ⟨7948830239737297230140789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21196880639299459280375437 7948830239737297230140789)
                  ·
                    refine ⟨745202834975371615325699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7948830239737297230140789 745202834975371615325699)
                    ·
                      rfl

theorem cell23_4353832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 2, 3, 5].length) (baseStart_4353832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4353832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4353832 prefixEnd_4353832 := by exact prefixLift 4353832
  have htrace : WordTrace (prefixWord ++ tailWord_4353832) baseStart_4353832 baseEnd_4353832 := by
    simpa [prefixWord, tailWord_4353832, baseEnd_4353832] using wordTrace_append hprefix tailTrace_4353832
  have hstable : (prefixWord ++ tailWord_4353832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4353832).length < 2 ^ (prefixWord ++ tailWord_4353832).sum := by decide
  have hdescent : baseEnd_4353832 < baseStart_4353832 := by decide
  rcases family_descends (prefixWord ++ tailWord_4353832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4353846 : List Nat := [5, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3]
def baseStart_4353846 : Nat := 118140960795 + 4353846 * 2 ^ 59
def prefixEnd_4353846 : Nat := 4983230072969 + 3 ^ 40 * 4353846 * 2
def baseEnd_4353846 : Nat := 2235615693655277791202033

theorem tailTrace_4353846 : CollatzResearch.WordTrace tailWord_4353846 prefixEnd_4353846 2235615693655277791202033 := by
  unfold tailWord_4353846
  simp only [CollatzResearch.WordTrace]
  refine ⟨9924863086547937158916587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 105865206256511329695110261 9924863086547937158916587)
  ·
    refine ⟨14887294629821905738374881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9924863086547937158916587 14887294629821905738374881)
    ·
      refine ⟨11165470972366429303781161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14887294629821905738374881 11165470972366429303781161)
      ·
        refine ⟨8374103229274821977835871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11165470972366429303781161 8374103229274821977835871)
        ·
          refine ⟨12561154843912232966753807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8374103229274821977835871 12561154843912232966753807)
          ·
            refine ⟨18841732265868349450130711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12561154843912232966753807 18841732265868349450130711)
            ·
              refine ⟨28262598398802524175196067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18841732265868349450130711 28262598398802524175196067)
              ·
                refine ⟨42393897598203786262794101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28262598398802524175196067 42393897598203786262794101)
                ·
                  refine ⟨3974427899831604962136947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 42393897598203786262794101 3974427899831604962136947)
                  ·
                    refine ⟨5961641849747407443205421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3974427899831604962136947 5961641849747407443205421)
                    ·
                      refine ⟨2235615693655277791202033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5961641849747407443205421 2235615693655277791202033)
                      ·
                        rfl

theorem cell23_4353846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3].length) (baseStart_4353846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4353846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4353846 prefixEnd_4353846 := by exact prefixLift 4353846
  have htrace : WordTrace (prefixWord ++ tailWord_4353846) baseStart_4353846 baseEnd_4353846 := by
    simpa [prefixWord, tailWord_4353846, baseEnd_4353846] using wordTrace_append hprefix tailTrace_4353846
  have hstable : (prefixWord ++ tailWord_4353846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4353846).length < 2 ^ (prefixWord ++ tailWord_4353846).sum := by decide
  have hdescent : baseEnd_4353846 < baseStart_4353846 := by decide
  rcases family_descends (prefixWord ++ tailWord_4353846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4353852 : List Nat := [2, 2, 2, 2, 1, 1, 4, 1, 3, 1, 4]
def baseStart_4353852 : Nat := 118140960795 + 4353852 * 2 ^ 59
def prefixEnd_4353852 : Nat := 4983230072969 + 3 ^ 40 * 4353852 * 2
def baseEnd_4353852 : Nat := 2235618774539204767727005

theorem tailTrace_4353852 : CollatzResearch.WordTrace tailWord_4353852 prefixEnd_4353852 2235618774539204767727005 := by
  unfold tailWord_4353852
  simp only [CollatzResearch.WordTrace]
  refine ⟨79399014111372628783691905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105865352148496838378255873 79399014111372628783691905)
  ·
    refine ⟨59549260583529471587768929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79399014111372628783691905 59549260583529471587768929)
    ·
      refine ⟨44661945437647103690826697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59549260583529471587768929 44661945437647103690826697)
      ·
        refine ⟨33496459078235327768120023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44661945437647103690826697 33496459078235327768120023)
        ·
          refine ⟨50244688617352991652180035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33496459078235327768120023 50244688617352991652180035)
          ·
            refine ⟨75367032926029487478270053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50244688617352991652180035 75367032926029487478270053)
            ·
              refine ⟨14131318673630528902175635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 75367032926029487478270053 14131318673630528902175635)
              ·
                refine ⟨21196978010445793353263453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14131318673630528902175635 21196978010445793353263453)
                ·
                  refine ⟨7948866753917172507473795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21196978010445793353263453 7948866753917172507473795)
                  ·
                    refine ⟨11923300130875758761210693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7948866753917172507473795 11923300130875758761210693)
                    ·
                      refine ⟨2235618774539204767727005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11923300130875758761210693 2235618774539204767727005)
                      ·
                        rfl

theorem cell23_4353852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 4, 1, 3, 1, 4].length) (baseStart_4353852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4353852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4353852 prefixEnd_4353852 := by exact prefixLift 4353852
  have htrace : WordTrace (prefixWord ++ tailWord_4353852) baseStart_4353852 baseEnd_4353852 := by
    simpa [prefixWord, tailWord_4353852, baseEnd_4353852] using wordTrace_append hprefix tailTrace_4353852
  have hstable : (prefixWord ++ tailWord_4353852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4353852).length < 2 ^ (prefixWord ++ tailWord_4353852).sum := by decide
  have hdescent : baseEnd_4353852 < baseStart_4353852 := by decide
  rcases family_descends (prefixWord ++ tailWord_4353852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4353879 : List Nat := [1, 1, 3, 2, 5, 1, 1, 1, 4, 4]
def baseStart_4353879 : Nat := 118140960795 + 4353879 * 2 ^ 59
def prefixEnd_4353879 : Nat := 4983230072969 + 3 ^ 40 * 4353879 * 2
def baseEnd_4353879 : Nat := 745210879505625387363127

theorem tailTrace_4353879 : CollatzResearch.WordTrace tailWord_4353879 prefixEnd_4353879 745210879505625387363127 := by
  unfold tailWord_4353879
  simp only [CollatzResearch.WordTrace]
  refine ⟨158799012993647441178616691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105866008662431627452411127 158799012993647441178616691)
  ·
    refine ⟨238198519490471161767925037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158799012993647441178616691 238198519490471161767925037)
    ·
      refine ⟨89324444808926685662971889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 238198519490471161767925037 89324444808926685662971889)
      ·
        refine ⟨66993333606695014247228917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89324444808926685662971889 66993333606695014247228917)
        ·
          refine ⟨6280625025627657585677711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 66993333606695014247228917 6280625025627657585677711)
          ·
            refine ⟨9420937538441486378516567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6280625025627657585677711 9420937538441486378516567)
            ·
              refine ⟨14131406307662229567774851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9420937538441486378516567 14131406307662229567774851)
              ·
                refine ⟨21197109461493344351662277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14131406307662229567774851 21197109461493344351662277)
                ·
                  refine ⟨3974458024030002065936677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21197109461493344351662277 3974458024030002065936677)
                  ·
                    refine ⟨745210879505625387363127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3974458024030002065936677 745210879505625387363127)
                    ·
                      rfl

theorem cell23_4353879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 1, 1, 4, 4].length) (baseStart_4353879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4353879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4353879 prefixEnd_4353879 := by exact prefixLift 4353879
  have htrace : WordTrace (prefixWord ++ tailWord_4353879) baseStart_4353879 baseEnd_4353879 := by
    simpa [prefixWord, tailWord_4353879, baseEnd_4353879] using wordTrace_append hprefix tailTrace_4353879
  have hstable : (prefixWord ++ tailWord_4353879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4353879).length < 2 ^ (prefixWord ++ tailWord_4353879).sum := by decide
  have hdescent : baseEnd_4353879 < baseStart_4353879 := by decide
  rcases family_descends (prefixWord ++ tailWord_4353879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4353896 : List Nat := [2, 1, 4, 2, 1, 1, 5, 1, 2, 4]
def baseStart_4353896 : Nat := 118140960795 + 4353896 * 2 ^ 59
def prefixEnd_4353896 : Nat := 4983230072969 + 3 ^ 40 * 4353896 * 2
def baseEnd_4353896 : Nat := 745213789229334198525601

theorem tailTrace_4353896 : CollatzResearch.WordTrace tailWord_4353896 prefixEnd_4353896 745213789229334198525601 := by
  unfold tailWord_4353896
  simp only [CollatzResearch.WordTrace]
  refine ⟨79399816517292926540992771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105866422023057235387990361 79399816517292926540992771)
  ·
    refine ⟨119099724775939389811489157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79399816517292926540992771 119099724775939389811489157)
    ·
      refine ⟨22331198395488635589654217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 119099724775939389811489157 22331198395488635589654217)
      ·
        refine ⟨16748398796616476692240663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22331198395488635589654217 16748398796616476692240663)
        ·
          refine ⟨25122598194924715038360995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16748398796616476692240663 25122598194924715038360995)
          ·
            refine ⟨37683897292387072557541493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25122598194924715038360995 37683897292387072557541493)
            ·
              refine ⟨3532865371161288052269515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 37683897292387072557541493 3532865371161288052269515)
              ·
                refine ⟨5299298056741932078404273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3532865371161288052269515 5299298056741932078404273)
                ·
                  refine ⟨3974473542556449058803205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5299298056741932078404273 3974473542556449058803205)
                  ·
                    refine ⟨745213789229334198525601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3974473542556449058803205 745213789229334198525601)
                    ·
                      rfl

theorem cell23_4353896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 5, 1, 2, 4].length) (baseStart_4353896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4353896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4353896 prefixEnd_4353896 := by exact prefixLift 4353896
  have htrace : WordTrace (prefixWord ++ tailWord_4353896) baseStart_4353896 baseEnd_4353896 := by
    simpa [prefixWord, tailWord_4353896, baseEnd_4353896] using wordTrace_append hprefix tailTrace_4353896
  have hstable : (prefixWord ++ tailWord_4353896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4353896).length < 2 ^ (prefixWord ++ tailWord_4353896).sum := by decide
  have hdescent : baseEnd_4353896 < baseStart_4353896 := by decide
  rcases family_descends (prefixWord ++ tailWord_4353896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4353953 : List Nat := [1, 2, 3, 4, 2, 1, 1, 3, 2, 1, 3]
def baseStart_4353953 : Nat := 118140960795 + 4353953 * 2 ^ 59
def prefixEnd_4353953 : Nat := 4983230072969 + 3 ^ 40 * 4353953 * 2
def baseEnd_4353953 : Nat := 2235670636085308872564041

theorem tailTrace_4353953 : CollatzResearch.WordTrace tailWord_4353953 prefixEnd_4353953 2235670636085308872564041 := by
  unfold tailWord_4353953
  simp only [CollatzResearch.WordTrace]
  refine ⟨158801711995379351816810513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105867807996919567877873675 158801711995379351816810513)
  ·
    refine ⟨119101283996534513862607885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 158801711995379351816810513 119101283996534513862607885)
    ·
      refine ⟨44662981498700442698477957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 119101283996534513862607885 44662981498700442698477957)
      ·
        refine ⟨8374309031006333005964617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 44662981498700442698477957 8374309031006333005964617)
        ·
          refine ⟨6280731773254749754473463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8374309031006333005964617 6280731773254749754473463)
          ·
            refine ⟨9421097659882124631710195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6280731773254749754473463 9421097659882124631710195)
            ·
              refine ⟨14131646489823186947565293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9421097659882124631710195 14131646489823186947565293)
              ·
                refine ⟨5299367433683695105336985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14131646489823186947565293 5299367433683695105336985)
                ·
                  refine ⟨3974525575262771329002739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5299367433683695105336985 3974525575262771329002739)
                  ·
                    refine ⟨5961788362894156993504109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3974525575262771329002739 5961788362894156993504109)
                    ·
                      refine ⟨2235670636085308872564041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5961788362894156993504109 2235670636085308872564041)
                      ·
                        rfl

theorem cell23_4353953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 1, 3, 2, 1, 3].length) (baseStart_4353953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4353953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4353953 prefixEnd_4353953 := by exact prefixLift 4353953
  have htrace : WordTrace (prefixWord ++ tailWord_4353953) baseStart_4353953 baseEnd_4353953 := by
    simpa [prefixWord, tailWord_4353953, baseEnd_4353953] using wordTrace_append hprefix tailTrace_4353953
  have hstable : (prefixWord ++ tailWord_4353953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4353953).length < 2 ^ (prefixWord ++ tailWord_4353953).sum := by decide
  have hdescent : baseEnd_4353953 < baseStart_4353953 := by decide
  rcases family_descends (prefixWord ++ tailWord_4353953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4353999 : List Nat := [1, 1, 2, 1, 1, 5, 3, 4, 5]
def baseStart_4353999 : Nat := 118140960795 + 4353999 * 2 ^ 59
def prefixEnd_4353999 : Nat := 4983230072969 + 3 ^ 40 * 4353999 * 2
def baseEnd_4353999 : Nat := 248410472910601743620981

theorem tailTrace_4353999 : CollatzResearch.WordTrace tailWord_4353999 prefixEnd_4353999 248410472910601743620981 := by
  unfold tailWord_4353999
  simp only [CollatzResearch.WordTrace]
  refine ⟨158803389753212701672985051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105868926502141801115323367 158803389753212701672985051)
  ·
    refine ⟨238205084629819052509477577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158803389753212701672985051 238205084629819052509477577)
    ·
      refine ⟨178653813472364289382108183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 238205084629819052509477577 178653813472364289382108183)
      ·
        refine ⟨267980720208546434073162275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 178653813472364289382108183 267980720208546434073162275)
        ·
          refine ⟨401971080312819651109743413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 267980720208546434073162275 401971080312819651109743413)
          ·
            refine ⟨37684788779326842291538445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 401971080312819651109743413 37684788779326842291538445)
            ·
              refine ⟨14131795792247565859326917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37684788779326842291538445 14131795792247565859326917)
              ·
                refine ⟨2649711711046418598623797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14131795792247565859326917 2649711711046418598623797)
                ·
                  refine ⟨248410472910601743620981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2649711711046418598623797 248410472910601743620981)
                  ·
                    rfl

theorem cell23_4353999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 3, 4, 5].length) (baseStart_4353999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4353999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4353999 prefixEnd_4353999 := by exact prefixLift 4353999
  have htrace : WordTrace (prefixWord ++ tailWord_4353999) baseStart_4353999 baseEnd_4353999 := by
    simpa [prefixWord, tailWord_4353999, baseEnd_4353999] using wordTrace_append hprefix tailTrace_4353999
  have hstable : (prefixWord ++ tailWord_4353999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4353999).length < 2 ^ (prefixWord ++ tailWord_4353999).sum := by decide
  have hdescent : baseEnd_4353999 < baseStart_4353999 := by decide
  rcases family_descends (prefixWord ++ tailWord_4353999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4354049 : List Nat := [1, 2, 4, 1, 2, 1, 2, 1, 4, 1, 4]
def baseStart_4354049 : Nat := 118140960795 + 4354049 * 2 ^ 59
def prefixEnd_4354049 : Nat := 4983230072969 + 3 ^ 40 * 4354049 * 2
def baseEnd_4354049 : Nat := 2235719930228140496963599

theorem tailTrace_4354049 : CollatzResearch.WordTrace tailWord_4354049 prefixEnd_4354049 2235719930228140496963599 := by
  unfold tailWord_4354049
  simp only [CollatzResearch.WordTrace]
  refine ⟨158805213403031560212305201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105870142268687706808203467 158805213403031560212305201)
  ·
    refine ⟨119103910052273670159228901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 158805213403031560212305201 119103910052273670159228901)
    ·
      refine ⟨22331983134801313154855419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 119103910052273670159228901 22331983134801313154855419)
      ·
        refine ⟨33497974702201969732283129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22331983134801313154855419 33497974702201969732283129)
        ·
          refine ⟨25123481026651477299212347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33497974702201969732283129 25123481026651477299212347)
          ·
            refine ⟨37685221539977215948818521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25123481026651477299212347 37685221539977215948818521)
            ·
              refine ⟨28263916154982911961613891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37685221539977215948818521 28263916154982911961613891)
              ·
                refine ⟨42395874232474367942420837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28263916154982911961613891 42395874232474367942420837)
                ·
                  refine ⟨7949226418588943989203907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 42395874232474367942420837 7949226418588943989203907)
                  ·
                    refine ⟨11923839627883415983805861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7949226418588943989203907 11923839627883415983805861)
                    ·
                      refine ⟨2235719930228140496963599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11923839627883415983805861 2235719930228140496963599)
                      ·
                        rfl

theorem cell23_4354049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 1, 4, 1, 4].length) (baseStart_4354049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4354049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4354049 prefixEnd_4354049 := by exact prefixLift 4354049
  have htrace : WordTrace (prefixWord ++ tailWord_4354049) baseStart_4354049 baseEnd_4354049 := by
    simpa [prefixWord, tailWord_4354049, baseEnd_4354049] using wordTrace_append hprefix tailTrace_4354049
  have hstable : (prefixWord ++ tailWord_4354049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4354049).length < 2 ^ (prefixWord ++ tailWord_4354049).sum := by decide
  have hdescent : baseEnd_4354049 < baseStart_4354049 := by decide
  rcases family_descends (prefixWord ++ tailWord_4354049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4354061 : List Nat := [1, 7, 1, 2, 1, 1, 3, 1, 2, 2, 2]
def baseStart_4354061 : Nat := 118140960795 + 4354061 * 2 ^ 59
def prefixEnd_4354061 : Nat := 4983230072969 + 3 ^ 40 * 4354061 * 2
def baseEnd_4354061 : Nat := 2235726091995994450013545

theorem tailTrace_4354061 : CollatzResearch.WordTrace tailWord_4354061 prefixEnd_4354061 2235726091995994450013545 := by
  unfold tailWord_4354061
  simp only [CollatzResearch.WordTrace]
  refine ⟨158805651078988086261742037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105870434052658724174494691 158805651078988086261742037)
  ·
    refine ⟨3722007447163783271759579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 158805651078988086261742037 3722007447163783271759579)
    ·
      refine ⟨5583011170745674907639369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3722007447163783271759579 5583011170745674907639369)
      ·
        refine ⟨4187258378059256180729527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5583011170745674907639369 4187258378059256180729527)
        ·
          refine ⟨6280887567088884271094291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4187258378059256180729527 6280887567088884271094291)
          ·
            refine ⟨9421331350633326406641437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6280887567088884271094291 9421331350633326406641437)
            ·
              refine ⟨3532999256487497402490539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9421331350633326406641437 3532999256487497402490539)
              ·
                refine ⟨5299498884731246103735809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3532999256487497402490539 5299498884731246103735809)
                ·
                  refine ⟨3974624163548434577801857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5299498884731246103735809 3974624163548434577801857)
                  ·
                    refine ⟨2980968122661325933351393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3974624163548434577801857 2980968122661325933351393)
                    ·
                      refine ⟨2235726091995994450013545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2980968122661325933351393 2235726091995994450013545)
                      ·
                        rfl

theorem cell23_4354061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 3, 1, 2, 2, 2].length) (baseStart_4354061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4354061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4354061 prefixEnd_4354061 := by exact prefixLift 4354061
  have htrace : WordTrace (prefixWord ++ tailWord_4354061) baseStart_4354061 baseEnd_4354061 := by
    simpa [prefixWord, tailWord_4354061, baseEnd_4354061] using wordTrace_append hprefix tailTrace_4354061
  have hstable : (prefixWord ++ tailWord_4354061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4354061).length < 2 ^ (prefixWord ++ tailWord_4354061).sum := by decide
  have hdescent : baseEnd_4354061 < baseStart_4354061 := by decide
  rcases family_descends (prefixWord ++ tailWord_4354061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4354076 : List Nat := [2, 2, 3, 1, 3, 1, 2, 2, 3, 4]
def baseStart_4354076 : Nat := 118140960795 + 4354076 * 2 ^ 59
def prefixEnd_4354076 : Nat := 4983230072969 + 3 ^ 40 * 4354076 * 2
def baseEnd_4354076 : Nat := 745244598068603963775325

theorem tailTrace_4354076 : CollatzResearch.WordTrace tailWord_4354076 prefixEnd_4354076 745244598068603963775325 := by
  unfold tailWord_4354076
  simp only [CollatzResearch.WordTrace]
  refine ⟨79403099086966871911769041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105870798782622495882358721 79403099086966871911769041)
  ·
    refine ⟨59552324315225153933826781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79403099086966871911769041 59552324315225153933826781)
    ·
      refine ⟨22332121618209432725185043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59552324315225153933826781 22332121618209432725185043)
      ·
        refine ⟨33498182427314149087777565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22332121618209432725185043 33498182427314149087777565)
        ·
          refine ⟨12561818410242805907916587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33498182427314149087777565 12561818410242805907916587)
          ·
            refine ⟨18842727615364208861874881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12561818410242805907916587 18842727615364208861874881)
            ·
              refine ⟨14132045711523156646406161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18842727615364208861874881 14132045711523156646406161)
              ·
                refine ⟨10599034283642367484804621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14132045711523156646406161 10599034283642367484804621)
                ·
                  refine ⟨3974637856365887806801733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10599034283642367484804621 3974637856365887806801733)
                  ·
                    refine ⟨745244598068603963775325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3974637856365887806801733 745244598068603963775325)
                    ·
                      rfl

theorem cell23_4354076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 2, 2, 3, 4].length) (baseStart_4354076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4354076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4354076 prefixEnd_4354076 := by exact prefixLift 4354076
  have htrace : WordTrace (prefixWord ++ tailWord_4354076) baseStart_4354076 baseEnd_4354076 := by
    simpa [prefixWord, tailWord_4354076, baseEnd_4354076] using wordTrace_append hprefix tailTrace_4354076
  have hstable : (prefixWord ++ tailWord_4354076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4354076).length < 2 ^ (prefixWord ++ tailWord_4354076).sum := by decide
  have hdescent : baseEnd_4354076 < baseStart_4354076 := by decide
  rcases family_descends (prefixWord ++ tailWord_4354076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4354092 : List Nat := [2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 8]
def baseStart_4354092 : Nat := 118140960795 + 4354092 * 2 ^ 59
def prefixEnd_4354092 : Nat := 4983230072969 + 3 ^ 40 * 4354092 * 2
def baseEnd_4354092 : Nat := 2235742009896283828725901

theorem tailTrace_4354092 : CollatzResearch.WordTrace tailWord_4354092 prefixEnd_4354092 2235742009896283828725901 := by
  unfold tailWord_4354092
  simp only [CollatzResearch.WordTrace]
  refine ⟨79403390870937889278060265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105871187827917185704080353 79403390870937889278060265)
  ·
    refine ⟨59552543153203416958545199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79403390870937889278060265 59552543153203416958545199)
    ·
      refine ⟨89328814729805125437817799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59552543153203416958545199 89328814729805125437817799)
      ·
        refine ⟨133993222094707688156726699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89328814729805125437817799 133993222094707688156726699)
        ·
          refine ⟨200989833142061532235090049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 133993222094707688156726699 200989833142061532235090049)
          ·
            refine ⟨150742374856546149176317537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 200989833142061532235090049 150742374856546149176317537)
            ·
              refine ⟨113056781142409611882238153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 150742374856546149176317537 113056781142409611882238153)
              ·
                refine ⟨84792585856807208911678615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 113056781142409611882238153 84792585856807208911678615)
                ·
                  refine ⟨127188878785210813367517923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 84792585856807208911678615 127188878785210813367517923)
                  ·
                    refine ⟨190783318177816220051276885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 127188878785210813367517923 190783318177816220051276885)
                    ·
                      refine ⟨2235742009896283828725901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 190783318177816220051276885 2235742009896283828725901)
                      ·
                        rfl

theorem cell23_4354092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 8].length) (baseStart_4354092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4354092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4354092 prefixEnd_4354092 := by exact prefixLift 4354092
  have htrace : WordTrace (prefixWord ++ tailWord_4354092) baseStart_4354092 baseEnd_4354092 := by
    simpa [prefixWord, tailWord_4354092, baseEnd_4354092] using wordTrace_append hprefix tailTrace_4354092
  have hstable : (prefixWord ++ tailWord_4354092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4354092).length < 2 ^ (prefixWord ++ tailWord_4354092).sum := by decide
  have hdescent : baseEnd_4354092 < baseStart_4354092 := by decide
  rcases family_descends (prefixWord ++ tailWord_4354092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4354110 : List Nat := [4, 2, 1, 3, 2, 2, 1, 1, 3, 4]
def baseStart_4354110 : Nat := 118140960795 + 4354110 * 2 ^ 59
def prefixEnd_4354110 : Nat := 4983230072969 + 3 ^ 40 * 4354110 * 2
def baseEnd_4354110 : Nat := 745250417516021586100273

theorem tailTrace_4354110 : CollatzResearch.WordTrace tailWord_4354110 prefixEnd_4354110 745250417516021586100273 := by
  unfold tailWord_4354110
  simp only [CollatzResearch.WordTrace]
  refine ⟨19850929781976320953784473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 105871625503873711753517189 19850929781976320953784473)
  ·
    refine ⟨14888197336482240715338355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19850929781976320953784473 14888197336482240715338355)
    ·
      refine ⟨22332296004723361073007533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14888197336482240715338355 22332296004723361073007533)
      ·
        refine ⟨8374611001771260402377825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22332296004723361073007533 8374611001771260402377825)
        ·
          refine ⟨6280958251328445301783369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8374611001771260402377825 6280958251328445301783369)
          ·
            refine ⟨4710718688496333976337527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6280958251328445301783369 4710718688496333976337527)
            ·
              refine ⟨7066078032744500964506291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4710718688496333976337527 7066078032744500964506291)
              ·
                refine ⟨10599117049116751446759437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7066078032744500964506291 10599117049116751446759437)
                ·
                  refine ⟨3974668893418781792534789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10599117049116751446759437 3974668893418781792534789)
                  ·
                    refine ⟨745250417516021586100273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3974668893418781792534789 745250417516021586100273)
                    ·
                      rfl

theorem cell23_4354110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 2, 1, 1, 3, 4].length) (baseStart_4354110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4354110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4354110 prefixEnd_4354110 := by exact prefixLift 4354110
  have htrace : WordTrace (prefixWord ++ tailWord_4354110) baseStart_4354110 baseEnd_4354110 := by
    simpa [prefixWord, tailWord_4354110, baseEnd_4354110] using wordTrace_append hprefix tailTrace_4354110
  have hstable : (prefixWord ++ tailWord_4354110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4354110).length < 2 ^ (prefixWord ++ tailWord_4354110).sum := by decide
  have hdescent : baseEnd_4354110 < baseStart_4354110 := by decide
  rcases family_descends (prefixWord ++ tailWord_4354110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4354119 : List Nat := [1, 1, 4, 1, 3, 1, 2, 2, 3, 5]
def baseStart_4354119 : Nat := 118140960795 + 4354119 * 2 ^ 59
def prefixEnd_4354119 : Nat := 4983230072969 + 3 ^ 40 * 4354119 * 2
def baseEnd_4354119 : Nat := 745251957957985074362759

theorem tailTrace_4354119 : CollatzResearch.WordTrace tailWord_4354119 prefixEnd_4354119 745251957957985074362759 := by
  unfold tailWord_4354119
  simp only [CollatzResearch.WordTrace]
  refine ⟨158807766512777962167353411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105871844341851974778235607 158807766512777962167353411)
  ·
    refine ⟨238211649769166943251030117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158807766512777962167353411 238211649769166943251030117)
    ·
      refine ⟨44664684331718801859568147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 238211649769166943251030117 44664684331718801859568147)
      ·
        refine ⟨66997026497578202789352221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44664684331718801859568147 66997026497578202789352221)
        ·
          refine ⟨25123884936591826046007083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66997026497578202789352221 25123884936591826046007083)
          ·
            refine ⟨37685827404887739069010625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25123884936591826046007083 37685827404887739069010625)
            ·
              refine ⟨28264370553665804301757969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37685827404887739069010625 28264370553665804301757969)
              ·
                refine ⟨21198277915249353226318477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28264370553665804301757969 21198277915249353226318477)
                ·
                  refine ⟨7949354218218507459869429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21198277915249353226318477 7949354218218507459869429)
                  ·
                    refine ⟨745251957957985074362759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7949354218218507459869429 745251957957985074362759)
                    ·
                      rfl

theorem cell23_4354119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 2, 3, 5].length) (baseStart_4354119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4354119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4354119 prefixEnd_4354119 := by exact prefixLift 4354119
  have htrace : WordTrace (prefixWord ++ tailWord_4354119) baseStart_4354119 baseEnd_4354119 := by
    simpa [prefixWord, tailWord_4354119, baseEnd_4354119] using wordTrace_append hprefix tailTrace_4354119
  have hstable : (prefixWord ++ tailWord_4354119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4354119).length < 2 ^ (prefixWord ++ tailWord_4354119).sum := by decide
  have hdescent : baseEnd_4354119 < baseStart_4354119 := by decide
  rcases family_descends (prefixWord ++ tailWord_4354119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4354136 : List Nat := [2, 1, 2, 2, 1, 4, 3, 2, 1, 5]
def baseStart_4354136 : Nat := 118140960795 + 4354136 * 2 ^ 59
def prefixEnd_4354136 : Nat := 4983230072969 + 3 ^ 40 * 4354136 * 2
def baseEnd_4354136 : Nat := 745254867681693885525233

theorem tailTrace_4354136 : CollatzResearch.WordTrace tailWord_4354136 prefixEnd_4354136 745254867681693885525233 := by
  unfold tailWord_4354136
  simp only [CollatzResearch.WordTrace]
  refine ⟨79404193276858187035361131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105872257702477582713814841 79404193276858187035361131)
  ·
    refine ⟨119106289915287280553041697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79404193276858187035361131 119106289915287280553041697)
    ·
      refine ⟨89329717436465460414781273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119106289915287280553041697 89329717436465460414781273)
      ·
        refine ⟨66997288077349095311085955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89329717436465460414781273 66997288077349095311085955)
        ·
          refine ⟨100495932116023642966628933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66997288077349095311085955 100495932116023642966628933)
          ·
            refine ⟨18842987271754433056242925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 100495932116023642966628933 18842987271754433056242925)
            ·
              refine ⟨7066120226907912396091097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18842987271754433056242925 7066120226907912396091097)
              ·
                refine ⟨5299590170180934297068323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7066120226907912396091097 5299590170180934297068323)
                ·
                  refine ⟨7949385255271401445602485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5299590170180934297068323 7949385255271401445602485)
                  ·
                    refine ⟨745254867681693885525233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7949385255271401445602485 745254867681693885525233)
                    ·
                      rfl

theorem cell23_4354136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 3, 2, 1, 5].length) (baseStart_4354136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4354136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4354136 prefixEnd_4354136 := by exact prefixLift 4354136
  have htrace : WordTrace (prefixWord ++ tailWord_4354136) baseStart_4354136 baseEnd_4354136 := by
    simpa [prefixWord, tailWord_4354136, baseEnd_4354136] using wordTrace_append hprefix tailTrace_4354136
  have hstable : (prefixWord ++ tailWord_4354136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4354136).length < 2 ^ (prefixWord ++ tailWord_4354136).sum := by decide
  have hdescent : baseEnd_4354136 < baseStart_4354136 := by decide
  rcases family_descends (prefixWord ++ tailWord_4354136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4354149 : List Nat := [1, 3, 1, 3, 2, 2, 1, 1, 3, 6]
def baseStart_4354149 : Nat := 118140960795 + 4354149 * 2 ^ 59
def prefixEnd_4354149 : Nat := 4983230072969 + 3 ^ 40 * 4354149 * 2
def baseEnd_4354149 : Nat := 745257092764530035237713

theorem tailTrace_4354149 : CollatzResearch.WordTrace tailWord_4354149 prefixEnd_4354149 745257092764530035237713 := by
  unfold tailWord_4354149
  simp only [CollatzResearch.WordTrace]
  refine ⟨158808860702669277290945501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105872573801779518193963667 158808860702669277290945501)
  ·
    refine ⟨59553322763500978984104563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 158808860702669277290945501 59553322763500978984104563)
    ·
      refine ⟨89329984145251468476156845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59553322763500978984104563 89329984145251468476156845)
      ·
        refine ⟨33498744054469300678558817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 89329984145251468476156845 33498744054469300678558817)
        ·
          refine ⟨25124058040851975508919113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33498744054469300678558817 25124058040851975508919113)
          ·
            refine ⟨18843043530638981631689335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25124058040851975508919113 18843043530638981631689335)
            ·
              refine ⟨28264565295958472447534003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18843043530638981631689335 28264565295958472447534003)
              ·
                refine ⟨42396847943937708671301005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28264565295958472447534003 42396847943937708671301005)
                ·
                  refine ⟨15898817978976640751737877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 42396847943937708671301005 15898817978976640751737877)
                  ·
                    refine ⟨745257092764530035237713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15898817978976640751737877 745257092764530035237713)
                    ·
                      rfl

theorem cell23_4354149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 1, 3, 6].length) (baseStart_4354149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4354149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4354149 prefixEnd_4354149 := by exact prefixLift 4354149
  have htrace : WordTrace (prefixWord ++ tailWord_4354149) baseStart_4354149 baseEnd_4354149 := by
    simpa [prefixWord, tailWord_4354149, baseEnd_4354149] using wordTrace_append hprefix tailTrace_4354149
  have hstable : (prefixWord ++ tailWord_4354149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4354149).length < 2 ^ (prefixWord ++ tailWord_4354149).sum := by decide
  have hdescent : baseEnd_4354149 < baseStart_4354149 := by decide
  rcases family_descends (prefixWord ++ tailWord_4354149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4354167 : List Nat := [1, 1, 3, 1, 1, 7, 2, 2, 1, 1, 3]
def baseStart_4354167 : Nat := 118140960795 + 4354167 * 2 ^ 59
def prefixEnd_4354167 : Nat := 4983230072969 + 3 ^ 40 * 4354167 * 2
def baseEnd_4354167 : Nat := 2235780520945371035288057

theorem tailTrace_4354167 : CollatzResearch.WordTrace tailWord_4354167 prefixEnd_4354167 2235780520945371035288057 := by
  unfold tailWord_4354167
  simp only [CollatzResearch.WordTrace]
  refine ⟨158809517216604066365100755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105873011477736044243400503 158809517216604066365100755)
  ·
    refine ⟨238214275824906099547651133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158809517216604066365100755 238214275824906099547651133)
    ·
      refine ⟨89330353434339787330369175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 238214275824906099547651133 89330353434339787330369175)
      ·
        refine ⟨133995530151509680995553763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89330353434339787330369175 133995530151509680995553763)
        ·
          refine ⟨200993295227264521493330645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 133995530151509680995553763 200993295227264521493330645)
          ·
            refine ⟨4710780356889012222499937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 200993295227264521493330645 4710780356889012222499937)
            ·
              refine ⟨3533085267666759166874953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4710780356889012222499937 3533085267666759166874953)
              ·
                refine ⟨2649813950750069375156215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3533085267666759166874953 2649813950750069375156215)
                ·
                  refine ⟨3974720926125104062734323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2649813950750069375156215 3974720926125104062734323)
                  ·
                    refine ⟨5962081389187656094101485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3974720926125104062734323 5962081389187656094101485)
                    ·
                      refine ⟨2235780520945371035288057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5962081389187656094101485 2235780520945371035288057)
                      ·
                        rfl

theorem cell23_4354167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 7, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 7, 2, 2, 1, 1, 3].length) (baseStart_4354167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4354167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4354167 prefixEnd_4354167 := by exact prefixLift 4354167
  have htrace : WordTrace (prefixWord ++ tailWord_4354167) baseStart_4354167 baseEnd_4354167 := by
    simpa [prefixWord, tailWord_4354167, baseEnd_4354167] using wordTrace_append hprefix tailTrace_4354167
  have hstable : (prefixWord ++ tailWord_4354167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4354167).length < 2 ^ (prefixWord ++ tailWord_4354167).sum := by decide
  have hdescent : baseEnd_4354167 < baseStart_4354167 := by decide
  rcases family_descends (prefixWord ++ tailWord_4354167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4354179 : List Nat := [1, 1, 1, 3, 3, 3, 3, 8]
def baseStart_4354179 : Nat := 118140960795 + 4354179 * 2 ^ 59
def prefixEnd_4354179 : Nat := 4983230072969 + 3 ^ 40 * 4354179 * 2
def baseEnd_4354179 : Nat := 82806914174563888456963

theorem tailTrace_4354179 : CollatzResearch.WordTrace tailWord_4354179 prefixEnd_4354179 82806914174563888456963 := by
  unfold tailWord_4354179
  simp only [CollatzResearch.WordTrace]
  refine ⟨158809954892560592414537591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105873303261707061609691727 158809954892560592414537591)
  ·
    refine ⟨238214932338840888621806387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158809954892560592414537591 238214932338840888621806387)
    ·
      refine ⟨357322398508261332932709581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 238214932338840888621806387 357322398508261332932709581)
      ·
        refine ⟨133995899440597999849766093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 357322398508261332932709581 133995899440597999849766093)
        ·
          refine ⟨50248462290224249943662285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 133995899440597999849766093 50248462290224249943662285)
          ·
            refine ⟨18843173358834093728873357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50248462290224249943662285 18843173358834093728873357)
            ·
              refine ⟨7066190009562785148327509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18843173358834093728873357 7066190009562785148327509)
              ·
                refine ⟨82806914174563888456963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7066190009562785148327509 82806914174563888456963)
                ·
                  rfl

theorem cell23_4354179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 3, 8].length) (baseStart_4354179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4354179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4354179 prefixEnd_4354179 := by exact prefixLift 4354179
  have htrace : WordTrace (prefixWord ++ tailWord_4354179) baseStart_4354179 baseEnd_4354179 := by
    simpa [prefixWord, tailWord_4354179, baseEnd_4354179] using wordTrace_append hprefix tailTrace_4354179
  have hstable : (prefixWord ++ tailWord_4354179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4354179).length < 2 ^ (prefixWord ++ tailWord_4354179).sum := by decide
  have hdescent : baseEnd_4354179 < baseStart_4354179 := by decide
  rcases family_descends (prefixWord ++ tailWord_4354179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4354186 : List Nat := [3, 1, 2, 3, 1, 2, 1, 3, 1, 2, 4]
def baseStart_4354186 : Nat := 118140960795 + 4354186 * 2 ^ 59
def prefixEnd_4354186 : Nat := 4983230072969 + 3 ^ 40 * 4354186 * 2
def baseEnd_4354186 : Nat := 2235790277077806460950469

theorem tailTrace_4354186 : CollatzResearch.WordTrace tailWord_4354186 prefixEnd_4354186 2235790277077806460950469 := by
  unfold tailWord_4354186
  simp only [CollatzResearch.WordTrace]
  refine ⟨39702552550883808152510603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105873473469023488406694941 39702552550883808152510603)
  ·
    refine ⟨59553828826325712228765905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39702552550883808152510603 59553828826325712228765905)
    ·
      refine ⟨44665371619744284171574429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59553828826325712228765905 44665371619744284171574429)
      ·
        refine ⟨16749514357404106564340411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44665371619744284171574429 16749514357404106564340411)
        ·
          refine ⟨25124271536106159846510617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16749514357404106564340411 25124271536106159846510617)
          ·
            refine ⟨18843203652079619884882963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25124271536106159846510617 18843203652079619884882963)
            ·
              refine ⟨28264805478119429827324445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18843203652079619884882963 28264805478119429827324445)
              ·
                refine ⟨10599302054294786185246667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28264805478119429827324445 10599302054294786185246667)
                ·
                  refine ⟨15898953081442179277870001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10599302054294786185246667 15898953081442179277870001)
                  ·
                    refine ⟨11924214811081634458402501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15898953081442179277870001 11924214811081634458402501)
                    ·
                      refine ⟨2235790277077806460950469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11924214811081634458402501 2235790277077806460950469)
                      ·
                        rfl

theorem cell23_4354186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 3, 1, 2, 4].length) (baseStart_4354186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4354186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4354186 prefixEnd_4354186 := by exact prefixLift 4354186
  have htrace : WordTrace (prefixWord ++ tailWord_4354186) baseStart_4354186 baseEnd_4354186 := by
    simpa [prefixWord, tailWord_4354186, baseEnd_4354186] using wordTrace_append hprefix tailTrace_4354186
  have hstable : (prefixWord ++ tailWord_4354186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4354186).length < 2 ^ (prefixWord ++ tailWord_4354186).sum := by decide
  have hdescent : baseEnd_4354186 < baseStart_4354186 := by decide
  rcases family_descends (prefixWord ++ tailWord_4354186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4354207 : List Nat := [1, 1, 2, 6, 1, 1, 1, 5, 1, 2, 2]
def baseStart_4354207 : Nat := 118140960795 + 4354207 * 2 ^ 59
def prefixEnd_4354207 : Nat := 4983230072969 + 3 ^ 40 * 4354207 * 2
def baseEnd_4354207 : Nat := 2235801060171550878787873

theorem tailTrace_4354207 : CollatzResearch.WordTrace tailWord_4354207 prefixEnd_4354207 2235801060171550878787873 := by
  unfold tailWord_4354207
  simp only [CollatzResearch.WordTrace]
  refine ⟨158810976136459153196556875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105873984090972768797704583 158810976136459153196556875)
  ·
    refine ⟨238216464204688729794835313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158810976136459153196556875 238216464204688729794835313)
    ·
      refine ⟨178662348153516547346126485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 238216464204688729794835313 178662348153516547346126485)
      ·
        refine ⟨8374797569696088156849679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 178662348153516547346126485 8374797569696088156849679)
        ·
          refine ⟨12562196354544132235274519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8374797569696088156849679 12562196354544132235274519)
          ·
            refine ⟨18843294531816198352911779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12562196354544132235274519 18843294531816198352911779)
            ·
              refine ⟨28264941797724297529367669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18843294531816198352911779 28264941797724297529367669)
              ·
                refine ⟨2649838293536652893378219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28264941797724297529367669 2649838293536652893378219)
                ·
                  refine ⟨3974757440304979340067329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2649838293536652893378219 3974757440304979340067329)
                  ·
                    refine ⟨2981068080228734505050497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3974757440304979340067329 2981068080228734505050497)
                    ·
                      refine ⟨2235801060171550878787873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2981068080228734505050497 2235801060171550878787873)
                      ·
                        rfl

theorem cell23_4354207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 5, 1, 2, 2].length) (baseStart_4354207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4354207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4354207 prefixEnd_4354207 := by exact prefixLift 4354207
  have htrace : WordTrace (prefixWord ++ tailWord_4354207) baseStart_4354207 baseEnd_4354207 := by
    simpa [prefixWord, tailWord_4354207, baseEnd_4354207] using wordTrace_append hprefix tailTrace_4354207
  have hstable : (prefixWord ++ tailWord_4354207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4354207).length < 2 ^ (prefixWord ++ tailWord_4354207).sum := by decide
  have hdescent : baseEnd_4354207 < baseStart_4354207 := by decide
  rcases family_descends (prefixWord ++ tailWord_4354207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4354210 : List Nat := [3, 3, 1, 3, 1, 2, 1, 3, 1, 2, 3]
def baseStart_4354210 : Nat := 118140960795 + 4354210 * 2 ^ 59
def prefixEnd_4354210 : Nat := 4983230072969 + 3 ^ 40 * 4354210 * 2
def baseEnd_4354210 : Nat := 2235802600613514367050359

theorem tailTrace_4354210 : CollatzResearch.WordTrace tailWord_4354210 prefixEnd_4354210 2235802600613514367050359 := by
  unfold tailWord_4354210
  simp only [CollatzResearch.WordTrace]
  refine ⟨39702771388862071177229021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105874057036965523139277389 39702771388862071177229021)
  ·
    refine ⟨14888539270823276691460883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39702771388862071177229021 14888539270823276691460883)
    ·
      refine ⟨22332808906234915037191325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14888539270823276691460883 22332808906234915037191325)
      ·
        refine ⟨8374803339838093138946747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22332808906234915037191325 8374803339838093138946747)
        ·
          refine ⟨12562205009757139708420121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8374803339838093138946747 12562205009757139708420121)
          ·
            refine ⟨9421653757317854781315091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12562205009757139708420121 9421653757317854781315091)
            ·
              refine ⟨14132480635976782171972637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9421653757317854781315091 14132480635976782171972637)
              ·
                refine ⟨5299680238491293314489739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14132480635976782171972637 5299680238491293314489739)
                ·
                  refine ⟨7949520357736939971734609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5299680238491293314489739 7949520357736939971734609)
                  ·
                    refine ⟨5962140268302704978800957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7949520357736939971734609 5962140268302704978800957)
                    ·
                      refine ⟨2235802600613514367050359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5962140268302704978800957 2235802600613514367050359)
                      ·
                        rfl

theorem cell23_4354210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 1, 3, 1, 2, 3].length) (baseStart_4354210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4354210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4354210 prefixEnd_4354210 := by exact prefixLift 4354210
  have htrace : WordTrace (prefixWord ++ tailWord_4354210) baseStart_4354210 baseEnd_4354210 := by
    simpa [prefixWord, tailWord_4354210, baseEnd_4354210] using wordTrace_append hprefix tailTrace_4354210
  have hstable : (prefixWord ++ tailWord_4354210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4354210).length < 2 ^ (prefixWord ++ tailWord_4354210).sum := by decide
  have hdescent : baseEnd_4354210 < baseStart_4354210 := by decide
  rcases family_descends (prefixWord ++ tailWord_4354210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4354250 : List Nat := [3, 1, 2, 1, 3, 1, 4, 2, 1, 3, 2]
def baseStart_4354250 : Nat := 118140960795 + 4354250 * 2 ^ 59
def prefixEnd_4354250 : Nat := 4983230072969 + 3 ^ 40 * 4354250 * 2
def baseEnd_4354250 : Nat := 2235823139839694210550175

theorem tailTrace_4354250 : CollatzResearch.WordTrace tailWord_4354250 prefixEnd_4354250 2235823139839694210550175 := by
  unfold tailWord_4354250
  simp only [CollatzResearch.WordTrace]
  refine ⟨39703136118825842885093051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105875029650202247693581469 39703136118825842885093051)
  ·
    refine ⟨59554704178238764327639577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39703136118825842885093051 59554704178238764327639577)
    ·
      refine ⟨44666028133679073245729683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59554704178238764327639577 44666028133679073245729683)
      ·
        refine ⟨66999042200518609868594525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44666028133679073245729683 66999042200518609868594525)
        ·
          refine ⟨25124640825194478700722947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66999042200518609868594525 25124640825194478700722947)
          ·
            refine ⟨37686961237791718051084421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25124640825194478700722947 37686961237791718051084421)
            ·
              refine ⟨7066305232085947134578329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37686961237791718051084421 7066305232085947134578329)
              ·
                refine ⟨5299728924064460350933747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7066305232085947134578329 5299728924064460350933747)
                ·
                  refine ⟨7949593386096690526400621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5299728924064460350933747 7949593386096690526400621)
                  ·
                    refine ⟨2981097519786258947400233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7949593386096690526400621 2981097519786258947400233)
                    ·
                      refine ⟨2235823139839694210550175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2981097519786258947400233 2235823139839694210550175)
                      ·
                        rfl

theorem cell23_4354250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 4, 2, 1, 3, 2].length) (baseStart_4354250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4354250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4354250 prefixEnd_4354250 := by exact prefixLift 4354250
  have htrace : WordTrace (prefixWord ++ tailWord_4354250) baseStart_4354250 baseEnd_4354250 := by
    simpa [prefixWord, tailWord_4354250, baseEnd_4354250] using wordTrace_append hprefix tailTrace_4354250
  have hstable : (prefixWord ++ tailWord_4354250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4354250).length < 2 ^ (prefixWord ++ tailWord_4354250).sum := by decide
  have hdescent : baseEnd_4354250 < baseStart_4354250 := by decide
  rcases family_descends (prefixWord ++ tailWord_4354250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4354280 : List Nat := [2, 1, 4, 1, 2, 2, 2, 1, 4, 2, 2]
def baseStart_4354280 : Nat := 118140960795 + 4354280 * 2 ^ 59
def prefixEnd_4354280 : Nat := 4983230072969 + 3 ^ 40 * 4354280 * 2
def baseEnd_4354280 : Nat := 2235838544259329093175037

theorem tailTrace_4354280 : CollatzResearch.WordTrace tailWord_4354280 prefixEnd_4354280 2235838544259329093175037 := by
  unfold tailWord_4354280
  simp only [CollatzResearch.WordTrace]
  refine ⟨79406819332597343331982147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105875759110129791109309529 79406819332597343331982147)
  ·
    refine ⟨119110228998896014997973221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79406819332597343331982147 119110228998896014997973221)
    ·
      refine ⟨22333167937293002812119979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 119110228998896014997973221 22333167937293002812119979)
      ·
        refine ⟨33499751905939504218179969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22333167937293002812119979 33499751905939504218179969)
        ·
          refine ⟨25124813929454628163634977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33499751905939504218179969 25124813929454628163634977)
          ·
            refine ⟨18843610447090971122726233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25124813929454628163634977 18843610447090971122726233)
            ·
              refine ⟨14132707835318228342044675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18843610447090971122726233 14132707835318228342044675)
              ·
                refine ⟨21199061752977342513067013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14132707835318228342044675 21199061752977342513067013)
                ·
                  refine ⟨3974824078683251721200065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21199061752977342513067013 3974824078683251721200065)
                  ·
                    refine ⟨2981118059012438790900049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3974824078683251721200065 2981118059012438790900049)
                    ·
                      refine ⟨2235838544259329093175037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2981118059012438790900049 2235838544259329093175037)
                      ·
                        rfl

theorem cell23_4354280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 2, 1, 4, 2, 2].length) (baseStart_4354280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4354280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4354280 prefixEnd_4354280 := by exact prefixLift 4354280
  have htrace : WordTrace (prefixWord ++ tailWord_4354280) baseStart_4354280 baseEnd_4354280 := by
    simpa [prefixWord, tailWord_4354280, baseEnd_4354280] using wordTrace_append hprefix tailTrace_4354280
  have hstable : (prefixWord ++ tailWord_4354280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4354280).length < 2 ^ (prefixWord ++ tailWord_4354280).sum := by decide
  have hdescent : baseEnd_4354280 < baseStart_4354280 := by decide
  rcases family_descends (prefixWord ++ tailWord_4354280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4354296 : List Nat := [2, 1, 2, 1, 1, 2, 1, 5, 2, 3, 3]
def baseStart_4354296 : Nat := 118140960795 + 4354296 * 2 ^ 59
def prefixEnd_4354296 : Nat := 4983230072969 + 3 ^ 40 * 4354296 * 2
def baseEnd_4354296 : Nat := 2235846759949801030574963

theorem tailTrace_4354296 : CollatzResearch.WordTrace tailWord_4354296 prefixEnd_4354296 2235846759949801030574963 := by
  unfold tailWord_4354296
  simp only [CollatzResearch.WordTrace]
  refine ⟨79407111116568360698273371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105876148155424480931031161 79407111116568360698273371)
  ·
    refine ⟨119110666674852541047410057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79407111116568360698273371 119110666674852541047410057)
    ·
      refine ⟨89333000006139405785557543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119110666674852541047410057 89333000006139405785557543)
      ·
        refine ⟨133999500009209108678336315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89333000006139405785557543 133999500009209108678336315)
        ·
          refine ⟨200999250013813663017504473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 133999500009209108678336315 200999250013813663017504473)
          ·
            refine ⟨150749437510360247263128355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 200999250013813663017504473 150749437510360247263128355)
            ·
              refine ⟨226124156265540370894692533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 150749437510360247263128355 226124156265540370894692533)
              ·
                refine ⟨21199139649894409771377425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 226124156265540370894692533 21199139649894409771377425)
                ·
                  refine ⟨15899354737420807328533069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21199139649894409771377425 15899354737420807328533069)
                  ·
                    refine ⟨5962258026532802748199901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15899354737420807328533069 5962258026532802748199901)
                    ·
                      refine ⟨2235846759949801030574963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5962258026532802748199901 2235846759949801030574963)
                      ·
                        rfl

theorem cell23_4354296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 5, 2, 3, 3].length) (baseStart_4354296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4354296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4354296 prefixEnd_4354296 := by exact prefixLift 4354296
  have htrace : WordTrace (prefixWord ++ tailWord_4354296) baseStart_4354296 baseEnd_4354296 := by
    simpa [prefixWord, tailWord_4354296, baseEnd_4354296] using wordTrace_append hprefix tailTrace_4354296
  have hstable : (prefixWord ++ tailWord_4354296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4354296).length < 2 ^ (prefixWord ++ tailWord_4354296).sum := by decide
  have hdescent : baseEnd_4354296 < baseStart_4354296 := by decide
  rcases family_descends (prefixWord ++ tailWord_4354296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4354463 : List Nat := [1, 1, 2, 5, 1, 1, 1, 4, 1, 1, 5]
def baseStart_4354463 : Nat := 118140960795 + 4354463 * 2 ^ 59
def prefixEnd_4354463 : Nat := 4983230072969 + 3 ^ 40 * 4354463 * 2
def baseEnd_4354463 : Nat := 2235932511219101877186695

theorem tailTrace_4354463 : CollatzResearch.WordTrace tailWord_4354463 prefixEnd_4354463 2235932511219101877186695 := by
  unfold tailWord_4354463
  simp only [CollatzResearch.WordTrace]
  refine ⟨158820313223531708917876043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105880208815687805945250695 158820313223531708917876043)
  ·
    refine ⟨238230469835297563376814065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158820313223531708917876043 238230469835297563376814065)
    ·
      refine ⟨178672852376473172532610549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 238230469835297563376814065 178672852376473172532610549)
      ·
        refine ⟨16750579910294359924932239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 178672852376473172532610549 16750579910294359924932239)
        ·
          refine ⟨25125869865441539887398359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16750579910294359924932239 25125869865441539887398359)
          ·
            refine ⟨37688804798162309831097539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25125869865441539887398359 37688804798162309831097539)
            ·
              refine ⟨56533207197243464746646309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37688804798162309831097539 56533207197243464746646309)
              ·
                refine ⟨10599976349483149639996183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 56533207197243464746646309 10599976349483149639996183)
                ·
                  refine ⟨15899964524224724459994275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10599976349483149639996183 15899964524224724459994275)
                  ·
                    refine ⟨23849946786337086689991413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15899964524224724459994275 23849946786337086689991413)
                    ·
                      refine ⟨2235932511219101877186695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23849946786337086689991413 2235932511219101877186695)
                      ·
                        rfl

theorem cell23_4354463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 4, 1, 1, 5].length) (baseStart_4354463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4354463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4354463 prefixEnd_4354463 := by exact prefixLift 4354463
  have htrace : WordTrace (prefixWord ++ tailWord_4354463) baseStart_4354463 baseEnd_4354463 := by
    simpa [prefixWord, tailWord_4354463, baseEnd_4354463] using wordTrace_append hprefix tailTrace_4354463
  have hstable : (prefixWord ++ tailWord_4354463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4354463).length < 2 ^ (prefixWord ++ tailWord_4354463).sum := by decide
  have hdescent : baseEnd_4354463 < baseStart_4354463 := by decide
  rcases family_descends (prefixWord ++ tailWord_4354463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4354474 : List Nat := [3, 1, 6, 1, 1, 1, 1, 1, 3, 5]
def baseStart_4354474 : Nat := 118140960795 + 4354474 * 2 ^ 59
def prefixEnd_4354474 : Nat := 4983230072969 + 3 ^ 40 * 4354474 * 2
def baseEnd_4354474 : Nat := 745312719835433778049715

theorem tailTrace_4354474 : CollatzResearch.WordTrace tailWord_4354474 prefixEnd_4354474 745312719835433778049715 := by
  unfold tailWord_4354474
  simp only [CollatzResearch.WordTrace]
  refine ⟨39705178606622964449131619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105880476284327905197684317 39705178606622964449131619)
  ·
    refine ⟨59557767909934446673697429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39705178606622964449131619 59557767909934446673697429)
    ·
      refine ⟨2791770370778177187829567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 59557767909934446673697429 2791770370778177187829567)
      ·
        refine ⟨4187655556167265781744351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2791770370778177187829567 4187655556167265781744351)
        ·
          refine ⟨6281483334250898672616527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4187655556167265781744351 6281483334250898672616527)
          ·
            refine ⟨9422225001376348008924791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6281483334250898672616527 9422225001376348008924791)
            ·
              refine ⟨14133337502064522013387187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9422225001376348008924791 14133337502064522013387187)
              ·
                refine ⟨21200006253096783020080781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14133337502064522013387187 21200006253096783020080781)
                ·
                  refine ⟨7950002344911293632530293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21200006253096783020080781 7950002344911293632530293)
                  ·
                    refine ⟨745312719835433778049715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7950002344911293632530293 745312719835433778049715)
                    ·
                      rfl

theorem cell23_4354474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 1, 1, 3, 5].length) (baseStart_4354474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4354474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4354474 prefixEnd_4354474 := by exact prefixLift 4354474
  have htrace : WordTrace (prefixWord ++ tailWord_4354474) baseStart_4354474 baseEnd_4354474 := by
    simpa [prefixWord, tailWord_4354474, baseEnd_4354474] using wordTrace_append hprefix tailTrace_4354474
  have hstable : (prefixWord ++ tailWord_4354474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4354474).length < 2 ^ (prefixWord ++ tailWord_4354474).sum := by decide
  have hdescent : baseEnd_4354474 < baseStart_4354474 := by decide
  rcases family_descends (prefixWord ++ tailWord_4354474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4354477 : List Nat := [1, 5, 2, 2, 2, 1, 1, 1, 3, 1, 4]
def baseStart_4354477 : Nat := 118140960795 + 4354477 * 2 ^ 59
def prefixEnd_4354477 : Nat := 4983230072969 + 3 ^ 40 * 4354477 * 2
def baseEnd_4354477 : Nat := 2235939699948264822411631

theorem tailTrace_4354477 : CollatzResearch.WordTrace tailWord_4354477 prefixEnd_4354477 2235939699948264822411631 := by
  unfold tailWord_4354477
  simp only [CollatzResearch.WordTrace]
  refine ⟨158820823845480989308885685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105880549230320659539257123 158820823845480989308885685)
  ·
    refine ⟨14889452235513842747708033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 158820823845480989308885685 14889452235513842747708033)
    ·
      refine ⟨11167089176635382060781025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14889452235513842747708033 11167089176635382060781025)
      ·
        refine ⟨8375316882476536545585769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11167089176635382060781025 8375316882476536545585769)
        ·
          refine ⟨6281487661857402409189327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8375316882476536545585769 6281487661857402409189327)
          ·
            refine ⟨9422231492786103613783991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6281487661857402409189327 9422231492786103613783991)
            ·
              refine ⟨14133347239179155420675987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9422231492786103613783991 14133347239179155420675987)
              ·
                refine ⟨21200020858768733131013981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14133347239179155420675987 21200020858768733131013981)
                ·
                  refine ⟨7950007822038274924130243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21200020858768733131013981 7950007822038274924130243)
                  ·
                    refine ⟨11925011733057412386195365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7950007822038274924130243 11925011733057412386195365)
                    ·
                      refine ⟨2235939699948264822411631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11925011733057412386195365 2235939699948264822411631)
                      ·
                        rfl

theorem cell23_4354477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 1, 1, 3, 1, 4].length) (baseStart_4354477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4354477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4354477 prefixEnd_4354477 := by exact prefixLift 4354477
  have htrace : WordTrace (prefixWord ++ tailWord_4354477) baseStart_4354477 baseEnd_4354477 := by
    simpa [prefixWord, tailWord_4354477, baseEnd_4354477] using wordTrace_append hprefix tailTrace_4354477
  have hstable : (prefixWord ++ tailWord_4354477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4354477).length < 2 ^ (prefixWord ++ tailWord_4354477).sum := by decide
  have hdescent : baseEnd_4354477 < baseStart_4354477 := by decide
  rcases family_descends (prefixWord ++ tailWord_4354477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4354500 : List Nat := [2, 3, 3, 2, 3, 10]
def baseStart_4354500 : Nat := 118140960795 + 4354500 * 2 ^ 59
def prefixEnd_4354500 : Nat := 4983230072969 + 3 ^ 40 * 4354500 * 2
def baseEnd_4354500 : Nat := 9201446543223531820675

theorem tailTrace_4354500 : CollatzResearch.WordTrace tailWord_4354500 prefixEnd_4354500 9201446543223531820675 := by
  unfold tailWord_4354500
  simp only [CollatzResearch.WordTrace]
  refine ⟨79410831362198832118486477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105881108482931776157981969 79410831362198832118486477)
  ·
    refine ⟨29779061760824562044432429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79410831362198832118486477 29779061760824562044432429)
    ·
      refine ⟨11167148160309210766662161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29779061760824562044432429 11167148160309210766662161)
      ·
        refine ⟨8375361120231908074996621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11167148160309210766662161 8375361120231908074996621)
        ·
          refine ⟨3140760420086965528123733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8375361120231908074996621 3140760420086965528123733)
          ·
            refine ⟨9201446543223531820675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 3140760420086965528123733 9201446543223531820675)
            ·
              rfl

theorem cell23_4354500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 10].length) (baseStart_4354500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4354500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4354500 prefixEnd_4354500 := by exact prefixLift 4354500
  have htrace : WordTrace (prefixWord ++ tailWord_4354500) baseStart_4354500 baseEnd_4354500 := by
    simpa [prefixWord, tailWord_4354500, baseEnd_4354500] using wordTrace_append hprefix tailTrace_4354500
  have hstable : (prefixWord ++ tailWord_4354500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4354500).length < 2 ^ (prefixWord ++ tailWord_4354500).sum := by decide
  have hdescent : baseEnd_4354500 < baseStart_4354500 := by decide
  rcases family_descends (prefixWord ++ tailWord_4354500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4354527 : List Nat := [1, 1, 2, 3, 3, 2, 2, 3, 2, 1, 3]
def baseStart_4354527 : Nat := 118140960795 + 4354527 * 2 ^ 59
def prefixEnd_4354527 : Nat := 4983230072969 + 3 ^ 40 * 4354527 * 2
def baseEnd_4354527 : Nat := 2235965373980989626786401

theorem tailTrace_4354527 : CollatzResearch.WordTrace tailWord_4354527 prefixEnd_4354527 2235965373980989626786401 := by
  unfold tailWord_4354527
  simp only [CollatzResearch.WordTrace]
  refine ⟨158822647495299847848205835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105881764996866565232137223 158822647495299847848205835)
  ·
    refine ⟨238233971242949771772308753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158822647495299847848205835 238233971242949771772308753)
    ·
      refine ⟨178675478432212328829231565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 238233971242949771772308753 178675478432212328829231565)
      ·
        refine ⟨67003304412079623310961837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 178675478432212328829231565 67003304412079623310961837)
        ·
          refine ⟨25126239154529858741610689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 67003304412079623310961837 25126239154529858741610689)
          ·
            refine ⟨18844679365897394056208017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25126239154529858741610689 18844679365897394056208017)
            ·
              refine ⟨14133509524423045542156013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18844679365897394056208017 14133509524423045542156013)
              ·
                refine ⟨5300066071658642078308505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14133509524423045542156013 5300066071658642078308505)
                ·
                  refine ⟨3975049553743981558731379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5300066071658642078308505 3975049553743981558731379)
                  ·
                    refine ⟨5962574330615972338097069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3975049553743981558731379 5962574330615972338097069)
                    ·
                      refine ⟨2235965373980989626786401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5962574330615972338097069 2235965373980989626786401)
                      ·
                        rfl

theorem cell23_4354527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 2, 3, 2, 1, 3].length) (baseStart_4354527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4354527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4354527 prefixEnd_4354527 := by exact prefixLift 4354527
  have htrace : WordTrace (prefixWord ++ tailWord_4354527) baseStart_4354527 baseEnd_4354527 := by
    simpa [prefixWord, tailWord_4354527, baseEnd_4354527] using wordTrace_append hprefix tailTrace_4354527
  have hstable : (prefixWord ++ tailWord_4354527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4354527).length < 2 ^ (prefixWord ++ tailWord_4354527).sum := by decide
  have hdescent : baseEnd_4354527 < baseStart_4354527 := by decide
  rcases family_descends (prefixWord ++ tailWord_4354527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4354553 : List Nat := [1, 2, 1, 3, 1, 2, 2, 3, 2, 1, 5]
def baseStart_4354553 : Nat := 118140960795 + 4354553 * 2 ^ 59
def prefixEnd_4354553 : Nat := 4983230072969 + 3 ^ 40 * 4354553 * 2
def baseEnd_4354553 : Nat := 2235978724478006525061281

theorem tailTrace_4354553 : CollatzResearch.WordTrace tailWord_4354553 prefixEnd_4354553 2235978724478006525061281 := by
  unfold tailWord_4354553
  simp only [CollatzResearch.WordTrace]
  refine ⟨158823595793205654288652313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105882397195470436192434875 158823595793205654288652313)
  ·
    refine ⟨119117696844904240716489235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 158823595793205654288652313 119117696844904240716489235)
    ·
      refine ⟨178676545267356361074733853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119117696844904240716489235 178676545267356361074733853)
      ·
        refine ⟨67003704475258635403025195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 178676545267356361074733853 67003704475258635403025195)
        ·
          refine ⟨100505556712887953104537793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67003704475258635403025195 100505556712887953104537793)
          ·
            refine ⟨75379167534665964828403345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 100505556712887953104537793 75379167534665964828403345)
            ·
              refine ⟨56534375650999473621302509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75379167534665964828403345 56534375650999473621302509)
              ·
                refine ⟨21200390869124802607988441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56534375650999473621302509 21200390869124802607988441)
                ·
                  refine ⟨15900293151843601955991331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21200390869124802607988441 15900293151843601955991331)
                  ·
                    refine ⟨23850439727765402933986997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15900293151843601955991331 23850439727765402933986997)
                    ·
                      refine ⟨2235978724478006525061281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23850439727765402933986997 2235978724478006525061281)
                      ·
                        rfl

theorem cell23_4354553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 3, 2, 1, 5].length) (baseStart_4354553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4354553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4354553 prefixEnd_4354553 := by exact prefixLift 4354553
  have htrace : WordTrace (prefixWord ++ tailWord_4354553) baseStart_4354553 baseEnd_4354553 := by
    simpa [prefixWord, tailWord_4354553, baseEnd_4354553] using wordTrace_append hprefix tailTrace_4354553
  have hstable : (prefixWord ++ tailWord_4354553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4354553).length < 2 ^ (prefixWord ++ tailWord_4354553).sum := by decide
  have hdescent : baseEnd_4354553 < baseStart_4354553 := by decide
  rcases family_descends (prefixWord ++ tailWord_4354553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4354563 : List Nat := [1, 1, 1, 3, 2, 1, 3, 1, 4, 2, 4]
def baseStart_4354563 : Nat := 118140960795 + 4354563 * 2 ^ 59
def prefixEnd_4354563 : Nat := 4983230072969 + 3 ^ 40 * 4354563 * 2
def baseEnd_4354563 : Nat := 2235983859284551485936235

theorem tailTrace_4354563 : CollatzResearch.WordTrace tailWord_4354563 prefixEnd_4354563 2235983859284551485936235 := by
  unfold tailWord_4354563
  simp only [CollatzResearch.WordTrace]
  refine ⟨158823960523169425996516343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105882640348779617331010895 158823960523169425996516343)
  ·
    refine ⟨238235940784754138994774515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158823960523169425996516343 238235940784754138994774515)
    ·
      refine ⟨357353911177131208492161773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 238235940784754138994774515 357353911177131208492161773)
      ·
        refine ⟨134007716691424203184560665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 357353911177131208492161773 134007716691424203184560665)
        ·
          refine ⟨100505787518568152388420499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 134007716691424203184560665 100505787518568152388420499)
          ·
            refine ⟨150758681277852228582630749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100505787518568152388420499 150758681277852228582630749)
            ·
              refine ⟨56534505479194585718486531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 150758681277852228582630749 56534505479194585718486531)
              ·
                refine ⟨84801758218791878577729797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56534505479194585718486531 84801758218791878577729797)
                ·
                  refine ⟨15900329666023477233324337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 84801758218791878577729797 15900329666023477233324337)
                  ·
                    refine ⟨11925247249517607924993253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15900329666023477233324337 11925247249517607924993253)
                    ·
                      refine ⟨2235983859284551485936235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11925247249517607924993253 2235983859284551485936235)
                      ·
                        rfl

theorem cell23_4354563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 1, 4, 2, 4].length) (baseStart_4354563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4354563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4354563 prefixEnd_4354563 := by exact prefixLift 4354563
  have htrace : WordTrace (prefixWord ++ tailWord_4354563) baseStart_4354563 baseEnd_4354563 := by
    simpa [prefixWord, tailWord_4354563, baseEnd_4354563] using wordTrace_append hprefix tailTrace_4354563
  have hstable : (prefixWord ++ tailWord_4354563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4354563).length < 2 ^ (prefixWord ++ tailWord_4354563).sum := by decide
  have hdescent : baseEnd_4354563 < baseStart_4354563 := by decide
  rcases family_descends (prefixWord ++ tailWord_4354563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4354584 : List Nat := [2, 1, 2, 3, 3, 3, 1, 1, 1, 4, 2]
def baseStart_4354584 : Nat := 118140960795 + 4354584 * 2 ^ 59
def prefixEnd_4354584 : Nat := 4983230072969 + 3 ^ 40 * 4354584 * 2
def baseEnd_4354584 : Nat := 2235994642378295903773639

theorem tailTrace_4354584 : CollatzResearch.WordTrace tailWord_4354584 prefixEnd_4354584 2235994642378295903773639 := by
  unfold tailWord_4354584
  simp only [CollatzResearch.WordTrace]
  refine ⟨79412363228046673291515403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105883150970728897722020537 79412363228046673291515403)
  ·
    refine ⟨119118544842070009937273105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79412363228046673291515403 119118544842070009937273105)
    ·
      refine ⟨89338908631552507452954829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119118544842070009937273105 89338908631552507452954829)
      ·
        refine ⟨33502090736832190294858061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 89338908631552507452954829 33502090736832190294858061)
        ·
          refine ⟨12563284026312071360571773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33502090736832190294858061 12563284026312071360571773)
          ·
            refine ⟨4711231509867026760214415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12563284026312071360571773 4711231509867026760214415)
            ·
              refine ⟨7066847264800540140321623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4711231509867026760214415 7066847264800540140321623)
              ·
                refine ⟨10600270897200810210482435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7066847264800540140321623 10600270897200810210482435)
                ·
                  refine ⟨15900406345801215315723653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10600270897200810210482435 15900406345801215315723653)
                  ·
                    refine ⟨2981326189837727871698185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15900406345801215315723653 2981326189837727871698185)
                    ·
                      refine ⟨2235994642378295903773639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2981326189837727871698185 2235994642378295903773639)
                      ·
                        rfl

theorem cell23_4354584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 3, 1, 1, 1, 4, 2].length) (baseStart_4354584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4354584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4354584 prefixEnd_4354584 := by exact prefixLift 4354584
  have htrace : WordTrace (prefixWord ++ tailWord_4354584) baseStart_4354584 baseEnd_4354584 := by
    simpa [prefixWord, tailWord_4354584, baseEnd_4354584] using wordTrace_append hprefix tailTrace_4354584
  have hstable : (prefixWord ++ tailWord_4354584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4354584).length < 2 ^ (prefixWord ++ tailWord_4354584).sum := by decide
  have hdescent : baseEnd_4354584 < baseStart_4354584 := by decide
  rcases family_descends (prefixWord ++ tailWord_4354584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4354603 : List Nat := [1, 1, 1, 1, 2, 1, 3, 2, 6, 5]
def baseStart_4354603 : Nat := 118140960795 + 4354603 * 2 ^ 59
def prefixEnd_4354603 : Nat := 4983230072969 + 3 ^ 40 * 4354603 * 2
def baseEnd_4354603 : Nat := 745334799503577109812017

theorem tailTrace_4354603 : CollatzResearch.WordTrace tailWord_4354603 prefixEnd_4354603 745334799503577109812017 := by
  unfold tailWord_4354603
  simp only [CollatzResearch.WordTrace]
  refine ⟨158825419443024512827972463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105883612962016341885314975 158825419443024512827972463)
  ·
    refine ⟨238238129164536769241958695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158825419443024512827972463 238238129164536769241958695)
    ·
      refine ⟨357357193746805153862938043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 238238129164536769241958695 357357193746805153862938043)
      ·
        refine ⟨536035790620207730794407065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 357357193746805153862938043 536035790620207730794407065)
        ·
          refine ⟨402026842965155798095805299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 536035790620207730794407065 402026842965155798095805299)
          ·
            refine ⟨603040264447733697143707949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 402026842965155798095805299 603040264447733697143707949)
            ·
              refine ⟨226140099167900136428890481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 603040264447733697143707949 226140099167900136428890481)
              ·
                refine ⟨169605074375925102321667861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 226140099167900136428890481 169605074375925102321667861)
                ·
                  refine ⟨7950237861371489171328181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 169605074375925102321667861 7950237861371489171328181)
                  ·
                    refine ⟨745334799503577109812017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7950237861371489171328181 745334799503577109812017)
                    ·
                      rfl

theorem cell23_4354603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 2, 6, 5].length) (baseStart_4354603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4354603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4354603 prefixEnd_4354603 := by exact prefixLift 4354603
  have htrace : WordTrace (prefixWord ++ tailWord_4354603) baseStart_4354603 baseEnd_4354603 := by
    simpa [prefixWord, tailWord_4354603, baseEnd_4354603] using wordTrace_append hprefix tailTrace_4354603
  have hstable : (prefixWord ++ tailWord_4354603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4354603).length < 2 ^ (prefixWord ++ tailWord_4354603).sum := by decide
  have hdescent : baseEnd_4354603 < baseStart_4354603 := by decide
  rcases family_descends (prefixWord ++ tailWord_4354603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4354620 : List Nat := [2, 2, 2, 2, 3, 1, 1, 1, 4, 5]
def baseStart_4354620 : Nat := 118140960795 + 4354620 * 2 ^ 59
def prefixEnd_4354620 : Nat := 4983230072969 + 3 ^ 40 * 4354620 * 2
def baseEnd_4354620 : Nat := 745337709227285920974491

theorem tailTrace_4354620 : CollatzResearch.WordTrace tailWord_4354620 prefixEnd_4354620 745337709227285920974491 := by
  unfold tailWord_4354620
  simp only [CollatzResearch.WordTrace]
  refine ⟨79413019741981462365670657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105884026322641949820894209 79413019741981462365670657)
  ·
    refine ⟨59559764806486096774252993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79413019741981462365670657 59559764806486096774252993)
    ·
      refine ⟨44669823604864572580689745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59559764806486096774252993 44669823604864572580689745)
      ·
        refine ⟨33502367703648429435517309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44669823604864572580689745 33502367703648429435517309)
        ·
          refine ⟨12563387888868161038318991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33502367703648429435517309 12563387888868161038318991)
          ·
            refine ⟨18845081833302241557478487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12563387888868161038318991 18845081833302241557478487)
            ·
              refine ⟨28267622749953362336217731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18845081833302241557478487 28267622749953362336217731)
              ·
                refine ⟨42401434124930043504326597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28267622749953362336217731 42401434124930043504326597)
                ·
                  refine ⟨7950268898424383157061237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 42401434124930043504326597 7950268898424383157061237)
                  ·
                    refine ⟨745337709227285920974491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7950268898424383157061237 745337709227285920974491)
                    ·
                      rfl

theorem cell23_4354620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 1, 4, 5].length) (baseStart_4354620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4354620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4354620 prefixEnd_4354620 := by exact prefixLift 4354620
  have htrace : WordTrace (prefixWord ++ tailWord_4354620) baseStart_4354620 baseEnd_4354620 := by
    simpa [prefixWord, tailWord_4354620, baseEnd_4354620] using wordTrace_append hprefix tailTrace_4354620
  have hstable : (prefixWord ++ tailWord_4354620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4354620).length < 2 ^ (prefixWord ++ tailWord_4354620).sum := by decide
  have hdescent : baseEnd_4354620 < baseStart_4354620 := by decide
  rcases family_descends (prefixWord ++ tailWord_4354620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4354657 : List Nat := [1, 2, 3, 1, 1, 5, 2, 1, 2, 1, 4]
def baseStart_4354657 : Nat := 118140960795 + 4354657 * 2 ^ 59
def prefixEnd_4354657 : Nat := 4983230072969 + 3 ^ 40 * 4354657 * 2
def baseEnd_4354657 : Nat := 2236032126466074118160803

theorem tailTrace_4354657 : CollatzResearch.WordTrace tailWord_4354657 prefixEnd_4354657 2236032126466074118160803 := by
  unfold tailWord_4354657
  simp only [CollatzResearch.WordTrace]
  refine ⟨158827388984828880050438225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105884925989885920033625483 158827388984828880050438225)
  ·
    refine ⟨119120541738621660037828669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 158827388984828880050438225 119120541738621660037828669)
    ·
      refine ⟨44670203151983122514185751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 119120541738621660037828669 44670203151983122514185751)
      ·
        refine ⟨67005304727974683771278627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44670203151983122514185751 67005304727974683771278627)
        ·
          refine ⟨100507957091962025656917941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67005304727974683771278627 100507957091962025656917941)
          ·
            refine ⟨9422620977371439905336057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 100507957091962025656917941 9422620977371439905336057)
            ·
              refine ⟨7066965733028579929002043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9422620977371439905336057 7066965733028579929002043)
              ·
                refine ⟨10600448599542869893503065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7066965733028579929002043 10600448599542869893503065)
                ·
                  refine ⟨7950336449657152420127299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10600448599542869893503065 7950336449657152420127299)
                  ·
                    refine ⟨11925504674485728630190949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7950336449657152420127299 11925504674485728630190949)
                    ·
                      refine ⟨2236032126466074118160803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11925504674485728630190949 2236032126466074118160803)
                      ·
                        rfl

theorem cell23_4354657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 2, 1, 2, 1, 4].length) (baseStart_4354657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4354657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4354657 prefixEnd_4354657 := by exact prefixLift 4354657
  have htrace : WordTrace (prefixWord ++ tailWord_4354657) baseStart_4354657 baseEnd_4354657 := by
    simpa [prefixWord, tailWord_4354657, baseEnd_4354657] using wordTrace_append hprefix tailTrace_4354657
  have hstable : (prefixWord ++ tailWord_4354657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4354657).length < 2 ^ (prefixWord ++ tailWord_4354657).sum := by decide
  have hdescent : baseEnd_4354657 < baseStart_4354657 := by decide
  rcases family_descends (prefixWord ++ tailWord_4354657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4354707 : List Nat := [1, 1, 1, 2, 1, 2, 2, 6, 3, 1, 3]
def baseStart_4354707 : Nat := 118140960795 + 4354707 * 2 ^ 59
def prefixEnd_4354707 : Nat := 4983230072969 + 3 ^ 40 * 4354707 * 2
def baseEnd_4354707 : Nat := 2236057800498798922535573

theorem tailTrace_4354707 : CollatzResearch.WordTrace tailWord_4354707 prefixEnd_4354707 2236057800498798922535573 := by
  unfold tailWord_4354707
  simp only [CollatzResearch.WordTrace]
  refine ⟨158829212634647738589758375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105886141756431825726505583 158829212634647738589758375)
  ·
    refine ⟨238243818951971607884637563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158829212634647738589758375 238243818951971607884637563)
    ·
      refine ⟨357365728427957411826956345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 238243818951971607884637563 357365728427957411826956345)
      ·
        refine ⟨268024296320968058870217259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 357365728427957411826956345 268024296320968058870217259)
        ·
          refine ⟨402036444481452088305325889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 268024296320968058870217259 402036444481452088305325889)
          ·
            refine ⟨301527333361089066228994417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 402036444481452088305325889 301527333361089066228994417)
            ·
              refine ⟨226145500020816799671745813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 301527333361089066228994417 226145500020816799671745813)
              ·
                refine ⟨10600570313475787484613085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 226145500020816799671745813 10600570313475787484613085)
                ·
                  refine ⟨3975213867553420306729907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10600570313475787484613085 3975213867553420306729907)
                  ·
                    refine ⟨5962820801330130460094861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3975213867553420306729907 5962820801330130460094861)
                    ·
                      refine ⟨2236057800498798922535573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5962820801330130460094861 2236057800498798922535573)
                      ·
                        rfl

theorem cell23_4354707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 6, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 6, 3, 1, 3].length) (baseStart_4354707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4354707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4354707 prefixEnd_4354707 := by exact prefixLift 4354707
  have htrace : WordTrace (prefixWord ++ tailWord_4354707) baseStart_4354707 baseEnd_4354707 := by
    simpa [prefixWord, tailWord_4354707, baseEnd_4354707] using wordTrace_append hprefix tailTrace_4354707
  have hstable : (prefixWord ++ tailWord_4354707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4354707).length < 2 ^ (prefixWord ++ tailWord_4354707).sum := by decide
  have hdescent : baseEnd_4354707 < baseStart_4354707 := by decide
  rcases family_descends (prefixWord ++ tailWord_4354707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4354741 : List Nat := [1, 3, 3, 3, 1, 2, 2, 1, 3, 1, 3]
def baseStart_4354741 : Nat := 118140960795 + 4354741 * 2 ^ 59
def prefixEnd_4354741 : Nat := 4983230072969 + 3 ^ 40 * 4354741 * 2
def baseEnd_4354741 : Nat := 2236075258841051789510417

theorem tailTrace_4354741 : CollatzResearch.WordTrace tailWord_4354741 prefixEnd_4354741 2236075258841051789510417 := by
  unfold tailWord_4354741
  simp only [CollatzResearch.WordTrace]
  refine ⟨158830452716524562396496077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105886968477683041597664051 158830452716524562396496077)
  ·
    refine ⟨59561419768696710898686029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 158830452716524562396496077 59561419768696710898686029)
    ·
      refine ⟨22335532413261266587007261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59561419768696710898686029 22335532413261266587007261)
      ·
        refine ⟨8375824654972974970127723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22335532413261266587007261 8375824654972974970127723)
        ·
          refine ⟨12563736982459462455191585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8375824654972974970127723 12563736982459462455191585)
          ·
            refine ⟨9422802736844596841393689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12563736982459462455191585 9422802736844596841393689)
            ·
              refine ⟨7067102052633447631045267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9422802736844596841393689 7067102052633447631045267)
              ·
                refine ⟨10600653078950171446567901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7067102052633447631045267 10600653078950171446567901)
                ·
                  refine ⟨3975244904606314292462963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10600653078950171446567901 3975244904606314292462963)
                  ·
                    refine ⟨5962867356909471438694445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3975244904606314292462963 5962867356909471438694445)
                    ·
                      refine ⟨2236075258841051789510417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5962867356909471438694445 2236075258841051789510417)
                      ·
                        rfl

theorem cell23_4354741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 2, 1, 3, 1, 3].length) (baseStart_4354741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4354741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4354741 prefixEnd_4354741 := by exact prefixLift 4354741
  have htrace : WordTrace (prefixWord ++ tailWord_4354741) baseStart_4354741 baseEnd_4354741 := by
    simpa [prefixWord, tailWord_4354741, baseEnd_4354741] using wordTrace_append hprefix tailTrace_4354741
  have hstable : (prefixWord ++ tailWord_4354741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4354741).length < 2 ^ (prefixWord ++ tailWord_4354741).sum := by decide
  have hdescent : baseEnd_4354741 < baseStart_4354741 := by decide
  rcases family_descends (prefixWord ++ tailWord_4354741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4354764 : List Nat := [2, 2, 1, 5, 1, 1, 1, 4, 1, 1, 4]
def baseStart_4354764 : Nat := 118140960795 + 4354764 * 2 ^ 59
def prefixEnd_4354764 : Nat := 4983230072969 + 3 ^ 40 * 4354764 * 2
def baseEnd_4354764 : Nat := 2236087068896105199522811

theorem tailTrace_4354764 : CollatzResearch.WordTrace tailWord_4354764 prefixEnd_4354764 2236087068896105199522811 := by
  unfold tailWord_4354764
  simp only [CollatzResearch.WordTrace]
  refine ⟨79415645797720618662291673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105887527730294158216388897 79415645797720618662291673)
  ·
    refine ⟨59561734348290463996718755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79415645797720618662291673 59561734348290463996718755)
    ·
      refine ⟨89342601522435695995078133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59561734348290463996718755 89342601522435695995078133)
      ·
        refine ⟨8375868892728346499538575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 89342601522435695995078133 8375868892728346499538575)
        ·
          refine ⟨12563803339092519749307863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8375868892728346499538575 12563803339092519749307863)
          ·
            refine ⟨18845705008638779623961795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12563803339092519749307863 18845705008638779623961795)
            ·
              refine ⟨28268557512958169435942693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18845705008638779623961795 28268557512958169435942693)
              ·
                refine ⟨5300354533679656769239255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28268557512958169435942693 5300354533679656769239255)
                ·
                  refine ⟨7950531800519485153858883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5300354533679656769239255 7950531800519485153858883)
                  ·
                    refine ⟨11925797700779227730788325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7950531800519485153858883 11925797700779227730788325)
                    ·
                      refine ⟨2236087068896105199522811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11925797700779227730788325 2236087068896105199522811)
                      ·
                        rfl

theorem cell23_4354764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 4, 1, 1, 4].length) (baseStart_4354764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4354764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4354764 prefixEnd_4354764 := by exact prefixLift 4354764
  have htrace : WordTrace (prefixWord ++ tailWord_4354764) baseStart_4354764 baseEnd_4354764 := by
    simpa [prefixWord, tailWord_4354764, baseEnd_4354764] using wordTrace_append hprefix tailTrace_4354764
  have hstable : (prefixWord ++ tailWord_4354764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4354764).length < 2 ^ (prefixWord ++ tailWord_4354764).sum := by decide
  have hdescent : baseEnd_4354764 < baseStart_4354764 := by decide
  rcases family_descends (prefixWord ++ tailWord_4354764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4354787 : List Nat := [1, 1, 1, 7, 1, 3, 9]
def baseStart_4354787 : Nat := 118140960795 + 4354787 * 2 ^ 59
def prefixEnd_4354787 : Nat := 4983230072969 + 3 ^ 40 * 4354787 * 2
def baseEnd_4354787 : Nat := 27606158999397019870805

theorem tailTrace_4354787 : CollatzResearch.WordTrace tailWord_4354787 prefixEnd_4354787 27606158999397019870805 := by
  unfold tailWord_4354787
  simp only [CollatzResearch.WordTrace]
  refine ⟨158832130474357912252670615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105888086982905274835113743 158832130474357912252670615)
  ·
    refine ⟨238248195711536868379005923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158832130474357912252670615 238248195711536868379005923)
    ·
      refine ⟨357372293567305302568508885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 238248195711536868379005923 357372293567305302568508885)
      ·
        refine ⟨8375913130483718028949427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 357372293567305302568508885 8375913130483718028949427)
        ·
          refine ⟨12563869695725577043424141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8375913130483718028949427 12563869695725577043424141)
          ·
            refine ⟨4711451135897091391284053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12563869695725577043424141 4711451135897091391284053)
            ·
              refine ⟨27606158999397019870805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4711451135897091391284053 27606158999397019870805)
              ·
                rfl

theorem cell23_4354787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 3, 9].length) (baseStart_4354787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4354787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4354787 prefixEnd_4354787 := by exact prefixLift 4354787
  have htrace : WordTrace (prefixWord ++ tailWord_4354787) baseStart_4354787 baseEnd_4354787 := by
    simpa [prefixWord, tailWord_4354787, baseEnd_4354787] using wordTrace_append hprefix tailTrace_4354787
  have hstable : (prefixWord ++ tailWord_4354787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4354787).length < 2 ^ (prefixWord ++ tailWord_4354787).sum := by decide
  have hdescent : baseEnd_4354787 < baseStart_4354787 := by decide
  rcases family_descends (prefixWord ++ tailWord_4354787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4354798 : List Nat := [4, 1, 2, 1, 1, 5, 1, 1, 3, 2, 2]
def baseStart_4354798 : Nat := 118140960795 + 4354798 * 2 ^ 59
def prefixEnd_4354798 : Nat := 4983230072969 + 3 ^ 40 * 4354798 * 2
def baseEnd_4354798 : Nat := 2236104527238358066497655

theorem tailTrace_4354798 : CollatzResearch.WordTrace tailWord_4354798 prefixEnd_4354798 2236104527238358066497655 := by
  unfold tailWord_4354798
  simp only [CollatzResearch.WordTrace]
  refine ⟨19854066459664757641415131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 105888354451545374087547365 19854066459664757641415131)
  ·
    refine ⟨29781099689497136462122697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19854066459664757641415131 29781099689497136462122697)
    ·
      refine ⟨22335824767122852346592023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29781099689497136462122697 22335824767122852346592023)
      ·
        refine ⟨33503737150684278519888035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22335824767122852346592023 33503737150684278519888035)
        ·
          refine ⟨50255605726026417779832053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33503737150684278519888035 50255605726026417779832053)
          ·
            refine ⟨4711463036814976666859255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 50255605726026417779832053 4711463036814976666859255)
            ·
              refine ⟨7067194555222465000288883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4711463036814976666859255 7067194555222465000288883)
              ·
                refine ⟨10600791832833697500433325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7067194555222465000288883 10600791832833697500433325)
                ·
                  refine ⟨3975296937312636562662497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10600791832833697500433325 3975296937312636562662497)
                  ·
                    refine ⟨2981472702984477421996873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3975296937312636562662497 2981472702984477421996873)
                    ·
                      refine ⟨2236104527238358066497655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2981472702984477421996873 2236104527238358066497655)
                      ·
                        rfl

theorem cell23_4354798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 5, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 5, 1, 1, 3, 2, 2].length) (baseStart_4354798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4354798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4354798 prefixEnd_4354798 := by exact prefixLift 4354798
  have htrace : WordTrace (prefixWord ++ tailWord_4354798) baseStart_4354798 baseEnd_4354798 := by
    simpa [prefixWord, tailWord_4354798, baseEnd_4354798] using wordTrace_append hprefix tailTrace_4354798
  have hstable : (prefixWord ++ tailWord_4354798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4354798).length < 2 ^ (prefixWord ++ tailWord_4354798).sum := by decide
  have hdescent : baseEnd_4354798 < baseStart_4354798 := by decide
  rcases family_descends (prefixWord ++ tailWord_4354798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4354800 : List Nat := [2, 1, 1, 1, 3, 1, 4, 1, 2, 7]
def baseStart_4354800 : Nat := 118140960795 + 4354800 * 2 ^ 59
def prefixEnd_4354800 : Nat := 4983230072969 + 3 ^ 40 * 4354800 * 2
def baseEnd_4354800 : Nat := 745368518066555686224215

theorem tailTrace_4354800 : CollatzResearch.WordTrace tailWord_4354800 prefixEnd_4354800 745368518066555686224215 := by
  unfold tailWord_4354800
  simp only [CollatzResearch.WordTrace]
  refine ⟨79416302311655407736446927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105888403082207210315262569 79416302311655407736446927)
  ·
    refine ⟨119124453467483111604670391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79416302311655407736446927 119124453467483111604670391)
    ·
      refine ⟨178686680201224667407005587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119124453467483111604670391 178686680201224667407005587)
      ·
        refine ⟨268030020301837001110508381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 178686680201224667407005587 268030020301837001110508381)
        ·
          refine ⟨100511257613188875416440643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 268030020301837001110508381 100511257613188875416440643)
          ·
            refine ⟨150766886419783313124660965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100511257613188875416440643 150766886419783313124660965)
            ·
              refine ⟨28268791203709371210873931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 150766886419783313124660965 28268791203709371210873931)
              ·
                refine ⟨42403186805564056816310897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28268791203709371210873931 42403186805564056816310897)
                ·
                  refine ⟨31802390104173042612233173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42403186805564056816310897 31802390104173042612233173)
                  ·
                    refine ⟨745368518066555686224215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 31802390104173042612233173 745368518066555686224215)
                    ·
                      rfl

theorem cell23_4354800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 1, 2, 7].length) (baseStart_4354800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4354800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4354800 prefixEnd_4354800 := by exact prefixLift 4354800
  have htrace : WordTrace (prefixWord ++ tailWord_4354800) baseStart_4354800 baseEnd_4354800 := by
    simpa [prefixWord, tailWord_4354800, baseEnd_4354800] using wordTrace_append hprefix tailTrace_4354800
  have hstable : (prefixWord ++ tailWord_4354800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4354800).length < 2 ^ (prefixWord ++ tailWord_4354800).sum := by decide
  have hdescent : baseEnd_4354800 < baseStart_4354800 := by decide
  rcases family_descends (prefixWord ++ tailWord_4354800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4354807 : List Nat := [1, 1, 3, 1, 1, 1, 3, 1, 2, 7, 2]
def baseStart_4354807 : Nat := 118140960795 + 4354807 * 2 ^ 59
def prefixEnd_4354807 : Nat := 4983230072969 + 3 ^ 40 * 4354807 * 2
def baseEnd_4354807 : Nat := 2236109148564248531285113

theorem tailTrace_4354807 : CollatzResearch.WordTrace tailWord_4354807 prefixEnd_4354807 2236109148564248531285113 := by
  unfold tailWord_4354807
  simp only [CollatzResearch.WordTrace]
  refine ⟨158832859934285455668398675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105888573289523637112265783 158832859934285455668398675)
  ·
    refine ⟨238249289901428183502598013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158832859934285455668398675 238249289901428183502598013)
    ·
      refine ⟨89343483713035568813474255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 238249289901428183502598013 89343483713035568813474255)
      ·
        refine ⟨134015225569553353220211383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89343483713035568813474255 134015225569553353220211383)
        ·
          refine ⟨201022838354330029830317075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 134015225569553353220211383 201022838354330029830317075)
          ·
            refine ⟨301534257531495044745475613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 201022838354330029830317075 301534257531495044745475613)
            ·
              refine ⟨113075346574310641779553355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 301534257531495044745475613 113075346574310641779553355)
              ·
                refine ⟨169613019861465962669330033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 113075346574310641779553355 169613019861465962669330033)
                ·
                  refine ⟨127209764896099472001997525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 169613019861465962669330033 127209764896099472001997525)
                  ·
                    refine ⟨2981478864752331375046817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 127209764896099472001997525 2981478864752331375046817)
                    ·
                      refine ⟨2236109148564248531285113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2981478864752331375046817 2236109148564248531285113)
                      ·
                        rfl

theorem cell23_4354807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 1, 2, 7, 2].length) (baseStart_4354807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4354807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4354807 prefixEnd_4354807 := by exact prefixLift 4354807
  have htrace : WordTrace (prefixWord ++ tailWord_4354807) baseStart_4354807 baseEnd_4354807 := by
    simpa [prefixWord, tailWord_4354807, baseEnd_4354807] using wordTrace_append hprefix tailTrace_4354807
  have hstable : (prefixWord ++ tailWord_4354807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4354807).length < 2 ^ (prefixWord ++ tailWord_4354807).sum := by decide
  have hdescent : baseEnd_4354807 < baseStart_4354807 := by decide
  rcases family_descends (prefixWord ++ tailWord_4354807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4354818 : List Nat := [3, 4, 1, 1, 1, 4, 1, 2, 1, 2, 3]
def baseStart_4354818 : Nat := 118140960795 + 4354818 * 2 ^ 59
def prefixEnd_4354818 : Nat := 4983230072969 + 3 ^ 40 * 4354818 * 2
def baseEnd_4354818 : Nat := 2236114796851447988247563

theorem tailTrace_4354818 : CollatzResearch.WordTrace tailWord_4354818 prefixEnd_4354818 2236114796851447988247563 := by
  unfold tailWord_4354818
  simp only [CollatzResearch.WordTrace]
  refine ⟨39708315284311401136762277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105888840758163736364699405 39708315284311401136762277)
  ·
    refine ⟨7445309115808387713142927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39708315284311401136762277 7445309115808387713142927)
    ·
      refine ⟨11167963673712581569714391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7445309115808387713142927 11167963673712581569714391)
      ·
        refine ⟨16751945510568872354571587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11167963673712581569714391 16751945510568872354571587)
        ·
          refine ⟨25127918265853308531857381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16751945510568872354571587 25127918265853308531857381)
          ·
            refine ⟨4711484674847495349723259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25127918265853308531857381 4711484674847495349723259)
            ·
              refine ⟨7067227012271243024584889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4711484674847495349723259 7067227012271243024584889)
              ·
                refine ⟨5300420259203432268438667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7067227012271243024584889 5300420259203432268438667)
                ·
                  refine ⟨7950630388805148402658001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5300420259203432268438667 7950630388805148402658001)
                  ·
                    refine ⟨5962972791603861301993501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7950630388805148402658001 5962972791603861301993501)
                    ·
                      refine ⟨2236114796851447988247563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5962972791603861301993501 2236114796851447988247563)
                      ·
                        rfl

theorem cell23_4354818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 4, 1, 2, 1, 2, 3].length) (baseStart_4354818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4354818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4354818 prefixEnd_4354818 := by exact prefixLift 4354818
  have htrace : WordTrace (prefixWord ++ tailWord_4354818) baseStart_4354818 baseEnd_4354818 := by
    simpa [prefixWord, tailWord_4354818, baseEnd_4354818] using wordTrace_append hprefix tailTrace_4354818
  have hstable : (prefixWord ++ tailWord_4354818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4354818).length < 2 ^ (prefixWord ++ tailWord_4354818).sum := by decide
  have hdescent : baseEnd_4354818 < baseStart_4354818 := by decide
  rcases family_descends (prefixWord ++ tailWord_4354818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4354867 : List Nat := [1, 1, 1, 2, 6, 1, 1, 1, 1, 4, 4]
def baseStart_4354867 : Nat := 118140960795 + 4354867 * 2 ^ 59
def prefixEnd_4354867 : Nat := 4983230072969 + 3 ^ 40 * 4354867 * 2
def baseEnd_4354867 : Nat := 2236139957403518296534837

theorem tailTrace_4354867 : CollatzResearch.WordTrace tailWord_4354867 prefixEnd_4354867 2236139957403518296534837 := by
  unfold tailWord_4354867
  simp only [CollatzResearch.WordTrace]
  refine ⟨158835048314068085915582855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105890032209378723943721903 158835048314068085915582855)
  ·
    refine ⟨238252572471102128873374283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158835048314068085915582855 238252572471102128873374283)
    ·
      refine ⟨357378858706653193310061425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 238252572471102128873374283 357378858706653193310061425)
      ·
        refine ⟨268034144029989894982546069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 357378858706653193310061425 268034144029989894982546069)
        ·
          refine ⟨12564100501405776327306847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 268034144029989894982546069 12564100501405776327306847)
          ·
            refine ⟨18846150752108664490960271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12564100501405776327306847 18846150752108664490960271)
            ·
              refine ⟨28269226128162996736440407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18846150752108664490960271 28269226128162996736440407)
              ·
                refine ⟨42403839192244495104660611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28269226128162996736440407 42403839192244495104660611)
                ·
                  refine ⟨63605758788366742656990917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42403839192244495104660611 63605758788366742656990917)
                  ·
                    refine ⟨11926079772818764248185797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 63605758788366742656990917 11926079772818764248185797)
                    ·
                      refine ⟨2236139957403518296534837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11926079772818764248185797 2236139957403518296534837)
                      ·
                        rfl

theorem cell23_4354867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 1, 1, 4, 4].length) (baseStart_4354867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4354867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4354867 prefixEnd_4354867 := by exact prefixLift 4354867
  have htrace : WordTrace (prefixWord ++ tailWord_4354867) baseStart_4354867 baseEnd_4354867 := by
    simpa [prefixWord, tailWord_4354867, baseEnd_4354867] using wordTrace_append hprefix tailTrace_4354867
  have hstable : (prefixWord ++ tailWord_4354867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4354867).length < 2 ^ (prefixWord ++ tailWord_4354867).sum := by decide
  have hdescent : baseEnd_4354867 < baseStart_4354867 := by decide
  rcases family_descends (prefixWord ++ tailWord_4354867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4354871 : List Nat := [1, 1, 3, 1, 2, 1, 3, 5, 2, 2, 2]
def baseStart_4354871 : Nat := 118140960795 + 4354871 * 2 ^ 59
def prefixEnd_4354871 : Nat := 4983230072969 + 3 ^ 40 * 4354871 * 2
def baseEnd_4354871 : Nat := 2236142011326136280884819

theorem tailTrace_4354871 : CollatzResearch.WordTrace tailWord_4354871 prefixEnd_4354871 2236142011326136280884819 := by
  unfold tailWord_4354871
  simp only [CollatzResearch.WordTrace]
  refine ⟨158835194206053594598728467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105890129470702396399152311 158835194206053594598728467)
  ·
    refine ⟨238252791309080391898092701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158835194206053594598728467 238252791309080391898092701)
    ·
      refine ⟨89344796740905146961784763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 238252791309080391898092701 89344796740905146961784763)
      ·
        refine ⟨134017195111357720442677145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89344796740905146961784763 134017195111357720442677145)
        ·
          refine ⟨100512896333518290332007859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 134017195111357720442677145 100512896333518290332007859)
          ·
            refine ⟨150769344500277435498011789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100512896333518290332007859 150769344500277435498011789)
            ·
              refine ⟨56538504187604038311754421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 150769344500277435498011789 56538504187604038311754421)
              ·
                refine ⟨5300484767587878591726977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 56538504187604038311754421 5300484767587878591726977)
                ·
                  refine ⟨3975363575690908943795233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5300484767587878591726977 3975363575690908943795233)
                  ·
                    refine ⟨2981522681768181707846425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3975363575690908943795233 2981522681768181707846425)
                    ·
                      refine ⟨2236142011326136280884819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2981522681768181707846425 2236142011326136280884819)
                      ·
                        rfl

theorem cell23_4354871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 5, 2, 2, 2].length) (baseStart_4354871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4354871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4354871 prefixEnd_4354871 := by exact prefixLift 4354871
  have htrace : WordTrace (prefixWord ++ tailWord_4354871) baseStart_4354871 baseEnd_4354871 := by
    simpa [prefixWord, tailWord_4354871, baseEnd_4354871] using wordTrace_append hprefix tailTrace_4354871
  have hstable : (prefixWord ++ tailWord_4354871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4354871).length < 2 ^ (prefixWord ++ tailWord_4354871).sum := by decide
  have hdescent : baseEnd_4354871 < baseStart_4354871 := by decide
  rcases family_descends (prefixWord ++ tailWord_4354871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4354887 : List Nat := [1, 1, 4, 1, 2, 1, 1, 1, 3, 5, 3]
def baseStart_4354887 : Nat := 118140960795 + 4354887 * 2 ^ 59
def prefixEnd_4354887 : Nat := 4983230072969 + 3 ^ 40 * 4354887 * 2
def baseEnd_4354887 : Nat := 2236150227016608218284745

theorem tailTrace_4354887 : CollatzResearch.WordTrace tailWord_4354887 prefixEnd_4354887 2236150227016608218284745 := by
  unfold tailWord_4354887
  simp only [CollatzResearch.WordTrace]
  refine ⟨158835777773995629331310915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105890518515997086220873943 158835777773995629331310915)
  ·
    refine ⟨238253666660993443996966373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158835777773995629331310915 238253666660993443996966373)
    ·
      refine ⟨44672562498936270749431195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 238253666660993443996966373 44672562498936270749431195)
      ·
        refine ⟨67008843748404406124146793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44672562498936270749431195 67008843748404406124146793)
        ·
          refine ⟨50256632811303304593110095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67008843748404406124146793 50256632811303304593110095)
          ·
            refine ⟨75384949216954956889665143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50256632811303304593110095 75384949216954956889665143)
            ·
              refine ⟨113077423825432435334497715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75384949216954956889665143 113077423825432435334497715)
              ·
                refine ⟨169616135738148653001746573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 113077423825432435334497715 169616135738148653001746573)
                ·
                  refine ⟨63606050901805744875654965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 169616135738148653001746573 63606050901805744875654965)
                  ·
                    refine ⟨5963067272044288582092653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 63606050901805744875654965 5963067272044288582092653)
                    ·
                      refine ⟨2236150227016608218284745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5963067272044288582092653 2236150227016608218284745)
                      ·
                        rfl

theorem cell23_4354887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 1, 3, 5, 3].length) (baseStart_4354887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4354887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4354887 prefixEnd_4354887 := by exact prefixLift 4354887
  have htrace : WordTrace (prefixWord ++ tailWord_4354887) baseStart_4354887 baseEnd_4354887 := by
    simpa [prefixWord, tailWord_4354887, baseEnd_4354887] using wordTrace_append hprefix tailTrace_4354887
  have hstable : (prefixWord ++ tailWord_4354887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4354887).length < 2 ^ (prefixWord ++ tailWord_4354887).sum := by decide
  have hdescent : baseEnd_4354887 < baseStart_4354887 := by decide
  rcases family_descends (prefixWord ++ tailWord_4354887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4354917 : List Nat := [1, 3, 1, 3, 1, 1, 2, 3, 1, 2, 5]
def baseStart_4354917 : Nat := 118140960795 + 4354917 * 2 ^ 59
def prefixEnd_4354917 : Nat := 4983230072969 + 3 ^ 40 * 4354917 * 2
def baseEnd_4354917 : Nat := 2236165631436243100909607

theorem tailTrace_4354917 : CollatzResearch.WordTrace tailWord_4354917 prefixEnd_4354917 2236165631436243100909607 := by
  unfold tailWord_4354917
  simp only [CollatzResearch.WordTrace]
  refine ⟨158836871963886944454903005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105891247975924629636602003 158836871963886944454903005)
  ·
    refine ⟨59563826986457604170588627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 158836871963886944454903005 59563826986457604170588627)
    ·
      refine ⟨89345740479686406255882941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59563826986457604170588627 89345740479686406255882941)
      ·
        refine ⟨33504652679882402345956103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 89345740479686406255882941 33504652679882402345956103)
        ·
          refine ⟨50256979019823603518934155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33504652679882402345956103 50256979019823603518934155)
          ·
            refine ⟨75385468529735405278401233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50256979019823603518934155 75385468529735405278401233)
            ·
              refine ⟨56539101397301553958800925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75385468529735405278401233 56539101397301553958800925)
              ·
                refine ⟨21202163023988082734550347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56539101397301553958800925 21202163023988082734550347)
                ·
                  refine ⟨31803244535982124101825521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21202163023988082734550347 31803244535982124101825521)
                  ·
                    refine ⟨23852433401986593076369141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 31803244535982124101825521 23852433401986593076369141)
                    ·
                      refine ⟨2236165631436243100909607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23852433401986593076369141 2236165631436243100909607)
                      ·
                        rfl

theorem cell23_4354917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 3, 1, 2, 5].length) (baseStart_4354917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4354917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4354917 prefixEnd_4354917 := by exact prefixLift 4354917
  have htrace : WordTrace (prefixWord ++ tailWord_4354917) baseStart_4354917 baseEnd_4354917 := by
    simpa [prefixWord, tailWord_4354917, baseEnd_4354917] using wordTrace_append hprefix tailTrace_4354917
  have hstable : (prefixWord ++ tailWord_4354917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4354917).length < 2 ^ (prefixWord ++ tailWord_4354917).sum := by decide
  have hdescent : baseEnd_4354917 < baseStart_4354917 := by decide
  rcases family_descends (prefixWord ++ tailWord_4354917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4354944 : List Nat := [2, 1, 1, 2, 1, 2, 2, 2, 4, 4, 2]
def baseStart_4354944 : Nat := 118140960795 + 4354944 * 2 ^ 59
def prefixEnd_4354944 : Nat := 4983230072969 + 3 ^ 40 * 4354944 * 2
def baseEnd_4354944 : Nat := 2236179495413914495271983

theorem tailTrace_4354944 : CollatzResearch.WordTrace tailWord_4354944 prefixEnd_4354944 2236179495413914495271983 := by
  unfold tailWord_4354944
  simp only [CollatzResearch.WordTrace]
  refine ⟨79418928367394564033067943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105891904489859418710757257 79418928367394564033067943)
  ·
    refine ⟨119128392551091846049601915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79418928367394564033067943 119128392551091846049601915)
    ·
      refine ⟨178692588826637769074402873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119128392551091846049601915 178692588826637769074402873)
      ·
        refine ⟨134019441619978326805802155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 178692588826637769074402873 134019441619978326805802155)
        ·
          refine ⟨201029162429967490208703233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 134019441619978326805802155 201029162429967490208703233)
          ·
            refine ⟨150771871822475617656527425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 201029162429967490208703233 150771871822475617656527425)
            ·
              refine ⟨113078903866856713242395569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 150771871822475617656527425 113078903866856713242395569)
              ·
                refine ⟨84809177900142534931796677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 113078903866856713242395569 84809177900142534931796677)
                ·
                  refine ⟨15901720856276725299711877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 84809177900142534931796677 15901720856276725299711877)
                  ·
                    refine ⟨2981572660551885993695977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15901720856276725299711877 2981572660551885993695977)
                    ·
                      refine ⟨2236179495413914495271983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2981572660551885993695977 2236179495413914495271983)
                      ·
                        rfl

theorem cell23_4354944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 2, 4, 4, 2].length) (baseStart_4354944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4354944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4354944 prefixEnd_4354944 := by exact prefixLift 4354944
  have htrace : WordTrace (prefixWord ++ tailWord_4354944) baseStart_4354944 baseEnd_4354944 := by
    simpa [prefixWord, tailWord_4354944, baseEnd_4354944] using wordTrace_append hprefix tailTrace_4354944
  have hstable : (prefixWord ++ tailWord_4354944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4354944).length < 2 ^ (prefixWord ++ tailWord_4354944).sum := by decide
  have hdescent : baseEnd_4354944 < baseStart_4354944 := by decide
  rcases family_descends (prefixWord ++ tailWord_4354944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4354967 : List Nat := [1, 1, 3, 3, 1, 2, 1, 3, 8]
def baseStart_4354967 : Nat := 118140960795 + 4354967 * 2 ^ 59
def prefixEnd_4354967 : Nat := 4983230072969 + 3 ^ 40 * 4354967 * 2
def baseEnd_4354967 : Nat := 248465700607663100587153

theorem tailTrace_4354967 : CollatzResearch.WordTrace tailWord_4354967 prefixEnd_4354967 248465700607663100587153 := by
  unfold tailWord_4354967
  simp only [CollatzResearch.WordTrace]
  refine ⟨158838695613705802994223155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105892463742470535329482103 158838695613705802994223155)
  ·
    refine ⟨238258043420558704491334733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158838695613705802994223155 238258043420558704491334733)
    ·
      refine ⟨89346766282709514184250525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 238258043420558704491334733 89346766282709514184250525)
      ·
        refine ⟨33505037356016067819093947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 89346766282709514184250525 33505037356016067819093947)
        ·
          refine ⟨50257556034024101728640921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33505037356016067819093947 50257556034024101728640921)
          ·
            refine ⟨37693167025518076296480691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50257556034024101728640921 37693167025518076296480691)
            ·
              refine ⟨56539750538277114444721037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37693167025518076296480691 56539750538277114444721037)
              ·
                refine ⟨21202406451853917916770389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56539750538277114444721037 21202406451853917916770389)
                ·
                  refine ⟨248465700607663100587153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 21202406451853917916770389 248465700607663100587153)
                  ·
                    rfl

theorem cell23_4354967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 3, 8].length) (baseStart_4354967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4354967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4354967 prefixEnd_4354967 := by exact prefixLift 4354967
  have htrace : WordTrace (prefixWord ++ tailWord_4354967) baseStart_4354967 baseEnd_4354967 := by
    simpa [prefixWord, tailWord_4354967, baseEnd_4354967] using wordTrace_append hprefix tailTrace_4354967
  have hstable : (prefixWord ++ tailWord_4354967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4354967).length < 2 ^ (prefixWord ++ tailWord_4354967).sum := by decide
  have hdescent : baseEnd_4354967 < baseStart_4354967 := by decide
  rcases family_descends (prefixWord ++ tailWord_4354967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4355007 : List Nat := [1, 1, 2, 2, 2, 1, 2, 1, 2, 4, 5]
def baseStart_4355007 : Nat := 118140960795 + 4355007 * 2 ^ 59
def prefixEnd_4355007 : Nat := 4983230072969 + 3 ^ 40 * 4355007 * 2
def baseEnd_4355007 : Nat := 2236211844695147748784193

theorem tailTrace_4355007 : CollatzResearch.WordTrace tailWord_4355007 prefixEnd_4355007 2236211844695147748784193 := by
  unfold tailWord_4355007
  simp only [CollatzResearch.WordTrace]
  refine ⟨158840154533560889825679275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105893436355707259883786183 158840154533560889825679275)
  ·
    refine ⟨238260231800341334738518913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158840154533560889825679275 238260231800341334738518913)
    ·
      refine ⟨178695173850256001053889185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 238260231800341334738518913 178695173850256001053889185)
      ·
        refine ⟨134021380387692000790416889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 178695173850256001053889185 134021380387692000790416889)
        ·
          refine ⟨100516035290769000592812667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 134021380387692000790416889 100516035290769000592812667)
          ·
            refine ⟨150774052936153500889219001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100516035290769000592812667 150774052936153500889219001)
            ·
              refine ⟨113080539702115125666914251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 150774052936153500889219001 113080539702115125666914251)
              ·
                refine ⟨169620809553172688500371377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 113080539702115125666914251 169620809553172688500371377)
                ·
                  refine ⟨127215607164879516375278533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 169620809553172688500371377 127215607164879516375278533)
                  ·
                    refine ⟨23852926343414909320364725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 127215607164879516375278533 23852926343414909320364725)
                    ·
                      refine ⟨2236211844695147748784193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23852926343414909320364725 2236211844695147748784193)
                      ·
                        rfl

theorem cell23_4355007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 1, 2, 4, 5].length) (baseStart_4355007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4355007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4355007 prefixEnd_4355007 := by exact prefixLift 4355007
  have htrace : WordTrace (prefixWord ++ tailWord_4355007) baseStart_4355007 baseEnd_4355007 := by
    simpa [prefixWord, tailWord_4355007, baseEnd_4355007] using wordTrace_append hprefix tailTrace_4355007
  have hstable : (prefixWord ++ tailWord_4355007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4355007).length < 2 ^ (prefixWord ++ tailWord_4355007).sum := by decide
  have hdescent : baseEnd_4355007 < baseStart_4355007 := by decide
  rcases family_descends (prefixWord ++ tailWord_4355007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4355045 : List Nat := [1, 3, 1, 6, 1, 1, 1, 2, 3, 1, 3]
def baseStart_4355045 : Nat := 118140960795 + 4355045 * 2 ^ 59
def prefixEnd_4355045 : Nat := 4983230072969 + 3 ^ 40 * 4355045 * 2
def baseEnd_4355045 : Nat := 2236231356960018600109019

theorem tailTrace_4355045 : CollatzResearch.WordTrace tailWord_4355045 prefixEnd_4355045 2236231356960018600109019 := by
  unfold tailWord_4355045
  simp only [CollatzResearch.WordTrace]
  refine ⟨158841540507423222315562589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105894360338282148210375059 158841540507423222315562589)
  ·
    refine ⟨59565577690283708368335971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 158841540507423222315562589 59565577690283708368335971)
    ·
      refine ⟨89348366535425562552503957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59565577690283708368335971 89348366535425562552503957)
      ·
        refine ⟨4188204681348073244648623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 89348366535425562552503957 4188204681348073244648623)
        ·
          refine ⟨6282307022022109866972935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4188204681348073244648623 6282307022022109866972935)
          ·
            refine ⟨9423460533033164800459403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6282307022022109866972935 9423460533033164800459403)
            ·
              refine ⟨14135190799549747200689105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9423460533033164800459403 14135190799549747200689105)
              ·
                refine ⟨10601393099662310400516829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14135190799549747200689105 10601393099662310400516829)
                ·
                  refine ⟨3975522412373366400193811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10601393099662310400516829 3975522412373366400193811)
                  ·
                    refine ⟨5963283618560049600290717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3975522412373366400193811 5963283618560049600290717)
                    ·
                      refine ⟨2236231356960018600109019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5963283618560049600290717 2236231356960018600109019)
                      ·
                        rfl

theorem cell23_4355045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 1, 2, 3, 1, 3].length) (baseStart_4355045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4355045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4355045 prefixEnd_4355045 := by exact prefixLift 4355045
  have htrace : WordTrace (prefixWord ++ tailWord_4355045) baseStart_4355045 baseEnd_4355045 := by
    simpa [prefixWord, tailWord_4355045, baseEnd_4355045] using wordTrace_append hprefix tailTrace_4355045
  have hstable : (prefixWord ++ tailWord_4355045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4355045).length < 2 ^ (prefixWord ++ tailWord_4355045).sum := by decide
  have hdescent : baseEnd_4355045 < baseStart_4355045 := by decide
  rcases family_descends (prefixWord ++ tailWord_4355045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4355062 : List Nat := [5, 1, 1, 1, 3, 2, 2, 3, 1, 1, 3]
def baseStart_4355062 : Nat := 118140960795 + 4355062 * 2 ^ 59
def prefixEnd_4355062 : Nat := 4983230072969 + 3 ^ 40 * 4355062 * 2
def baseEnd_4355062 : Nat := 2236240086131145033596441

theorem tailTrace_4355062 : CollatzResearch.WordTrace tailWord_4355062 prefixEnd_4355062 2236240086131145033596441 := by
  unfold tailWord_4355062
  simp only [CollatzResearch.WordTrace]
  refine ⟨9927635034272602138683215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 105894773698907756145954293 9927635034272602138683215)
  ·
    refine ⟨14891452551408903208024823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9927635034272602138683215 14891452551408903208024823)
    ·
      refine ⟨22337178827113354812037235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14891452551408903208024823 22337178827113354812037235)
      ·
        refine ⟨33505768240670032218055853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22337178827113354812037235 33505768240670032218055853)
        ·
          refine ⟨12564663090251262081770945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33505768240670032218055853 12564663090251262081770945)
          ·
            refine ⟨9423497317688446561328209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12564663090251262081770945 9423497317688446561328209)
            ·
              refine ⟨7067622988266334920996157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9423497317688446561328209 7067622988266334920996157)
              ·
                refine ⟨2650358620599875595373559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7067622988266334920996157 2650358620599875595373559)
                ·
                  refine ⟨3975537930899813393060339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2650358620599875595373559 3975537930899813393060339)
                  ·
                    refine ⟨5963306896349720089590509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3975537930899813393060339 5963306896349720089590509)
                    ·
                      refine ⟨2236240086131145033596441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5963306896349720089590509 2236240086131145033596441)
                      ·
                        rfl

theorem cell23_4355062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 2, 3, 1, 1, 3].length) (baseStart_4355062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4355062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4355062 prefixEnd_4355062 := by exact prefixLift 4355062
  have htrace : WordTrace (prefixWord ++ tailWord_4355062) baseStart_4355062 baseEnd_4355062 := by
    simpa [prefixWord, tailWord_4355062, baseEnd_4355062] using wordTrace_append hprefix tailTrace_4355062
  have hstable : (prefixWord ++ tailWord_4355062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4355062).length < 2 ^ (prefixWord ++ tailWord_4355062).sum := by decide
  have hdescent : baseEnd_4355062 < baseStart_4355062 := by decide
  rcases family_descends (prefixWord ++ tailWord_4355062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4355068 : List Nat := [2, 2, 2, 1, 2, 3, 4, 1, 1, 1, 4]
def baseStart_4355068 : Nat := 118140960795 + 4355068 * 2 ^ 59
def prefixEnd_4355068 : Nat := 4983230072969 + 3 ^ 40 * 4355068 * 2
def baseEnd_4355068 : Nat := 2236243167015072010121413

theorem tailTrace_4355068 : CollatzResearch.WordTrace tailWord_4355068 prefixEnd_4355068 2236243167015072010121413 := by
  unfold tailWord_4355068
  simp only [CollatzResearch.WordTrace]
  refine ⟨79421189693169948621824929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105894919590893264829099905 79421189693169948621824929)
  ·
    refine ⟨59565892269877461466368697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79421189693169948621824929 59565892269877461466368697)
    ·
      refine ⟨44674419202408096099776523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59565892269877461466368697 44674419202408096099776523)
      ·
        refine ⟨67011628803612144149664785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44674419202408096099776523 67011628803612144149664785)
        ·
          refine ⟨50258721602709108112248589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67011628803612144149664785 50258721602709108112248589)
          ·
            refine ⟨18847020601015915542093221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50258721602709108112248589 18847020601015915542093221)
            ·
              refine ⟨3533816362690484164142479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18847020601015915542093221 3533816362690484164142479)
              ·
                refine ⟨5300724544035726246213719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3533816362690484164142479 5300724544035726246213719)
                ·
                  refine ⟨7951086816053589369320579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5300724544035726246213719 7951086816053589369320579)
                  ·
                    refine ⟨11926630224080384053980869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7951086816053589369320579 11926630224080384053980869)
                    ·
                      refine ⟨2236243167015072010121413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11926630224080384053980869 2236243167015072010121413)
                      ·
                        rfl

theorem cell23_4355068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 4, 1, 1, 1, 4].length) (baseStart_4355068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4355068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4355068 prefixEnd_4355068 := by exact prefixLift 4355068
  have htrace : WordTrace (prefixWord ++ tailWord_4355068) baseStart_4355068 baseEnd_4355068 := by
    simpa [prefixWord, tailWord_4355068, baseEnd_4355068] using wordTrace_append hprefix tailTrace_4355068
  have hstable : (prefixWord ++ tailWord_4355068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4355068).length < 2 ^ (prefixWord ++ tailWord_4355068).sum := by decide
  have hdescent : baseEnd_4355068 < baseStart_4355068 := by decide
  rcases family_descends (prefixWord ++ tailWord_4355068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4355095 : List Nat := [1, 1, 3, 5, 1, 2, 3, 1, 2, 4]
def baseStart_4355095 : Nat := 118140960795 + 4355095 * 2 ^ 59
def prefixEnd_4355095 : Nat := 4983230072969 + 3 ^ 40 * 4355095 * 2
def baseEnd_4355095 : Nat := 745419010330914468161263

theorem tailTrace_4355095 : CollatzResearch.WordTrace tailWord_4355095 prefixEnd_4355095 745419010330914468161263 := by
  unfold tailWord_4355095
  simp only [CollatzResearch.WordTrace]
  refine ⟨158843364157242080854882739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105895576104828053903255159 158843364157242080854882739)
  ·
    refine ⟨238265046235863121282324109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158843364157242080854882739 238265046235863121282324109)
    ·
      refine ⟨89349392338448670480871541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 238265046235863121282324109 89349392338448670480871541)
      ·
        refine ⟨8376505531729562857581707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 89349392338448670480871541 8376505531729562857581707)
        ·
          refine ⟨12564758297594344286372561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8376505531729562857581707 12564758297594344286372561)
          ·
            refine ⟨9423568723195758214779421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12564758297594344286372561 9423568723195758214779421)
            ·
              refine ⟨3533838271198409330542283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9423568723195758214779421 3533838271198409330542283)
              ·
                refine ⟨5300757406797613995813425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3533838271198409330542283 5300757406797613995813425)
                ·
                  refine ⟨3975568055098210496860069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5300757406797613995813425 3975568055098210496860069)
                  ·
                    refine ⟨745419010330914468161263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3975568055098210496860069 745419010330914468161263)
                    ·
                      rfl

theorem cell23_4355095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 3, 1, 2, 4].length) (baseStart_4355095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4355095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4355095 prefixEnd_4355095 := by exact prefixLift 4355095
  have htrace : WordTrace (prefixWord ++ tailWord_4355095) baseStart_4355095 baseEnd_4355095 := by
    simpa [prefixWord, tailWord_4355095, baseEnd_4355095] using wordTrace_append hprefix tailTrace_4355095
  have hstable : (prefixWord ++ tailWord_4355095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4355095).length < 2 ^ (prefixWord ++ tailWord_4355095).sum := by decide
  have hdescent : baseEnd_4355095 < baseStart_4355095 := by decide
  rcases family_descends (prefixWord ++ tailWord_4355095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4355108 : List Nat := [2, 3, 1, 4, 1, 3, 2, 7]
def baseStart_4355108 : Nat := 118140960795 + 4355108 * 2 ^ 59
def prefixEnd_4355108 : Nat := 4983230072969 + 3 ^ 40 * 4355108 * 2
def baseEnd_4355108 : Nat := 82824581712638957541527

theorem tailTrace_4355108 : CollatzResearch.WordTrace tailWord_4355108 prefixEnd_4355108 82824581712638957541527 := by
  unfold tailWord_4355108
  simp only [CollatzResearch.WordTrace]
  refine ⟨79421919153097492037552989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105895892204129989383403985 79421919153097492037552989)
  ·
    refine ⟨29783219682411559514082371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79421919153097492037552989 29783219682411559514082371)
    ·
      refine ⟨44674829523617339271123557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29783219682411559514082371 44674829523617339271123557)
      ·
        refine ⟨8376530535678251113335667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 44674829523617339271123557 8376530535678251113335667)
        ·
          refine ⟨12564795803517376670003501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8376530535678251113335667 12564795803517376670003501)
          ·
            refine ⟨4711798426319016251251313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12564795803517376670003501 4711798426319016251251313)
            ·
              refine ⟨3533848819739262188438485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4711798426319016251251313 3533848819739262188438485)
              ·
                refine ⟨82824581712638957541527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3533848819739262188438485 82824581712638957541527)
                ·
                  rfl

theorem cell23_4355108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 3, 2, 7].length) (baseStart_4355108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4355108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4355108 prefixEnd_4355108 := by exact prefixLift 4355108
  have htrace : WordTrace (prefixWord ++ tailWord_4355108) baseStart_4355108 baseEnd_4355108 := by
    simpa [prefixWord, tailWord_4355108, baseEnd_4355108] using wordTrace_append hprefix tailTrace_4355108
  have hstable : (prefixWord ++ tailWord_4355108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4355108).length < 2 ^ (prefixWord ++ tailWord_4355108).sum := by decide
  have hdescent : baseEnd_4355108 < baseStart_4355108 := by decide
  rcases family_descends (prefixWord ++ tailWord_4355108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4355118 : List Nat := [4, 1, 3, 1, 1, 1, 1, 1, 6, 1, 3]
def baseStart_4355118 : Nat := 118140960795 + 4355118 * 2 ^ 59
def prefixEnd_4355118 : Nat := 4983230072969 + 3 ^ 40 * 4355118 * 2
def baseEnd_4355118 : Nat := 2236268841047796814496183

theorem tailTrace_4355118 : CollatzResearch.WordTrace tailWord_4355118 prefixEnd_4355118 2236268841047796814496183 := by
  unfold tailWord_4355118
  simp only [CollatzResearch.WordTrace]
  refine ⟨19855525379519844472871251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 105896135357439170521980005 19855525379519844472871251)
  ·
    refine ⟨29783288069279766709306877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19855525379519844472871251 29783288069279766709306877)
    ·
      refine ⟨11168733025979912515990079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29783288069279766709306877 11168733025979912515990079)
      ·
        refine ⟨16753099538969868773985119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11168733025979912515990079 16753099538969868773985119)
        ·
          refine ⟨25129649308454803160977679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16753099538969868773985119 25129649308454803160977679)
          ·
            refine ⟨37694473962682204741466519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25129649308454803160977679 37694473962682204741466519)
            ·
              refine ⟨56541710944023307112199779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37694473962682204741466519 56541710944023307112199779)
              ·
                refine ⟨84812566416034960668299669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56541710944023307112199779 84812566416034960668299669)
                ·
                  refine ⟨3975589050751638781326547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 84812566416034960668299669 3975589050751638781326547)
                  ·
                    refine ⟨5963383576127458171989821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3975589050751638781326547 5963383576127458171989821)
                    ·
                      refine ⟨2236268841047796814496183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5963383576127458171989821 2236268841047796814496183)
                      ·
                        rfl

theorem cell23_4355118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 1, 6, 1, 3].length) (baseStart_4355118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4355118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4355118 prefixEnd_4355118 := by exact prefixLift 4355118
  have htrace : WordTrace (prefixWord ++ tailWord_4355118) baseStart_4355118 baseEnd_4355118 := by
    simpa [prefixWord, tailWord_4355118, baseEnd_4355118] using wordTrace_append hprefix tailTrace_4355118
  have hstable : (prefixWord ++ tailWord_4355118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4355118).length < 2 ^ (prefixWord ++ tailWord_4355118).sum := by decide
  have hdescent : baseEnd_4355118 < baseStart_4355118 := by decide
  rcases family_descends (prefixWord ++ tailWord_4355118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4355144 : List Nat := [2, 1, 3, 1, 1, 1, 3, 2, 1, 3, 5]
def baseStart_4355144 : Nat := 118140960795 + 4355144 * 2 ^ 59
def prefixEnd_4355144 : Nat := 4983230072969 + 3 ^ 40 * 4355144 * 2
def baseEnd_4355144 : Nat := 2236282191544813712771063

theorem tailTrace_4355144 : CollatzResearch.WordTrace tailWord_4355144 prefixEnd_4355144 2236282191544813712771063 := by
  unfold tailWord_4355144
  simp only [CollatzResearch.WordTrace]
  refine ⟨79422575667032281111708243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105896767556043041482277657 79422575667032281111708243)
  ·
    refine ⟨119133863500548421667562365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79422575667032281111708243 119133863500548421667562365)
    ·
      refine ⟨44675198812705658125335887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 119133863500548421667562365 44675198812705658125335887)
      ·
        refine ⟨67012798219058487188003831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44675198812705658125335887 67012798219058487188003831)
        ·
          refine ⟨100519197328587730782005747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67012798219058487188003831 100519197328587730782005747)
          ·
            refine ⟨150778795992881596173008621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100519197328587730782005747 150778795992881596173008621)
            ·
              refine ⟨56542048497330598564878233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 150778795992881596173008621 56542048497330598564878233)
              ·
                refine ⟨42406536372997948923658675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56542048497330598564878233 42406536372997948923658675)
                ·
                  refine ⟨63609804559496923385488013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42406536372997948923658675 63609804559496923385488013)
                  ·
                    refine ⟨23853676709811346269558005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 63609804559496923385488013 23853676709811346269558005)
                    ·
                      refine ⟨2236282191544813712771063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23853676709811346269558005 2236282191544813712771063)
                      ·
                        rfl

theorem cell23_4355144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 2, 1, 3, 5].length) (baseStart_4355144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4355144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4355144 prefixEnd_4355144 := by exact prefixLift 4355144
  have htrace : WordTrace (prefixWord ++ tailWord_4355144) baseStart_4355144 baseEnd_4355144 := by
    simpa [prefixWord, tailWord_4355144, baseEnd_4355144] using wordTrace_append hprefix tailTrace_4355144
  have hstable : (prefixWord ++ tailWord_4355144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4355144).length < 2 ^ (prefixWord ++ tailWord_4355144).sum := by decide
  have hdescent : baseEnd_4355144 < baseStart_4355144 := by decide
  rcases family_descends (prefixWord ++ tailWord_4355144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4355191 : List Nat := [1, 1, 3, 1, 1, 4, 2, 2, 2, 3, 3]
def baseStart_4355191 : Nat := 118140960795 + 4355191 * 2 ^ 59
def prefixEnd_4355191 : Nat := 4983230072969 + 3 ^ 40 * 4355191 * 2
def baseEnd_4355191 : Nat := 2236306325135575028883347

theorem tailTrace_4355191 : CollatzResearch.WordTrace tailWord_4355191 prefixEnd_4355191 2236306325135575028883347 := by
  unfold tailWord_4355191
  simp only [CollatzResearch.WordTrace]
  refine ⟨158846865564894289250377427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105897910376596192833584951 158846865564894289250377427)
  ·
    refine ⟨238270298347341433875566141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158846865564894289250377427 238270298347341433875566141)
    ·
      refine ⟨89351361880253037703337303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 238270298347341433875566141 89351361880253037703337303)
      ·
        refine ⟨134027042820379556555005955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89351361880253037703337303 134027042820379556555005955)
        ·
          refine ⟨201040564230569334832508933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 134027042820379556555005955 201040564230569334832508933)
          ·
            refine ⟨37695105793231750281095425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 201040564230569334832508933 37695105793231750281095425)
            ·
              refine ⟨28271329344923812710821569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37695105793231750281095425 28271329344923812710821569)
              ·
                refine ⟨21203497008692859533116177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28271329344923812710821569 21203497008692859533116177)
                ·
                  refine ⟨15902622756519644649837133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21203497008692859533116177 15902622756519644649837133)
                  ·
                    refine ⟨5963483533694866743688925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15902622756519644649837133 5963483533694866743688925)
                    ·
                      refine ⟨2236306325135575028883347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5963483533694866743688925 2236306325135575028883347)
                      ·
                        rfl

theorem cell23_4355191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 2, 2, 3, 3].length) (baseStart_4355191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4355191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4355191 prefixEnd_4355191 := by exact prefixLift 4355191
  have htrace : WordTrace (prefixWord ++ tailWord_4355191) baseStart_4355191 baseEnd_4355191 := by
    simpa [prefixWord, tailWord_4355191, baseEnd_4355191] using wordTrace_append hprefix tailTrace_4355191
  have hstable : (prefixWord ++ tailWord_4355191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4355191).length < 2 ^ (prefixWord ++ tailWord_4355191).sum := by decide
  have hdescent : baseEnd_4355191 < baseStart_4355191 := by decide
  rcases family_descends (prefixWord ++ tailWord_4355191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4355228 : List Nat := [2, 2, 3, 2, 1, 2, 3, 1, 2, 5]
def baseStart_4355228 : Nat := 118140960795 + 4355228 * 2 ^ 59
def prefixEnd_4355228 : Nat := 4983230072969 + 3 ^ 40 * 4355228 * 2
def baseEnd_4355228 : Nat := 745441774639930461373559

theorem tailTrace_4355228 : CollatzResearch.WordTrace tailWord_4355228 prefixEnd_4355228 745441774639930461373559 := by
  unfold tailWord_4355228
  simp only [CollatzResearch.WordTrace]
  refine ⟨79424107532880122284737169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105898810043840163046316225 79424107532880122284737169)
  ·
    refine ⟨59568080649660091713552877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79424107532880122284737169 59568080649660091713552877)
    ·
      refine ⟨22338030243622534392582329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59568080649660091713552877 22338030243622534392582329)
      ·
        refine ⟨16753522682716900794436747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22338030243622534392582329 16753522682716900794436747)
        ·
          refine ⟨25130284024075351191655121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16753522682716900794436747 25130284024075351191655121)
          ·
            refine ⟨18847713018056513393741341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25130284024075351191655121 18847713018056513393741341)
            ·
              refine ⟨7067892381771192522653003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18847713018056513393741341 7067892381771192522653003)
              ·
                refine ⟨10601838572656788783979505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7067892381771192522653003 10601838572656788783979505)
                ·
                  refine ⟨7951378929492591587984629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10601838572656788783979505 7951378929492591587984629)
                  ·
                    refine ⟨745441774639930461373559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7951378929492591587984629 745441774639930461373559)
                    ·
                      rfl

theorem cell23_4355228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 3, 1, 2, 5].length) (baseStart_4355228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4355228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4355228 prefixEnd_4355228 := by exact prefixLift 4355228
  have htrace : WordTrace (prefixWord ++ tailWord_4355228) baseStart_4355228 baseEnd_4355228 := by
    simpa [prefixWord, tailWord_4355228, baseEnd_4355228] using wordTrace_append hprefix tailTrace_4355228
  have hstable : (prefixWord ++ tailWord_4355228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4355228).length < 2 ^ (prefixWord ++ tailWord_4355228).sum := by decide
  have hdescent : baseEnd_4355228 < baseStart_4355228 := by decide
  rcases family_descends (prefixWord ++ tailWord_4355228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4355271 : List Nat := [1, 1, 4, 1, 1, 1, 1, 7, 6]
def baseStart_4355271 : Nat := 118140960795 + 4355271 * 2 ^ 59
def prefixEnd_4355271 : Nat := 4983230072969 + 3 ^ 40 * 4355271 * 2
def baseEnd_4355271 : Nat := 248483044843103857320331

theorem tailTrace_4355271 : CollatzResearch.WordTrace tailWord_4355271 prefixEnd_4355271 248483044843103857320331 := by
  unfold tailWord_4355271
  simp only [CollatzResearch.WordTrace]
  refine ⟨158849783404604462913289667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105899855603069641942193111 158849783404604462913289667)
  ·
    refine ⟨238274675106906694369934501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158849783404604462913289667 238274675106906694369934501)
    ·
      refine ⟨44676501582545005194362719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 238274675106906694369934501 44676501582545005194362719)
      ·
        refine ⟨67014752373817507791544079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44676501582545005194362719 67014752373817507791544079)
        ·
          refine ⟨100522128560726261687316119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67014752373817507791544079 100522128560726261687316119)
          ·
            refine ⟨150783192841089392530974179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100522128560726261687316119 150783192841089392530974179)
            ·
              refine ⟨226174789261634088796461269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 150783192841089392530974179 226174789261634088796461269)
              ·
                refine ⟨5300971623319548956167061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 226174789261634088796461269 5300971623319548956167061)
                ·
                  refine ⟨248483044843103857320331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5300971623319548956167061 248483044843103857320331)
                  ·
                    rfl

theorem cell23_4355271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 7, 6].length) (baseStart_4355271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4355271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4355271 prefixEnd_4355271 := by exact prefixLift 4355271
  have htrace : WordTrace (prefixWord ++ tailWord_4355271) baseStart_4355271 baseEnd_4355271 := by
    simpa [prefixWord, tailWord_4355271, baseEnd_4355271] using wordTrace_append hprefix tailTrace_4355271
  have hstable : (prefixWord ++ tailWord_4355271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4355271).length < 2 ^ (prefixWord ++ tailWord_4355271).sum := by decide
  have hdescent : baseEnd_4355271 < baseStart_4355271 := by decide
  rcases family_descends (prefixWord ++ tailWord_4355271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4355281 : List Nat := [1, 2, 2, 1, 2, 2, 1, 1, 1, 7, 3]
def baseStart_4355281 : Nat := 118140960795 + 4355281 * 2 ^ 59
def prefixEnd_4355281 : Nat := 4983230072969 + 3 ^ 40 * 4355281 * 2
def baseEnd_4355281 : Nat := 2236352538394479676757933

theorem tailTrace_4355281 : CollatzResearch.WordTrace tailWord_4355281 prefixEnd_4355281 2236352538394479676757933 := by
  unfold tailWord_4355281
  simp only [CollatzResearch.WordTrace]
  refine ⟨158850148134568234621153697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105900098756378823080769131 158850148134568234621153697)
  ·
    refine ⟨119137611100926175965865273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 158850148134568234621153697 119137611100926175965865273)
    ·
      refine ⟨89353208325694631974398955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119137611100926175965865273 89353208325694631974398955)
      ·
        refine ⟨134029812488541947961598433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89353208325694631974398955 134029812488541947961598433)
        ·
          refine ⟨100522359366406460971198825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 134029812488541947961598433 100522359366406460971198825)
          ·
            refine ⟨75391769524804845728399119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 100522359366406460971198825 75391769524804845728399119)
            ·
              refine ⟨113087654287207268592598679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75391769524804845728399119 113087654287207268592598679)
              ·
                refine ⟨169631481430810902888898019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 113087654287207268592598679 169631481430810902888898019)
                ·
                  refine ⟨254447222146216354333347029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 169631481430810902888898019 254447222146216354333347029)
                  ·
                    refine ⟨5963606769051945804687821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 254447222146216354333347029 5963606769051945804687821)
                    ·
                      refine ⟨2236352538394479676757933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5963606769051945804687821 2236352538394479676757933)
                      ·
                        rfl

theorem cell23_4355281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 1, 1, 7, 3].length) (baseStart_4355281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4355281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4355281 prefixEnd_4355281 := by exact prefixLift 4355281
  have htrace : WordTrace (prefixWord ++ tailWord_4355281) baseStart_4355281 baseEnd_4355281 := by
    simpa [prefixWord, tailWord_4355281, baseEnd_4355281] using wordTrace_append hprefix tailTrace_4355281
  have hstable : (prefixWord ++ tailWord_4355281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4355281).length < 2 ^ (prefixWord ++ tailWord_4355281).sum := by decide
  have hdescent : baseEnd_4355281 < baseStart_4355281 := by decide
  rcases family_descends (prefixWord ++ tailWord_4355281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4355309 : List Nat := [1, 5, 1, 2, 2, 2, 3, 2, 1, 4]
def baseStart_4355309 : Nat := 118140960795 + 4355309 * 2 ^ 59
def prefixEnd_4355309 : Nat := 4983230072969 + 3 ^ 40 * 4355309 * 2
def baseEnd_4355309 : Nat := 745455638617601855735935

theorem tailTrace_4355309 : CollatzResearch.WordTrace tailWord_4355309 prefixEnd_4355309 745455638617601855735935 := by
  unfold tailWord_4355309
  simp only [CollatzResearch.WordTrace]
  refine ⟨158851169378466795403172981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105900779585644530268781987 158851169378466795403172981)
  ·
    refine ⟨14892297129231262069047467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 158851169378466795403172981 14892297129231262069047467)
    ·
      refine ⟨22338445693846893103571201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14892297129231262069047467 22338445693846893103571201)
      ·
        refine ⟨16753834270385169827678401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22338445693846893103571201 16753834270385169827678401)
        ·
          refine ⟨12565375702788877370758801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16753834270385169827678401 12565375702788877370758801)
          ·
            refine ⟨9424031777091658028069101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12565375702788877370758801 9424031777091658028069101)
            ·
              refine ⟨3534011916409371760525913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9424031777091658028069101 3534011916409371760525913)
              ·
                refine ⟨2650508937307028820394435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3534011916409371760525913 2650508937307028820394435)
                ·
                  refine ⟨3975763405960543230591653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2650508937307028820394435 3975763405960543230591653)
                  ·
                    refine ⟨745455638617601855735935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3975763405960543230591653 745455638617601855735935)
                    ·
                      rfl

theorem cell23_4355309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 3, 2, 1, 4].length) (baseStart_4355309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4355309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4355309 prefixEnd_4355309 := by exact prefixLift 4355309
  have htrace : WordTrace (prefixWord ++ tailWord_4355309) baseStart_4355309 baseEnd_4355309 := by
    simpa [prefixWord, tailWord_4355309, baseEnd_4355309] using wordTrace_append hprefix tailTrace_4355309
  have hstable : (prefixWord ++ tailWord_4355309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4355309).length < 2 ^ (prefixWord ++ tailWord_4355309).sum := by decide
  have hdescent : baseEnd_4355309 < baseStart_4355309 := by decide
  rcases family_descends (prefixWord ++ tailWord_4355309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4355315 : List Nat := [1, 1, 1, 2, 2, 5, 3, 1, 3, 1, 3]
def baseStart_4355315 : Nat := 118140960795 + 4355315 * 2 ^ 59
def prefixEnd_4355315 : Nat := 4983230072969 + 3 ^ 40 * 4355315 * 2
def baseEnd_4355315 : Nat := 2236369996736732543732777

theorem tailTrace_4355315 : CollatzResearch.WordTrace tailWord_4355315 prefixEnd_4355315 2236369996736732543732777 := by
  unfold tailWord_4355315
  simp only [CollatzResearch.WordTrace]
  refine ⟨158851388216445058427891399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105900925477630038951927599 158851388216445058427891399)
  ·
    refine ⟨238277082324667587641837099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158851388216445058427891399 238277082324667587641837099)
    ·
      refine ⟨357415623487001381462755649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 238277082324667587641837099 357415623487001381462755649)
      ·
        refine ⟨268061717615251036097066737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 357415623487001381462755649 268061717615251036097066737)
        ·
          refine ⟨201046288211438277072800053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 268061717615251036097066737 201046288211438277072800053)
          ·
            refine ⟨18848089519822338475575005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 201046288211438277072800053 18848089519822338475575005)
            ·
              refine ⟨7068033569933376928340627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18848089519822338475575005 7068033569933376928340627)
              ·
                refine ⟨10602050354900065392510941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7068033569933376928340627 10602050354900065392510941)
                ·
                  refine ⟨3975768883087524522191603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10602050354900065392510941 3975768883087524522191603)
                  ·
                    refine ⟨5963653324631286783287405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3975768883087524522191603 5963653324631286783287405)
                    ·
                      refine ⟨2236369996736732543732777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5963653324631286783287405 2236369996736732543732777)
                      ·
                        rfl

theorem cell23_4355315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 3, 1, 3, 1, 3].length) (baseStart_4355315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4355315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4355315 prefixEnd_4355315 := by exact prefixLift 4355315
  have htrace : WordTrace (prefixWord ++ tailWord_4355315) baseStart_4355315 baseEnd_4355315 := by
    simpa [prefixWord, tailWord_4355315, baseEnd_4355315] using wordTrace_append hprefix tailTrace_4355315
  have hstable : (prefixWord ++ tailWord_4355315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4355315).length < 2 ^ (prefixWord ++ tailWord_4355315).sum := by decide
  have hdescent : baseEnd_4355315 < baseStart_4355315 := by decide
  rcases family_descends (prefixWord ++ tailWord_4355315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4355318 : List Nat := [5, 1, 1, 1, 1, 1, 1, 4, 3, 5]
def baseStart_4355318 : Nat := 118140960795 + 4355318 * 2 ^ 59
def prefixEnd_4355318 : Nat := 4983230072969 + 3 ^ 40 * 4355318 * 2
def baseEnd_4355318 : Nat := 745457179059565343998421

theorem tailTrace_4355318 : CollatzResearch.WordTrace tailWord_4355318 prefixEnd_4355318 745457179059565343998421 := by
  unfold tailWord_4355318
  simp only [CollatzResearch.WordTrace]
  refine ⟨9928218602214636871265663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 105900998423622793293500405 9928218602214636871265663)
  ·
    refine ⟨14892327903321955306898495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9928218602214636871265663 14892327903321955306898495)
    ·
      refine ⟨22338491854982932960347743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14892327903321955306898495 22338491854982932960347743)
      ·
        refine ⟨33507737782474399440521615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22338491854982932960347743 33507737782474399440521615)
        ·
          refine ⟨50261606673711599160782423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33507737782474399440521615 50261606673711599160782423)
          ·
            refine ⟨75392410010567398741173635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50261606673711599160782423 75392410010567398741173635)
            ·
              refine ⟨113088615015851098111760453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75392410010567398741173635 113088615015851098111760453)
              ·
                refine ⟨21204115315472080895955085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 113088615015851098111760453 21204115315472080895955085)
                ·
                  refine ⟨7951543243302030335983157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21204115315472080895955085 7951543243302030335983157)
                  ·
                    refine ⟨745457179059565343998421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7951543243302030335983157 745457179059565343998421)
                    ·
                      rfl

theorem cell23_4355318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 4, 3, 5].length) (baseStart_4355318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4355318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4355318 prefixEnd_4355318 := by exact prefixLift 4355318
  have htrace : WordTrace (prefixWord ++ tailWord_4355318) baseStart_4355318 baseEnd_4355318 := by
    simpa [prefixWord, tailWord_4355318, baseEnd_4355318] using wordTrace_append hprefix tailTrace_4355318
  have hstable : (prefixWord ++ tailWord_4355318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4355318).length < 2 ^ (prefixWord ++ tailWord_4355318).sum := by decide
  have hdescent : baseEnd_4355318 < baseStart_4355318 := by decide
  rcases family_descends (prefixWord ++ tailWord_4355318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4355342 : List Nat := [4, 1, 1, 2, 1, 4, 2, 1, 2, 3, 2]
def baseStart_4355342 : Nat := 118140960795 + 4355342 * 2 ^ 59
def prefixEnd_4355342 : Nat := 4983230072969 + 3 ^ 40 * 4355342 * 2
def baseEnd_4355342 : Nat := 2236383860714403938095153

theorem tailTrace_4355342 : CollatzResearch.WordTrace tailWord_4355342 prefixEnd_4355342 2236383860714403938095153 := by
  unfold tailWord_4355342
  simp only [CollatzResearch.WordTrace]
  refine ⟨19856546623418405254890535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 105901581991564828026082853 19856546623418405254890535)
  ·
    refine ⟨29784819935127607882335803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19856546623418405254890535 29784819935127607882335803)
    ·
      refine ⟨44677229902691411823503705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29784819935127607882335803 44677229902691411823503705)
      ·
        refine ⟨33507922427018558867627779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44677229902691411823503705 33507922427018558867627779)
        ·
          refine ⟨50261883640527838301441669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33507922427018558867627779 50261883640527838301441669)
          ·
            refine ⟨9424103182598969681520313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 50261883640527838301441669 9424103182598969681520313)
            ·
              refine ⟨7068077386949227261140235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9424103182598969681520313 7068077386949227261140235)
              ·
                refine ⟨10602116080423840891710353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7068077386949227261140235 10602116080423840891710353)
                ·
                  refine ⟨7951587060317880668782765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10602116080423840891710353 7951587060317880668782765)
                  ·
                    refine ⟨2981845147619205250793537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7951587060317880668782765 2981845147619205250793537)
                    ·
                      refine ⟨2236383860714403938095153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2981845147619205250793537 2236383860714403938095153)
                      ·
                        rfl

theorem cell23_4355342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 2, 1, 2, 3, 2].length) (baseStart_4355342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4355342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4355342 prefixEnd_4355342 := by exact prefixLift 4355342
  have htrace : WordTrace (prefixWord ++ tailWord_4355342) baseStart_4355342 baseEnd_4355342 := by
    simpa [prefixWord, tailWord_4355342, baseEnd_4355342] using wordTrace_append hprefix tailTrace_4355342
  have hstable : (prefixWord ++ tailWord_4355342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4355342).length < 2 ^ (prefixWord ++ tailWord_4355342).sum := by decide
  have hdescent : baseEnd_4355342 < baseStart_4355342 := by decide
  rcases family_descends (prefixWord ++ tailWord_4355342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4355365 : List Nat := [1, 3, 1, 2, 4, 1, 1, 4, 2, 4]
def baseStart_4355365 : Nat := 118140960795 + 4355365 * 2 ^ 59
def prefixEnd_4355365 : Nat := 4983230072969 + 3 ^ 40 * 4355365 * 2
def baseEnd_4355365 : Nat := 745465223589819116035849

theorem tailTrace_4355365 : CollatzResearch.WordTrace tailWord_4355365 prefixEnd_4355365 745465223589819116035849 := by
  unfold tailWord_4355365
  simp only [CollatzResearch.WordTrace]
  refine ⟨158853211866263916967211549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105902141244175944644807699 158853211866263916967211549)
  ·
    refine ⟨59569954449848968862704331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 158853211866263916967211549 59569954449848968862704331)
    ·
      refine ⟨89354931674773453294056497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59569954449848968862704331 89354931674773453294056497)
      ·
        refine ⟨67016198756080089970542373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89354931674773453294056497 67016198756080089970542373)
        ·
          refine ⟨12565537266765016869476695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 67016198756080089970542373 12565537266765016869476695)
          ·
            refine ⟨18848305900147525304215043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12565537266765016869476695 18848305900147525304215043)
            ·
              refine ⟨28272458850221287956322565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18848305900147525304215043 28272458850221287956322565)
              ·
                refine ⟨5301086034416491491810481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28272458850221287956322565 5301086034416491491810481)
                ·
                  refine ⟨3975814525812368618857861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5301086034416491491810481 3975814525812368618857861)
                  ·
                    refine ⟨745465223589819116035849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3975814525812368618857861 745465223589819116035849)
                    ·
                      rfl

theorem cell23_4355365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 4, 2, 4].length) (baseStart_4355365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4355365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4355365 prefixEnd_4355365 := by exact prefixLift 4355365
  have htrace : WordTrace (prefixWord ++ tailWord_4355365) baseStart_4355365 baseEnd_4355365 := by
    simpa [prefixWord, tailWord_4355365, baseEnd_4355365] using wordTrace_append hprefix tailTrace_4355365
  have hstable : (prefixWord ++ tailWord_4355365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4355365).length < 2 ^ (prefixWord ++ tailWord_4355365).sum := by decide
  have hdescent : baseEnd_4355365 < baseStart_4355365 := by decide
  rcases family_descends (prefixWord ++ tailWord_4355365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4355378 : List Nat := [3, 2, 1, 1, 4, 1, 3, 8]
def baseStart_4355378 : Nat := 118140960795 + 4355378 * 2 ^ 59
def prefixEnd_4355378 : Nat := 4983230072969 + 3 ^ 40 * 4355378 * 2
def baseEnd_4355378 : Nat := 82829716519183918416481

theorem tailTrace_4355378 : CollatzResearch.WordTrace tailWord_4355378 prefixEnd_4355378 82829716519183918416481 := by
  unfold tailWord_4355378
  simp only [CollatzResearch.WordTrace]
  refine ⟨39713421503804205046858697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105902457343477880124956525 39713421503804205046858697)
  ·
    refine ⟨29785066127853153785144023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39713421503804205046858697 29785066127853153785144023)
    ·
      refine ⟨44677599191779730677716035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29785066127853153785144023 44677599191779730677716035)
      ·
        refine ⟨67016398787669596016574053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44677599191779730677716035 67016398787669596016574053)
        ·
          refine ⟨12565574772688049253107635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 67016398787669596016574053 12565574772688049253107635)
          ·
            refine ⟨18848362159032073879661453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12565574772688049253107635 18848362159032073879661453)
            ·
              refine ⟨7068135809637027704873045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18848362159032073879661453 7068135809637027704873045)
              ·
                refine ⟨82829716519183918416481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7068135809637027704873045 82829716519183918416481)
                ·
                  rfl

theorem cell23_4355378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 3, 8].length) (baseStart_4355378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4355378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4355378 prefixEnd_4355378 := by exact prefixLift 4355378
  have htrace : WordTrace (prefixWord ++ tailWord_4355378) baseStart_4355378 baseEnd_4355378 := by
    simpa [prefixWord, tailWord_4355378, baseEnd_4355378] using wordTrace_append hprefix tailTrace_4355378
  have hstable : (prefixWord ++ tailWord_4355378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4355378).length < 2 ^ (prefixWord ++ tailWord_4355378).sum := by decide
  have hdescent : baseEnd_4355378 < baseStart_4355378 := by decide
  rcases family_descends (prefixWord ++ tailWord_4355378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4355465 : List Nat := [1, 2, 1, 1, 7, 1, 1, 1, 2, 1, 5]
def baseStart_4355465 : Nat := 118140960795 + 4355465 * 2 ^ 59
def prefixEnd_4355465 : Nat := 4983230072969 + 3 ^ 40 * 4355465 * 2
def baseEnd_4355465 : Nat := 2236447018834906956857087

theorem tailTrace_4355465 : CollatzResearch.WordTrace tailWord_4355465 prefixEnd_4355465 2236447018834906956857087 := by
  unfold tailWord_4355465
  simp only [CollatzResearch.WordTrace]
  refine ⟨158856859165901634045851849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105904572777267756030567899 158856859165901634045851849)
  ·
    refine ⟨119142644374426225534388887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 158856859165901634045851849 119142644374426225534388887)
    ·
      refine ⟨178713966561639338301583331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119142644374426225534388887 178713966561639338301583331)
      ·
        refine ⟨268070949842459007452374997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 178713966561639338301583331 268070949842459007452374997)
        ·
          refine ⟨6282912886932632987165039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 268070949842459007452374997 6282912886932632987165039)
          ·
            refine ⟨9424369330398949480747559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6282912886932632987165039 9424369330398949480747559)
            ·
              refine ⟨14136553995598424221121339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9424369330398949480747559 14136553995598424221121339)
              ·
                refine ⟨21204830993397636331682009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14136553995598424221121339 21204830993397636331682009)
                ·
                  refine ⟨15903623245048227248761507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21204830993397636331682009 15903623245048227248761507)
                  ·
                    refine ⟨23855434867572340873142261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15903623245048227248761507 23855434867572340873142261)
                    ·
                      refine ⟨2236447018834906956857087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23855434867572340873142261 2236447018834906956857087)
                      ·
                        rfl

theorem cell23_4355465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 1, 1, 2, 1, 5].length) (baseStart_4355465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4355465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4355465 prefixEnd_4355465 := by exact prefixLift 4355465
  have htrace : WordTrace (prefixWord ++ tailWord_4355465) baseStart_4355465 baseEnd_4355465 := by
    simpa [prefixWord, tailWord_4355465, baseEnd_4355465] using wordTrace_append hprefix tailTrace_4355465
  have hstable : (prefixWord ++ tailWord_4355465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4355465).length < 2 ^ (prefixWord ++ tailWord_4355465).sum := by decide
  have hdescent : baseEnd_4355465 < baseStart_4355465 := by decide
  rcases family_descends (prefixWord ++ tailWord_4355465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4355485 : List Nat := [1, 4, 2, 1, 3, 1, 3, 1, 7]
def baseStart_4355485 : Nat := 118140960795 + 4355485 * 2 ^ 59
def prefixEnd_4355485 : Nat := 4983230072969 + 3 ^ 40 * 4355485 * 2
def baseEnd_4355485 : Nat := 248495254271999653178555

theorem tailTrace_4355485 : CollatzResearch.WordTrace tailWord_4355485 prefixEnd_4355485 248495254271999653178555 := by
  unfold tailWord_4355485
  simp only [CollatzResearch.WordTrace]
  refine ⟨158857588625829177461579909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105905059083886118307719939 158857588625829177461579909)
  ·
    refine ⟨29785797867342970774046233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 158857588625829177461579909 29785797867342970774046233)
    ·
      refine ⟨22339348400507228080534675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29785797867342970774046233 22339348400507228080534675)
      ·
        refine ⟨33509022600760842120802013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22339348400507228080534675 33509022600760842120802013)
        ·
          refine ⟨12565883475285315795300755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33509022600760842120802013 12565883475285315795300755)
          ·
            refine ⟨18848825212927973692951133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12565883475285315795300755 18848825212927973692951133)
            ·
              refine ⟨7068309454847990134856675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18848825212927973692951133 7068309454847990134856675)
              ·
                refine ⟨10602464182271985202285013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7068309454847990134856675 10602464182271985202285013)
                ·
                  refine ⟨248495254271999653178555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10602464182271985202285013 248495254271999653178555)
                  ·
                    rfl

theorem cell23_4355485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 3, 1, 7].length) (baseStart_4355485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4355485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4355485 prefixEnd_4355485 := by exact prefixLift 4355485
  have htrace : WordTrace (prefixWord ++ tailWord_4355485) baseStart_4355485 baseEnd_4355485 := by
    simpa [prefixWord, tailWord_4355485, baseEnd_4355485] using wordTrace_append hprefix tailTrace_4355485
  have hstable : (prefixWord ++ tailWord_4355485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4355485).length < 2 ^ (prefixWord ++ tailWord_4355485).sum := by decide
  have hdescent : baseEnd_4355485 < baseStart_4355485 := by decide
  rcases family_descends (prefixWord ++ tailWord_4355485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4355495 : List Nat := [1, 1, 6, 1, 1, 1, 2, 1, 1, 5, 3]
def baseStart_4355495 : Nat := 118140960795 + 4355495 * 2 ^ 59
def prefixEnd_4355495 : Nat := 4983230072969 + 3 ^ 40 * 4355495 * 2
def baseEnd_4355495 : Nat := 2236462423254541839481949

theorem tailTrace_4355495 : CollatzResearch.WordTrace tailWord_4355495 prefixEnd_4355495 2236462423254541839481949 := by
  unfold tailWord_4355495
  simp only [CollatzResearch.WordTrace]
  refine ⟨158857953355792949169443939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105905302237195299446295959 158857953355792949169443939)
  ·
    refine ⟨238286930033689423754165909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158857953355792949169443939 238286930033689423754165909)
    ·
      refine ⟨11169699845329191738476527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 238286930033689423754165909 11169699845329191738476527)
      ·
        refine ⟨16754549767993787607714791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11169699845329191738476527 16754549767993787607714791)
        ·
          refine ⟨25131824651990681411572187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16754549767993787607714791 25131824651990681411572187)
          ·
            refine ⟨37697736977986022117358281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25131824651990681411572187 37697736977986022117358281)
            ·
              refine ⟨28273302733489516588018711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37697736977986022117358281 28273302733489516588018711)
              ·
                refine ⟨42409954100234274882028067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28273302733489516588018711 42409954100234274882028067)
                ·
                  refine ⟨63614931150351412323042101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42409954100234274882028067 63614931150351412323042101)
                  ·
                    refine ⟨5963899795345444905285197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 63614931150351412323042101 5963899795345444905285197)
                    ·
                      refine ⟨2236462423254541839481949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5963899795345444905285197 2236462423254541839481949)
                      ·
                        rfl

theorem cell23_4355495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 1, 1, 5, 3].length) (baseStart_4355495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4355495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4355495 prefixEnd_4355495 := by exact prefixLift 4355495
  have htrace : WordTrace (prefixWord ++ tailWord_4355495) baseStart_4355495 baseEnd_4355495 := by
    simpa [prefixWord, tailWord_4355495, baseEnd_4355495] using wordTrace_append hprefix tailTrace_4355495
  have hstable : (prefixWord ++ tailWord_4355495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4355495).length < 2 ^ (prefixWord ++ tailWord_4355495).sum := by decide
  have hdescent : baseEnd_4355495 < baseStart_4355495 := by decide
  rcases family_descends (prefixWord ++ tailWord_4355495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4355535 : List Nat := [1, 1, 2, 1, 1, 4, 4, 2, 2, 1, 4]
def baseStart_4355535 : Nat := 118140960795 + 4355535 * 2 ^ 59
def prefixEnd_4355535 : Nat := 4983230072969 + 3 ^ 40 * 4355535 * 2
def baseEnd_4355535 : Nat := 2236482962480721682981765

theorem tailTrace_4355535 : CollatzResearch.WordTrace tailWord_4355535 prefixEnd_4355535 2236482962480721682981765 := by
  unfold tailWord_4355535
  simp only [CollatzResearch.WordTrace]
  refine ⟨158859412275648036000900059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105906274850432024000600039 158859412275648036000900059)
  ·
    refine ⟨238289118413472054001350089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158859412275648036000900059 238289118413472054001350089)
    ·
      refine ⟨178716838810104040501012567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 238289118413472054001350089 178716838810104040501012567)
      ·
        refine ⟨268075258215156060751518851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 178716838810104040501012567 268075258215156060751518851)
        ·
          refine ⟨402112887322734091127278277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 268075258215156060751518851 402112887322734091127278277)
          ·
            refine ⟨75396166373012642086364677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 402112887322734091127278277 75396166373012642086364677)
            ·
              refine ⟨14136781194939870391193377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 75396166373012642086364677 14136781194939870391193377)
              ·
                refine ⟨10602585896204902793395033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14136781194939870391193377 10602585896204902793395033)
                ·
                  refine ⟨7951939422153677095046275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10602585896204902793395033 7951939422153677095046275)
                  ·
                    refine ⟨11927909133230515642569413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7951939422153677095046275 11927909133230515642569413)
                    ·
                      refine ⟨2236482962480721682981765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11927909133230515642569413 2236482962480721682981765)
                      ·
                        rfl

theorem cell23_4355535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 4, 2, 2, 1, 4].length) (baseStart_4355535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4355535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4355535 prefixEnd_4355535 := by exact prefixLift 4355535
  have htrace : WordTrace (prefixWord ++ tailWord_4355535) baseStart_4355535 baseEnd_4355535 := by
    simpa [prefixWord, tailWord_4355535, baseEnd_4355535] using wordTrace_append hprefix tailTrace_4355535
  have hstable : (prefixWord ++ tailWord_4355535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4355535).length < 2 ^ (prefixWord ++ tailWord_4355535).sum := by decide
  have hdescent : baseEnd_4355535 < baseStart_4355535 := by decide
  rcases family_descends (prefixWord ++ tailWord_4355535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4355542 : List Nat := [5, 2, 1, 1, 1, 2, 2, 1, 1, 2, 5]
def baseStart_4355542 : Nat := 118140960795 + 4355542 * 2 ^ 59
def prefixEnd_4355542 : Nat := 4983230072969 + 3 ^ 40 * 4355542 * 2
def baseEnd_4355542 : Nat := 2236486556845303155594233

theorem tailTrace_4355542 : CollatzResearch.WordTrace tailWord_4355542 prefixEnd_4355542 2236486556845303155594233 := by
  unfold tailWord_4355542
  simp only [CollatzResearch.WordTrace]
  refine ⟨9928729224163917262275305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 105906445057748450797603253 9928729224163917262275305)
  ·
    refine ⟨7446546918122937946706479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9928729224163917262275305 7446546918122937946706479)
    ·
      refine ⟨11169820377184406920059719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7446546918122937946706479 11169820377184406920059719)
      ·
        refine ⟨16754730565776610380089579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11169820377184406920059719 16754730565776610380089579)
        ·
          refine ⟨25132095848664915570134369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16754730565776610380089579 25132095848664915570134369)
          ·
            refine ⟨18849071886498686677600777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25132095848664915570134369 18849071886498686677600777)
            ·
              refine ⟨14136803914874015008200583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18849071886498686677600777 14136803914874015008200583)
              ·
                refine ⟨21205205872311022512300875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14136803914874015008200583 21205205872311022512300875)
                ·
                  refine ⟨31807808808466533768451313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21205205872311022512300875 31807808808466533768451313)
                  ·
                    refine ⟨23855856606349900326338485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 31807808808466533768451313 23855856606349900326338485)
                    ·
                      refine ⟨2236486556845303155594233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23855856606349900326338485 2236486556845303155594233)
                      ·
                        rfl

theorem cell23_4355542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 2, 1, 1, 2, 5].length) (baseStart_4355542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4355542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4355542 prefixEnd_4355542 := by exact prefixLift 4355542
  have htrace : WordTrace (prefixWord ++ tailWord_4355542) baseStart_4355542 baseEnd_4355542 := by
    simpa [prefixWord, tailWord_4355542, baseEnd_4355542] using wordTrace_append hprefix tailTrace_4355542
  have hstable : (prefixWord ++ tailWord_4355542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4355542).length < 2 ^ (prefixWord ++ tailWord_4355542).sum := by decide
  have hdescent : baseEnd_4355542 < baseStart_4355542 := by decide
  rcases family_descends (prefixWord ++ tailWord_4355542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4355612 : List Nat := [2, 2, 3, 1, 2, 1, 1, 1, 3, 5, 2]
def baseStart_4355612 : Nat := 118140960795 + 4355612 * 2 ^ 59
def prefixEnd_4355612 : Nat := 4983230072969 + 3 ^ 40 * 4355612 * 2
def baseEnd_4355612 : Nat := 2236522500491117881718911

theorem tailTrace_4355612 : CollatzResearch.WordTrace tailWord_4355612 prefixEnd_4355612 2236522500491117881718911 := by
  unfold tailWord_4355612
  simp only [CollatzResearch.WordTrace]
  refine ⟨79431110348184539075726545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105908147130912718767635393 79431110348184539075726545)
  ·
    refine ⟨59573332761138404306794909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79431110348184539075726545 59573332761138404306794909)
    ·
      refine ⟨22339999785426901615048091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59573332761138404306794909 22339999785426901615048091)
      ·
        refine ⟨33509999678140352422572137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22339999785426901615048091 33509999678140352422572137)
        ·
          refine ⟨25132499758605264316929103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33509999678140352422572137 25132499758605264316929103)
          ·
            refine ⟨37698749637907896475393655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25132499758605264316929103 37698749637907896475393655)
            ·
              refine ⟨56548124456861844713090483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37698749637907896475393655 56548124456861844713090483)
              ·
                refine ⟨84822186685292767069635725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56548124456861844713090483 84822186685292767069635725)
                ·
                  refine ⟨31808320006984787651113397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 84822186685292767069635725 31808320006984787651113397)
                  ·
                    refine ⟨2982030000654823842291881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 31808320006984787651113397 2982030000654823842291881)
                    ·
                      refine ⟨2236522500491117881718911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2982030000654823842291881 2236522500491117881718911)
                      ·
                        rfl

theorem cell23_4355612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 1, 3, 5, 2].length) (baseStart_4355612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4355612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4355612 prefixEnd_4355612 := by exact prefixLift 4355612
  have htrace : WordTrace (prefixWord ++ tailWord_4355612) baseStart_4355612 baseEnd_4355612 := by
    simpa [prefixWord, tailWord_4355612, baseEnd_4355612] using wordTrace_append hprefix tailTrace_4355612
  have hstable : (prefixWord ++ tailWord_4355612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4355612).length < 2 ^ (prefixWord ++ tailWord_4355612).sum := by decide
  have hdescent : baseEnd_4355612 < baseStart_4355612 := by decide
  rcases family_descends (prefixWord ++ tailWord_4355612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4355642 : List Nat := [3, 1, 1, 1, 3, 2, 1, 5, 1, 1, 4]
def baseStart_4355642 : Nat := 118140960795 + 4355642 * 2 ^ 59
def prefixEnd_4355642 : Nat := 4983230072969 + 3 ^ 40 * 4355642 * 2
def baseEnd_4355642 : Nat := 2236537904910752764343773

theorem tailTrace_4355642 : CollatzResearch.WordTrace tailWord_4355642 prefixEnd_4355642 2236537904910752764343773 := by
  unfold tailWord_4355642
  simp only [CollatzResearch.WordTrace]
  refine ⟨39715828721565098318761295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105908876590840262183363453 39715828721565098318761295)
  ·
    refine ⟨59573743082347647478141943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39715828721565098318761295 59573743082347647478141943)
    ·
      refine ⟨89360614623521471217212915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59573743082347647478141943 89360614623521471217212915)
      ·
        refine ⟨134040921935282206825819373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89360614623521471217212915 134040921935282206825819373)
        ·
          refine ⟨50265345725730827559682265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 134040921935282206825819373 50265345725730827559682265)
          ·
            refine ⟨37699009294298120669761699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50265345725730827559682265 37699009294298120669761699)
            ·
              refine ⟨56548513941447181004642549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37699009294298120669761699 56548513941447181004642549)
              ·
                refine ⟨5301423182010673219185239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 56548513941447181004642549 5301423182010673219185239)
                ·
                  refine ⟨7952134773016009828777859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5301423182010673219185239 7952134773016009828777859)
                  ·
                    refine ⟨11928202159524014743166789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7952134773016009828777859 11928202159524014743166789)
                    ·
                      refine ⟨2236537904910752764343773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11928202159524014743166789 2236537904910752764343773)
                      ·
                        rfl

theorem cell23_4355642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 5, 1, 1, 4].length) (baseStart_4355642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4355642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4355642 prefixEnd_4355642 := by exact prefixLift 4355642
  have htrace : WordTrace (prefixWord ++ tailWord_4355642) baseStart_4355642 baseEnd_4355642 := by
    simpa [prefixWord, tailWord_4355642, baseEnd_4355642] using wordTrace_append hprefix tailTrace_4355642
  have hstable : (prefixWord ++ tailWord_4355642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4355642).length < 2 ^ (prefixWord ++ tailWord_4355642).sum := by decide
  have hdescent : baseEnd_4355642 < baseStart_4355642 := by decide
  rcases family_descends (prefixWord ++ tailWord_4355642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4355662 : List Nat := [4, 1, 1, 1, 1, 2, 1, 4, 3, 2, 3]
def baseStart_4355662 : Nat := 118140960795 + 4355662 * 2 ^ 59
def prefixEnd_4355662 : Nat := 4983230072969 + 3 ^ 40 * 4355662 * 2
def baseEnd_4355662 : Nat := 2236548174523842686093681

theorem tailTrace_4355662 : CollatzResearch.WordTrace tailWord_4355662 prefixEnd_4355662 2236548174523842686093681 := by
  unfold tailWord_4355662
  simp only [CollatzResearch.WordTrace]
  refine ⟨19858005543273492086346655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 105909362897458624460515493 19858005543273492086346655)
  ·
    refine ⟨29787008314910238129519983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19858005543273492086346655 29787008314910238129519983)
    ·
      refine ⟨44680512472365357194279975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29787008314910238129519983 44680512472365357194279975)
      ·
        refine ⟨67020768708548035791419963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44680512472365357194279975 67020768708548035791419963)
        ·
          refine ⟨100531153062822053687129945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67020768708548035791419963 100531153062822053687129945)
          ·
            refine ⟨75398364797116540265347459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 100531153062822053687129945 75398364797116540265347459)
            ·
              refine ⟨113097547195674810398021189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75398364797116540265347459 113097547195674810398021189)
              ·
                refine ⟨21205790099189026949628973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 113097547195674810398021189 21205790099189026949628973)
                ·
                  refine ⟨7952171287195885106110865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21205790099189026949628973 7952171287195885106110865)
                  ·
                    refine ⟨5964128465396913829583149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7952171287195885106110865 5964128465396913829583149)
                    ·
                      refine ⟨2236548174523842686093681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5964128465396913829583149 2236548174523842686093681)
                      ·
                        rfl

theorem cell23_4355662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 4, 3, 2, 3].length) (baseStart_4355662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4355662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4355662 prefixEnd_4355662 := by exact prefixLift 4355662
  have htrace : WordTrace (prefixWord ++ tailWord_4355662) baseStart_4355662 baseEnd_4355662 := by
    simpa [prefixWord, tailWord_4355662, baseEnd_4355662] using wordTrace_append hprefix tailTrace_4355662
  have hstable : (prefixWord ++ tailWord_4355662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4355662).length < 2 ^ (prefixWord ++ tailWord_4355662).sum := by decide
  have hdescent : baseEnd_4355662 < baseStart_4355662 := by decide
  rcases family_descends (prefixWord ++ tailWord_4355662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4355665 : List Nat := [1, 2, 2, 1, 3, 2, 4, 8]
def baseStart_4355665 : Nat := 118140960795 + 4355665 * 2 ^ 59
def prefixEnd_4355665 : Nat := 4983230072969 + 3 ^ 40 * 4355665 * 2
def baseEnd_4355665 : Nat := 82835174628363191642821

theorem tailTrace_4355665 : CollatzResearch.WordTrace tailWord_4355665 prefixEnd_4355665 82835174628363191642821 := by
  unfold tailWord_4355665
  simp only [CollatzResearch.WordTrace]
  refine ⟨158864153765177068203132449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105909435843451378802088299 158864153765177068203132449)
  ·
    refine ⟨119148115323882801152349337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 158864153765177068203132449 119148115323882801152349337)
    ·
      refine ⟨89361086492912100864262003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119148115323882801152349337 89361086492912100864262003)
      ·
        refine ⟨134041629739368151296393005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89361086492912100864262003 134041629739368151296393005)
        ·
          refine ⟨50265611152263056736147377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 134041629739368151296393005 50265611152263056736147377)
          ·
            refine ⟨37699208364197292552110533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50265611152263056736147377 37699208364197292552110533)
            ·
              refine ⟨7068601568286992353520725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37699208364197292552110533 7068601568286992353520725)
              ·
                refine ⟨82835174628363191642821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7068601568286992353520725 82835174628363191642821)
                ·
                  rfl

theorem cell23_4355665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 4, 8].length) (baseStart_4355665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4355665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4355665 prefixEnd_4355665 := by exact prefixLift 4355665
  have htrace : WordTrace (prefixWord ++ tailWord_4355665) baseStart_4355665 baseEnd_4355665 := by
    simpa [prefixWord, tailWord_4355665, baseEnd_4355665] using wordTrace_append hprefix tailTrace_4355665
  have hstable : (prefixWord ++ tailWord_4355665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4355665).length < 2 ^ (prefixWord ++ tailWord_4355665).sum := by decide
  have hdescent : baseEnd_4355665 < baseStart_4355665 := by decide
  rcases family_descends (prefixWord ++ tailWord_4355665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4355676 : List Nat := [2, 2, 4, 1, 2, 3, 1, 2, 1, 1, 4]
def baseStart_4355676 : Nat := 118140960795 + 4355676 * 2 ^ 59
def prefixEnd_4355676 : Nat := 4983230072969 + 3 ^ 40 * 4355676 * 2
def baseEnd_4355676 : Nat := 2236555363253005631318617

theorem tailTrace_4355676 : CollatzResearch.WordTrace tailWord_4355676 prefixEnd_4355676 2236555363253005631318617 := by
  unfold tailWord_4355676
  simp only [CollatzResearch.WordTrace]
  refine ⟨79432277484068608540891441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105909703312091478054521921 79432277484068608540891441)
  ·
    refine ⟨59574208113051456405668581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79432277484068608540891441 59574208113051456405668581)
    ·
      refine ⟨11170164021197148076062859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 59574208113051456405668581 11170164021197148076062859)
      ·
        refine ⟨16755246031795722114094289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11170164021197148076062859 16755246031795722114094289)
        ·
          refine ⟨12566434523846791585570717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16755246031795722114094289 12566434523846791585570717)
          ·
            refine ⟨4712412946442546844589019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12566434523846791585570717 4712412946442546844589019)
            ·
              refine ⟨7068619419663820266883529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4712412946442546844589019 7068619419663820266883529)
              ·
                refine ⟨5301464564747865200162647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7068619419663820266883529 5301464564747865200162647)
                ·
                  refine ⟨7952196847121797800243971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5301464564747865200162647 7952196847121797800243971)
                  ·
                    refine ⟨11928295270682696700365957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7952196847121797800243971 11928295270682696700365957)
                    ·
                      refine ⟨2236555363253005631318617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11928295270682696700365957 2236555363253005631318617)
                      ·
                        rfl

theorem cell23_4355676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 3, 1, 2, 1, 1, 4].length) (baseStart_4355676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4355676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4355676 prefixEnd_4355676 := by exact prefixLift 4355676
  have htrace : WordTrace (prefixWord ++ tailWord_4355676) baseStart_4355676 baseEnd_4355676 := by
    simpa [prefixWord, tailWord_4355676, baseEnd_4355676] using wordTrace_append hprefix tailTrace_4355676
  have hstable : (prefixWord ++ tailWord_4355676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4355676).length < 2 ^ (prefixWord ++ tailWord_4355676).sum := by decide
  have hdescent : baseEnd_4355676 < baseStart_4355676 := by decide
  rcases family_descends (prefixWord ++ tailWord_4355676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4355696 : List Nat := [2, 1, 1, 1, 6, 2, 3, 1, 1, 2, 3]
def baseStart_4355696 : Nat := 118140960795 + 4355696 * 2 ^ 59
def prefixEnd_4355696 : Nat := 4983230072969 + 3 ^ 40 * 4355696 * 2
def baseEnd_4355696 : Nat := 2236565632866095553068525

theorem tailTrace_4355696 : CollatzResearch.WordTrace tailWord_4355696 prefixEnd_4355696 2236565632866095553068525 := by
  unfold tailWord_4355696
  simp only [CollatzResearch.WordTrace]
  refine ⟨79432642214032380248755471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105910189618709840331673961 79432642214032380248755471)
  ·
    refine ⟨119148963321048570373133207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79432642214032380248755471 119148963321048570373133207)
    ·
      refine ⟨178723444981572855559699811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119148963321048570373133207 178723444981572855559699811)
      ·
        refine ⟨268085167472359283339549717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 178723444981572855559699811 268085167472359283339549717)
        ·
          refine ⟨12566492225266841406541393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 268085167472359283339549717 12566492225266841406541393)
          ·
            refine ⟨9424869168950131054906045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12566492225266841406541393 9424869168950131054906045)
            ·
              refine ⟨3534325938356299145589767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9424869168950131054906045 3534325938356299145589767)
              ·
                refine ⟨5301488907534448718384651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3534325938356299145589767 5301488907534448718384651)
                ·
                  refine ⟨7952233361301673077576977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5301488907534448718384651 7952233361301673077576977)
                  ·
                    refine ⟨5964175020976254808182733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7952233361301673077576977 5964175020976254808182733)
                    ·
                      refine ⟨2236565632866095553068525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5964175020976254808182733 2236565632866095553068525)
                      ·
                        rfl

theorem cell23_4355696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 3, 1, 1, 2, 3].length) (baseStart_4355696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4355696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4355696 prefixEnd_4355696 := by exact prefixLift 4355696
  have htrace : WordTrace (prefixWord ++ tailWord_4355696) baseStart_4355696 baseEnd_4355696 := by
    simpa [prefixWord, tailWord_4355696, baseEnd_4355696] using wordTrace_append hprefix tailTrace_4355696
  have hstable : (prefixWord ++ tailWord_4355696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4355696).length < 2 ^ (prefixWord ++ tailWord_4355696).sum := by decide
  have hdescent : baseEnd_4355696 < baseStart_4355696 := by decide
  rcases family_descends (prefixWord ++ tailWord_4355696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4355719 : List Nat := [1, 1, 4, 2, 1, 3, 1, 2, 3, 3, 2]
def baseStart_4355719 : Nat := 118140960795 + 4355719 * 2 ^ 59
def prefixEnd_4355719 : Nat := 4983230072969 + 3 ^ 40 * 4355719 * 2
def baseEnd_4355719 : Nat := 2236577442921148963080919

theorem tailTrace_4355719 : CollatzResearch.WordTrace tailWord_4355719 prefixEnd_4355719 2236577442921148963080919 := by
  unfold tailWord_4355719
  simp only [CollatzResearch.WordTrace]
  refine ⟨158866123306981435425598211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105910748871320956950398807 158866123306981435425598211)
  ·
    refine ⟨238299184960472153138397317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158866123306981435425598211 238299184960472153138397317)
    ·
      refine ⟨44681097180088528713449497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 238299184960472153138397317 44681097180088528713449497)
      ·
        refine ⟨33510822885066396535087123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44681097180088528713449497 33510822885066396535087123)
        ·
          refine ⟨50266234327599594802630685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33510822885066396535087123 50266234327599594802630685)
          ·
            refine ⟨18849837872849848050986507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50266234327599594802630685 18849837872849848050986507)
            ·
              refine ⟨28274756809274772076479761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18849837872849848050986507 28274756809274772076479761)
              ·
                refine ⟨21206067606956079057359821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28274756809274772076479761 21206067606956079057359821)
                ·
                  refine ⟨7952275352608529646509933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21206067606956079057359821 7952275352608529646509933)
                  ·
                    refine ⟨2982103257228198617441225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7952275352608529646509933 2982103257228198617441225)
                    ·
                      refine ⟨2236577442921148963080919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2982103257228198617441225 2236577442921148963080919)
                      ·
                        rfl

theorem cell23_4355719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 2, 3, 3, 2].length) (baseStart_4355719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4355719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4355719 prefixEnd_4355719 := by exact prefixLift 4355719
  have htrace : WordTrace (prefixWord ++ tailWord_4355719) baseStart_4355719 baseEnd_4355719 := by
    simpa [prefixWord, tailWord_4355719, baseEnd_4355719] using wordTrace_append hprefix tailTrace_4355719
  have hstable : (prefixWord ++ tailWord_4355719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4355719).length < 2 ^ (prefixWord ++ tailWord_4355719).sum := by decide
  have hdescent : baseEnd_4355719 < baseStart_4355719 := by decide
  rcases family_descends (prefixWord ++ tailWord_4355719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4355726 : List Nat := [4, 1, 1, 3, 1, 2, 2, 3, 2, 1, 3]
def baseStart_4355726 : Nat := 118140960795 + 4355726 * 2 ^ 59
def prefixEnd_4355726 : Nat := 4983230072969 + 3 ^ 40 * 4355726 * 2
def baseEnd_4355726 : Nat := 2236581037285730435693387

theorem tailTrace_4355726 : CollatzResearch.WordTrace tailWord_4355726 prefixEnd_4355726 2236581037285730435693387 := by
  unfold tailWord_4355726
  simp only [CollatzResearch.WordTrace]
  refine ⟨19858297327244509452637879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 105910919078637383747402021 19858297327244509452637879)
  ·
    refine ⟨29787445990866764178956819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19858297327244509452637879 29787445990866764178956819)
    ·
      refine ⟨44681168986300146268435229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29787445990866764178956819 44681168986300146268435229)
      ·
        refine ⟨16755438369862554850663211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44681168986300146268435229 16755438369862554850663211)
        ·
          refine ⟨25133157554793832275994817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16755438369862554850663211 25133157554793832275994817)
          ·
            refine ⟨18849868166095374206996113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25133157554793832275994817 18849868166095374206996113)
            ·
              refine ⟨14137401124571530655247085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18849868166095374206996113 14137401124571530655247085)
              ·
                refine ⟨5301525421714323995717657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14137401124571530655247085 5301525421714323995717657)
                ·
                  refine ⟨3976144066285742996788243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5301525421714323995717657 3976144066285742996788243)
                  ·
                    refine ⟨5964216099428614495182365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3976144066285742996788243 5964216099428614495182365)
                    ·
                      refine ⟨2236581037285730435693387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5964216099428614495182365 2236581037285730435693387)
                      ·
                        rfl

theorem cell23_4355726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 2, 3, 2, 1, 3].length) (baseStart_4355726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4355726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4355726 prefixEnd_4355726 := by exact prefixLift 4355726
  have htrace : WordTrace (prefixWord ++ tailWord_4355726) baseStart_4355726 baseEnd_4355726 := by
    simpa [prefixWord, tailWord_4355726, baseEnd_4355726] using wordTrace_append hprefix tailTrace_4355726
  have hstable : (prefixWord ++ tailWord_4355726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4355726).length < 2 ^ (prefixWord ++ tailWord_4355726).sum := by decide
  have hdescent : baseEnd_4355726 < baseStart_4355726 := by decide
  rcases family_descends (prefixWord ++ tailWord_4355726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4355749 : List Nat := [1, 3, 1, 2, 1, 2, 4, 2, 1, 4, 2]
def baseStart_4355749 : Nat := 118140960795 + 4355749 * 2 ^ 59
def prefixEnd_4355749 : Nat := 4983230072969 + 3 ^ 40 * 4355749 * 2
def baseEnd_4355749 : Nat := 2236592847340783845705781

theorem tailTrace_4355749 : CollatzResearch.WordTrace tailWord_4355749 prefixEnd_4355749 2236592847340783845705781 := by
  unfold tailWord_4355749
  simp only [CollatzResearch.WordTrace]
  refine ⟨158867217496872750549190301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105911478331248500366126867 158867217496872750549190301)
  ·
    refine ⟨59575206561327281455946363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 158867217496872750549190301 59575206561327281455946363)
    ·
      refine ⟨89362809841990922183919545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59575206561327281455946363 89362809841990922183919545)
      ·
        refine ⟨67022107381493191637939659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89362809841990922183919545 67022107381493191637939659)
        ·
          refine ⟨100533161072239787456909489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67022107381493191637939659 100533161072239787456909489)
          ·
            refine ⟨75399870804179840592682117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 100533161072239787456909489 75399870804179840592682117)
            ·
              refine ⟨14137475775783720111127897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 75399870804179840592682117 14137475775783720111127897)
              ·
                refine ⟨10603106831837790083345923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14137475775783720111127897 10603106831837790083345923)
                ·
                  refine ⟨15904660247756685125018885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10603106831837790083345923 15904660247756685125018885)
                  ·
                    refine ⟨2982123796454378460941041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15904660247756685125018885 2982123796454378460941041)
                    ·
                      refine ⟨2236592847340783845705781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2982123796454378460941041 2236592847340783845705781)
                      ·
                        rfl

theorem cell23_4355749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 4, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 4, 2, 1, 4, 2].length) (baseStart_4355749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4355749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4355749 prefixEnd_4355749 := by exact prefixLift 4355749
  have htrace : WordTrace (prefixWord ++ tailWord_4355749) baseStart_4355749 baseEnd_4355749 := by
    simpa [prefixWord, tailWord_4355749, baseEnd_4355749] using wordTrace_append hprefix tailTrace_4355749
  have hstable : (prefixWord ++ tailWord_4355749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4355749).length < 2 ^ (prefixWord ++ tailWord_4355749).sum := by decide
  have hdescent : baseEnd_4355749 < baseStart_4355749 := by decide
  rcases family_descends (prefixWord ++ tailWord_4355749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4355762 : List Nat := [3, 2, 1, 1, 1, 2, 3, 2, 2, 2, 4]
def baseStart_4355762 : Nat := 118140960795 + 4355762 * 2 ^ 59
def prefixEnd_4355762 : Nat := 4983230072969 + 3 ^ 40 * 4355762 * 2
def baseEnd_4355762 : Nat := 2236599522589292294843221

theorem tailTrace_4355762 : CollatzResearch.WordTrace tailWord_4355762 prefixEnd_4355762 2236599522589292294843221 := by
  unfold tailWord_4355762
  simp only [CollatzResearch.WordTrace]
  refine ⟨39716922911456413442353385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105911794430550435846275693 39716922911456413442353385)
  ·
    refine ⟨29787692183592310081765039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39716922911456413442353385 29787692183592310081765039)
    ·
      refine ⟨44681538275388465122647559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29787692183592310081765039 44681538275388465122647559)
      ·
        refine ⟨67022307413082697683971339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44681538275388465122647559 67022307413082697683971339)
        ·
          refine ⟨100533461119624046525957009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67022307413082697683971339 100533461119624046525957009)
          ·
            refine ⟨75400095839718034894467757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 100533461119624046525957009 75400095839718034894467757)
            ·
              refine ⟨28275035939894263085425409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 75400095839718034894467757 28275035939894263085425409)
              ·
                refine ⟨21206276954920697314069057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28275035939894263085425409 21206276954920697314069057)
                ·
                  refine ⟨15904707716190522985551793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21206276954920697314069057 15904707716190522985551793)
                  ·
                    refine ⟨11928530787142892239163845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15904707716190522985551793 11928530787142892239163845)
                    ·
                      refine ⟨2236599522589292294843221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11928530787142892239163845 2236599522589292294843221)
                      ·
                        rfl

theorem cell23_4355762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 2, 2, 2, 4].length) (baseStart_4355762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4355762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4355762 prefixEnd_4355762 := by exact prefixLift 4355762
  have htrace : WordTrace (prefixWord ++ tailWord_4355762) baseStart_4355762 baseEnd_4355762 := by
    simpa [prefixWord, tailWord_4355762, baseEnd_4355762] using wordTrace_append hprefix tailTrace_4355762
  have hstable : (prefixWord ++ tailWord_4355762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4355762).length < 2 ^ (prefixWord ++ tailWord_4355762).sum := by decide
  have hdescent : baseEnd_4355762 < baseStart_4355762 := by decide
  rcases family_descends (prefixWord ++ tailWord_4355762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4355772 : List Nat := [2, 2, 2, 3, 1, 2, 1, 3, 7]
def baseStart_4355772 : Nat := 118140960795 + 4355772 * 2 ^ 59
def prefixEnd_4355772 : Nat := 4983230072969 + 3 ^ 40 * 4355772 * 2
def baseEnd_4355772 : Nat := 248511628599537472857575

theorem tailTrace_4355772 : CollatzResearch.WordTrace tailWord_4355772 prefixEnd_4355772 248511628599537472857575 := by
  unfold tailWord_4355772
  simp only [CollatzResearch.WordTrace]
  refine ⟨79434028187894712738638785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105912037583859616984851713 79434028187894712738638785)
  ·
    refine ⟨59575521140921034553979089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79434028187894712738638785 59575521140921034553979089)
    ·
      refine ⟨44681640855690775915484317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59575521140921034553979089 44681640855690775915484317)
      ·
        refine ⟨16755615320884040968306619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44681640855690775915484317 16755615320884040968306619)
        ·
          refine ⟨25133422981326061452459929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16755615320884040968306619 25133422981326061452459929)
          ·
            refine ⟨18850067235994546089344947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25133422981326061452459929 18850067235994546089344947)
            ·
              refine ⟨28275100853991819134017421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18850067235994546089344947 28275100853991819134017421)
              ·
                refine ⟨10603162820246932175256533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28275100853991819134017421 10603162820246932175256533)
                ·
                  refine ⟨248511628599537472857575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10603162820246932175256533 248511628599537472857575)
                  ·
                    rfl

theorem cell23_4355772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 3, 7].length) (baseStart_4355772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4355772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4355772 prefixEnd_4355772 := by exact prefixLift 4355772
  have htrace : WordTrace (prefixWord ++ tailWord_4355772) baseStart_4355772 baseEnd_4355772 := by
    simpa [prefixWord, tailWord_4355772, baseEnd_4355772] using wordTrace_append hprefix tailTrace_4355772
  have hstable : (prefixWord ++ tailWord_4355772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4355772).length < 2 ^ (prefixWord ++ tailWord_4355772).sum := by decide
  have hdescent : baseEnd_4355772 < baseStart_4355772 := by decide
  rcases family_descends (prefixWord ++ tailWord_4355772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4355783 : List Nat := [1, 1, 4, 1, 1, 1, 7, 1, 2, 2, 2]
def baseStart_4355783 : Nat := 118140960795 + 4355783 * 2 ^ 59
def prefixEnd_4355783 : Nat := 4983230072969 + 3 ^ 40 * 4355783 * 2
def baseEnd_4355783 : Nat := 2236610305683036712680625

theorem tailTrace_4355783 : CollatzResearch.WordTrace tailWord_4355783 prefixEnd_4355783 2236610305683036712680625 := by
  unfold tailWord_4355783
  simp only [CollatzResearch.WordTrace]
  refine ⟨158868457578749574355928003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105912305052499716237285335 158868457578749574355928003)
  ·
    refine ⟨238302686368124361533892005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158868457578749574355928003 238302686368124361533892005)
    ·
      refine ⟨44681753694023317787604751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 238302686368124361533892005 44681753694023317787604751)
      ·
        refine ⟨67022630541034976681407127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44681753694023317787604751 67022630541034976681407127)
        ·
          refine ⟨100533945811552465022110691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67022630541034976681407127 100533945811552465022110691)
          ·
            refine ⟨150800918717328697533166037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100533945811552465022110691 150800918717328697533166037)
            ·
              refine ⟨3534396532437391348433579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 150800918717328697533166037 3534396532437391348433579)
              ·
                refine ⟨5301594798656087022650369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3534396532437391348433579 5301594798656087022650369)
                ·
                  refine ⟨3976196098992065266987777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5301594798656087022650369 3976196098992065266987777)
                  ·
                    refine ⟨2982147074244048950240833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3976196098992065266987777 2982147074244048950240833)
                    ·
                      refine ⟨2236610305683036712680625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2982147074244048950240833 2236610305683036712680625)
                      ·
                        rfl

theorem cell23_4355783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 7, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 7, 1, 2, 2, 2].length) (baseStart_4355783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4355783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4355783 prefixEnd_4355783 := by exact prefixLift 4355783
  have htrace : WordTrace (prefixWord ++ tailWord_4355783) baseStart_4355783 baseEnd_4355783 := by
    simpa [prefixWord, tailWord_4355783, baseEnd_4355783] using wordTrace_append hprefix tailTrace_4355783
  have hstable : (prefixWord ++ tailWord_4355783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4355783).length < 2 ^ (prefixWord ++ tailWord_4355783).sum := by decide
  have hdescent : baseEnd_4355783 < baseStart_4355783 := by decide
  rcases family_descends (prefixWord ++ tailWord_4355783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4355802 : List Nat := [3, 1, 1, 2, 2, 3, 2, 1, 1, 7]
def baseStart_4355802 : Nat := 118140960795 + 4355802 * 2 ^ 59
def prefixEnd_4355802 : Nat := 4983230072969 + 3 ^ 40 * 4355802 * 2
def baseEnd_4355802 : Nat := 745540020605157379447679

theorem tailTrace_4355802 : CollatzResearch.WordTrace tailWord_4355802 prefixEnd_4355802 745540020605157379447679 := by
  unfold tailWord_4355802
  simp only [CollatzResearch.WordTrace]
  refine ⟨39717287641420185150217415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105912767043787160400579773 39717287641420185150217415)
  ·
    refine ⟨59575931462130277725326123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39717287641420185150217415 59575931462130277725326123)
    ·
      refine ⟨89363897193195416587989185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59575931462130277725326123 89363897193195416587989185)
      ·
        refine ⟨67022922894896562440991889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89363897193195416587989185 67022922894896562440991889)
        ·
          refine ⟨50267192171172421830743917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67022922894896562440991889 50267192171172421830743917)
          ·
            refine ⟨18850197064189658186528969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50267192171172421830743917 18850197064189658186528969)
            ·
              refine ⟨14137647798142243639896727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18850197064189658186528969 14137647798142243639896727)
              ·
                refine ⟨21206471697213365459845091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14137647798142243639896727 21206471697213365459845091)
                ·
                  refine ⟨31809707545820048189767637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21206471697213365459845091 31809707545820048189767637)
                  ·
                    refine ⟨745540020605157379447679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 31809707545820048189767637 745540020605157379447679)
                    ·
                      rfl

theorem cell23_4355802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 2, 1, 1, 7].length) (baseStart_4355802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4355802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4355802 prefixEnd_4355802 := by exact prefixLift 4355802
  have htrace : WordTrace (prefixWord ++ tailWord_4355802) baseStart_4355802 baseEnd_4355802 := by
    simpa [prefixWord, tailWord_4355802, baseEnd_4355802] using wordTrace_append hprefix tailTrace_4355802
  have hstable : (prefixWord ++ tailWord_4355802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4355802).length < 2 ^ (prefixWord ++ tailWord_4355802).sum := by decide
  have hdescent : baseEnd_4355802 < baseStart_4355802 := by decide
  rcases family_descends (prefixWord ++ tailWord_4355802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4355812 : List Nat := [2, 3, 1, 1, 1, 3, 2, 2, 1, 2, 5]
def baseStart_4355812 : Nat := 118140960795 + 4355812 * 2 ^ 59
def prefixEnd_4355812 : Nat := 4983230072969 + 3 ^ 40 * 4355812 * 2
def baseEnd_4355812 : Nat := 2236625196622017099217991

theorem tailTrace_4355812 : CollatzResearch.WordTrace tailWord_4355812 prefixEnd_4355812 2236625196622017099217991 := by
  unfold tailWord_4355812
  simp only [CollatzResearch.WordTrace]
  refine ⟨79434757647822256154366845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105913010197096341539155793 79434757647822256154366845)
  ·
    refine ⟨29788034117933346057887567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79434757647822256154366845 29788034117933346057887567)
    ·
      refine ⟨44682051176900019086831351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29788034117933346057887567 44682051176900019086831351)
      ·
        refine ⟨67023076765350028630247027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44682051176900019086831351 67023076765350028630247027)
        ·
          refine ⟨100534615148025042945370541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67023076765350028630247027 100534615148025042945370541)
          ·
            refine ⟨37700480680509391104513953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 100534615148025042945370541 37700480680509391104513953)
            ·
              refine ⟨28275360510382043328385465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37700480680509391104513953 28275360510382043328385465)
              ·
                refine ⟨21206520382786532496289099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28275360510382043328385465 21206520382786532496289099)
                ·
                  refine ⟨31809780574179798744433649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21206520382786532496289099 31809780574179798744433649)
                  ·
                    refine ⟨23857335430634849058325237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 31809780574179798744433649 23857335430634849058325237)
                    ·
                      refine ⟨2236625196622017099217991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23857335430634849058325237 2236625196622017099217991)
                      ·
                        rfl

theorem cell23_4355812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 2, 1, 2, 5].length) (baseStart_4355812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4355812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4355812 prefixEnd_4355812 := by exact prefixLift 4355812
  have htrace : WordTrace (prefixWord ++ tailWord_4355812) baseStart_4355812 baseEnd_4355812 := by
    simpa [prefixWord, tailWord_4355812, baseEnd_4355812] using wordTrace_append hprefix tailTrace_4355812
  have hstable : (prefixWord ++ tailWord_4355812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4355812).length < 2 ^ (prefixWord ++ tailWord_4355812).sum := by decide
  have hdescent : baseEnd_4355812 < baseStart_4355812 := by decide
  rcases family_descends (prefixWord ++ tailWord_4355812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4355839 : List Nat := [1, 1, 2, 2, 1, 3, 2, 3, 2, 4, 2]
def baseStart_4355839 : Nat := 118140960795 + 4355839 * 2 ^ 59
def prefixEnd_4355839 : Nat := 4983230072969 + 3 ^ 40 * 4355839 * 2
def baseEnd_4355839 : Nat := 2236639060599688493580367

theorem tailTrace_4355839 : CollatzResearch.WordTrace tailWord_4355839 prefixEnd_4355839 2236639060599688493580367 := by
  unfold tailWord_4355839
  simp only [CollatzResearch.WordTrace]
  refine ⟨158870500066546695919966571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105913666711031130613311047 158870500066546695919966571)
  ·
    refine ⟨238305750099820043879949857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158870500066546695919966571 238305750099820043879949857)
    ·
      refine ⟨178729312574865032909962393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 238305750099820043879949857 178729312574865032909962393)
      ·
        refine ⟨134046984431148774682471795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 178729312574865032909962393 134046984431148774682471795)
        ·
          refine ⟨201070476646723162023707693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 134046984431148774682471795 201070476646723162023707693)
          ·
            refine ⟨75401428742521185758890385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 201070476646723162023707693 75401428742521185758890385)
            ·
              refine ⟨56551071556890889319167789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75401428742521185758890385 56551071556890889319167789)
              ·
                refine ⟨21206651833834083494687921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56551071556890889319167789 21206651833834083494687921)
                ·
                  refine ⟨15904988875375562621015941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21206651833834083494687921 15904988875375562621015941)
                  ·
                    refine ⟨2982185414132917991440489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15904988875375562621015941 2982185414132917991440489)
                    ·
                      refine ⟨2236639060599688493580367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2982185414132917991440489 2236639060599688493580367)
                      ·
                        rfl

theorem cell23_4355839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 3, 2, 4, 2].length) (baseStart_4355839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4355839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4355839 prefixEnd_4355839 := by exact prefixLift 4355839
  have htrace : WordTrace (prefixWord ++ tailWord_4355839) baseStart_4355839 baseEnd_4355839 := by
    simpa [prefixWord, tailWord_4355839, baseEnd_4355839] using wordTrace_append hprefix tailTrace_4355839
  have hstable : (prefixWord ++ tailWord_4355839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4355839).length < 2 ^ (prefixWord ++ tailWord_4355839).sum := by decide
  have hdescent : baseEnd_4355839 < baseStart_4355839 := by decide
  rcases family_descends (prefixWord ++ tailWord_4355839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4355852 : List Nat := [2, 2, 1, 2, 2, 1, 2, 1, 2, 4, 4]
def baseStart_4355852 : Nat := 118140960795 + 4355852 * 2 ^ 59
def prefixEnd_4355852 : Nat := 4983230072969 + 3 ^ 40 * 4355852 * 2
def baseEnd_4355852 : Nat := 2236645735848196942717807

theorem tailTrace_4355852 : CollatzResearch.WordTrace tailWord_4355852 prefixEnd_4355852 2236645735848196942717807 := by
  unfold tailWord_4355852
  simp only [CollatzResearch.WordTrace]
  refine ⟨79435487107749799570094905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105913982810333066093459873 79435487107749799570094905)
  ·
    refine ⟨59576615330812349677571179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79435487107749799570094905 59576615330812349677571179)
    ·
      refine ⟨89364922996218524516356769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59576615330812349677571179 89364922996218524516356769)
      ·
        refine ⟨67023692247163893387267577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89364922996218524516356769 67023692247163893387267577)
        ·
          refine ⟨50267769185372920040450683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67023692247163893387267577 50267769185372920040450683)
          ·
            refine ⟨75401653778059380060676025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50267769185372920040450683 75401653778059380060676025)
            ·
              refine ⟨56551240333544535045507019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75401653778059380060676025 56551240333544535045507019)
              ·
                refine ⟨84826860500316802568260529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56551240333544535045507019 84826860500316802568260529)
                ·
                  refine ⟨63620145375237601926195397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 84826860500316802568260529 63620145375237601926195397)
                  ·
                    refine ⟨11928777257857050361161637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 63620145375237601926195397 11928777257857050361161637)
                    ·
                      refine ⟨2236645735848196942717807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11928777257857050361161637 2236645735848196942717807)
                      ·
                        rfl

theorem cell23_4355852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 4, 4].length) (baseStart_4355852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4355852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4355852 prefixEnd_4355852 := by exact prefixLift 4355852
  have htrace : WordTrace (prefixWord ++ tailWord_4355852) baseStart_4355852 baseEnd_4355852 := by
    simpa [prefixWord, tailWord_4355852, baseEnd_4355852] using wordTrace_append hprefix tailTrace_4355852
  have hstable : (prefixWord ++ tailWord_4355852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4355852).length < 2 ^ (prefixWord ++ tailWord_4355852).sum := by decide
  have hdescent : baseEnd_4355852 < baseStart_4355852 := by decide
  rcases family_descends (prefixWord ++ tailWord_4355852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4355876 : List Nat := [2, 3, 1, 3, 2, 1, 2, 2, 2, 2, 3]
def baseStart_4355876 : Nat := 118140960795 + 4355876 * 2 ^ 59
def prefixEnd_4355876 : Nat := 4983230072969 + 3 ^ 40 * 4355876 * 2
def baseEnd_4355876 : Nat := 2236658059383904848817697

theorem tailTrace_4355876 : CollatzResearch.WordTrace tailWord_4355876 prefixEnd_4355876 2236658059383904848817697 := by
  unfold tailWord_4355876
  simp only [CollatzResearch.WordTrace]
  refine ⟨79435924783706325619531741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105914566378275100826042321 79435924783706325619531741)
  ·
    refine ⟨29788471793889872107324403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79435924783706325619531741 29788471793889872107324403)
    ·
      refine ⟨44682707690834808160986605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29788471793889872107324403 44682707690834808160986605)
      ·
        refine ⟨16756015384063053060369977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44682707690834808160986605 16756015384063053060369977)
        ·
          refine ⟨12567011538047289795277483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16756015384063053060369977 12567011538047289795277483)
          ·
            refine ⟨18850517307070934692916225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12567011538047289795277483 18850517307070934692916225)
            ·
              refine ⟨14137887980303201019687169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18850517307070934692916225 14137887980303201019687169)
              ·
                refine ⟨10603415985227400764765377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14137887980303201019687169 10603415985227400764765377)
                ·
                  refine ⟨7952561988920550573574033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10603415985227400764765377 7952561988920550573574033)
                  ·
                    refine ⟨5964421491690412930180525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7952561988920550573574033 5964421491690412930180525)
                    ·
                      refine ⟨2236658059383904848817697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5964421491690412930180525 2236658059383904848817697)
                      ·
                        rfl

theorem cell23_4355876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 2, 2, 2, 2, 3].length) (baseStart_4355876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4355876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4355876 prefixEnd_4355876 := by exact prefixLift 4355876
  have htrace : WordTrace (prefixWord ++ tailWord_4355876) baseStart_4355876 baseEnd_4355876 := by
    simpa [prefixWord, tailWord_4355876, baseEnd_4355876] using wordTrace_append hprefix tailTrace_4355876
  have hstable : (prefixWord ++ tailWord_4355876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4355876).length < 2 ^ (prefixWord ++ tailWord_4355876).sum := by decide
  have hdescent : baseEnd_4355876 < baseStart_4355876 := by decide
  rcases family_descends (prefixWord ++ tailWord_4355876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4355909 : List Nat := [1, 3, 1, 1, 1, 2, 4, 4, 1, 5]
def baseStart_4355909 : Nat := 118140960795 + 4355909 * 2 ^ 59
def prefixEnd_4355909 : Nat := 4983230072969 + 3 ^ 40 * 4355909 * 2
def baseEnd_4355909 : Nat := 745558334748501073235015

theorem tailTrace_4355909 : CollatzResearch.WordTrace tailWord_4355909 prefixEnd_4355909 745558334748501073235015 := by
  unfold tailWord_4355909
  simp only [CollatzResearch.WordTrace]
  refine ⟨158873053176293097875014781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105915368784195398583343187 158873053176293097875014781)
  ·
    refine ⟨59577394941109911703130543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 158873053176293097875014781 59577394941109911703130543)
    ·
      refine ⟨89366092411664867554695815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59577394941109911703130543 89366092411664867554695815)
      ·
        refine ⟨134049138617497301332043723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89366092411664867554695815 134049138617497301332043723)
        ·
          refine ⟨201073707926245951998065585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 134049138617497301332043723 201073707926245951998065585)
          ·
            refine ⟨150805280944684463998549189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 201073707926245951998065585 150805280944684463998549189)
            ·
              refine ⟨28275990177128336999727973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 150805280944684463998549189 28275990177128336999727973)
              ·
                refine ⟨5301748158211563187448995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28275990177128336999727973 5301748158211563187448995)
                ·
                  refine ⟨7952622237317344781173493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5301748158211563187448995 7952622237317344781173493)
                  ·
                    refine ⟨745558334748501073235015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7952622237317344781173493 745558334748501073235015)
                    ·
                      rfl

theorem cell23_4355909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 4, 1, 5].length) (baseStart_4355909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4355909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4355909 prefixEnd_4355909 := by exact prefixLift 4355909
  have htrace : WordTrace (prefixWord ++ tailWord_4355909) baseStart_4355909 baseEnd_4355909 := by
    simpa [prefixWord, tailWord_4355909, baseEnd_4355909] using wordTrace_append hprefix tailTrace_4355909
  have hstable : (prefixWord ++ tailWord_4355909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4355909).length < 2 ^ (prefixWord ++ tailWord_4355909).sum := by decide
  have hdescent : baseEnd_4355909 < baseStart_4355909 := by decide
  rcases family_descends (prefixWord ++ tailWord_4355909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4355910 : List Nat := [6, 1, 1, 2, 1, 1, 3, 1, 2, 2, 3]
def baseStart_4355910 : Nat := 118140960795 + 4355910 * 2 ^ 59
def prefixEnd_4355910 : Nat := 4983230072969 + 3 ^ 40 * 4355910 * 2
def baseEnd_4355910 : Nat := 2236675517726157715792541

theorem tailTrace_4355910 : CollatzResearch.WordTrace tailWord_4355910 prefixEnd_4355910 2236675517726157715792541 := by
  unfold tailWord_4355910
  simp only [CollatzResearch.WordTrace]
  refine ⟨4964784051540296095181287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 105915393099526316697200789 4964784051540296095181287)
  ·
    refine ⟨7447176077310444142771931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4964784051540296095181287 7447176077310444142771931)
    ·
      refine ⟨11170764115965666214157897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7447176077310444142771931 11170764115965666214157897)
      ·
        refine ⟨8378073086974249660618423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11170764115965666214157897 8378073086974249660618423)
        ·
          refine ⟨12567109630461374490927635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8378073086974249660618423 12567109630461374490927635)
          ·
            refine ⟨18850664445692061736391453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12567109630461374490927635 18850664445692061736391453)
            ·
              refine ⟨7068999167134523151146795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18850664445692061736391453 7068999167134523151146795)
              ·
                refine ⟨10603498750701784726720193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7068999167134523151146795 10603498750701784726720193)
                ·
                  refine ⟨7952624063026338545040145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10603498750701784726720193 7952624063026338545040145)
                  ·
                    refine ⟨5964468047269753908780109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7952624063026338545040145 5964468047269753908780109)
                    ·
                      refine ⟨2236675517726157715792541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5964468047269753908780109 2236675517726157715792541)
                      ·
                        rfl

theorem cell23_4355910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 3, 1, 2, 2, 3].length) (baseStart_4355910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4355910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4355910 prefixEnd_4355910 := by exact prefixLift 4355910
  have htrace : WordTrace (prefixWord ++ tailWord_4355910) baseStart_4355910 baseEnd_4355910 := by
    simpa [prefixWord, tailWord_4355910, baseEnd_4355910] using wordTrace_append hprefix tailTrace_4355910
  have hstable : (prefixWord ++ tailWord_4355910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4355910).length < 2 ^ (prefixWord ++ tailWord_4355910).sum := by decide
  have hdescent : baseEnd_4355910 < baseStart_4355910 := by decide
  rcases family_descends (prefixWord ++ tailWord_4355910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4355949 : List Nat := [1, 5, 1, 1, 1, 1, 3, 1, 3, 1, 5]
def baseStart_4355949 : Nat := 118140960795 + 4355949 * 2 ^ 59
def prefixEnd_4355949 : Nat := 4983230072969 + 3 ^ 40 * 4355949 * 2
def baseEnd_4355949 : Nat := 2236695543471683063204861

theorem tailTrace_4355949 : CollatzResearch.WordTrace tailWord_4355949 prefixEnd_4355949 2236695543471683063204861 := by
  unfold tailWord_4355949
  simp only [CollatzResearch.WordTrace]
  refine ⟨158874512096148184706470901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105916341397432123137647267 158874512096148184706470901)
  ·
    refine ⟨14894485509013892316231647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 158874512096148184706470901 14894485509013892316231647)
    ·
      refine ⟨22341728263520838474347471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14894485509013892316231647 22341728263520838474347471)
      ·
        refine ⟨33512592395281257711521207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22341728263520838474347471 33512592395281257711521207)
        ·
          refine ⟨50268888592921886567281811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33512592395281257711521207 50268888592921886567281811)
          ·
            refine ⟨75403332889382829850922717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50268888592921886567281811 75403332889382829850922717)
            ·
              refine ⟨28276249833518561194096019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 75403332889382829850922717 28276249833518561194096019)
              ·
                refine ⟨42414374750277841791144029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28276249833518561194096019 42414374750277841791144029)
                ·
                  refine ⟨15905390531354190671679011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 42414374750277841791144029 15905390531354190671679011)
                  ·
                    refine ⟨23858085797031286007518517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15905390531354190671679011 23858085797031286007518517)
                    ·
                      refine ⟨2236695543471683063204861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23858085797031286007518517 2236695543471683063204861)
                      ·
                        rfl

theorem cell23_4355949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 1, 3, 1, 5].length) (baseStart_4355949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4355949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4355949 prefixEnd_4355949 := by exact prefixLift 4355949
  have htrace : WordTrace (prefixWord ++ tailWord_4355949) baseStart_4355949 baseEnd_4355949 := by
    simpa [prefixWord, tailWord_4355949, baseEnd_4355949] using wordTrace_append hprefix tailTrace_4355949
  have hstable : (prefixWord ++ tailWord_4355949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4355949).length < 2 ^ (prefixWord ++ tailWord_4355949).sum := by decide
  have hdescent : baseEnd_4355949 < baseStart_4355949 := by decide
  rcases family_descends (prefixWord ++ tailWord_4355949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4355952 : List Nat := [2, 1, 1, 1, 4, 1, 1, 12]
def baseStart_4355952 : Nat := 118140960795 + 4355952 * 2 ^ 59
def prefixEnd_4355952 : Nat := 4983230072969 + 3 ^ 40 * 4355952 * 2
def baseEnd_4355952 : Nat := 82840632737542464869161

theorem tailTrace_4355952 : CollatzResearch.WordTrace tailWord_4355952 prefixEnd_4355952 82840632737542464869161 := by
  unfold tailWord_4355952
  simp only [CollatzResearch.WordTrace]
  refine ⟨79437310757568658109415055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105916414343424877479220073 79437310757568658109415055)
  ·
    refine ⟨119155966136352987164122583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79437310757568658109415055 119155966136352987164122583)
    ·
      refine ⟨178733949204529480746183875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119155966136352987164122583 178733949204529480746183875)
      ·
        refine ⟨268100923806794221119275813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 178733949204529480746183875 268100923806794221119275813)
        ·
          refine ⟨50268923213773916459864215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 268100923806794221119275813 50268923213773916459864215)
          ·
            refine ⟨75403384820660874689796323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50268923213773916459864215 75403384820660874689796323)
            ·
              refine ⟨113105077230991312034694485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75403384820660874689796323 113105077230991312034694485)
              ·
                refine ⟨82840632737542464869161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 113105077230991312034694485 82840632737542464869161)
                ·
                  rfl

theorem cell23_4355952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 12].length) (baseStart_4355952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4355952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4355952 prefixEnd_4355952 := by exact prefixLift 4355952
  have htrace : WordTrace (prefixWord ++ tailWord_4355952) baseStart_4355952 baseEnd_4355952 := by
    simpa [prefixWord, tailWord_4355952, baseEnd_4355952] using wordTrace_append hprefix tailTrace_4355952
  have hstable : (prefixWord ++ tailWord_4355952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4355952).length < 2 ^ (prefixWord ++ tailWord_4355952).sum := by decide
  have hdescent : baseEnd_4355952 < baseStart_4355952 := by decide
  rcases family_descends (prefixWord ++ tailWord_4355952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4355979 : List Nat := [1, 1, 1, 1, 4, 2, 1, 3, 3, 3, 3]
def baseStart_4355979 : Nat := 118140960795 + 4355979 * 2 ^ 59
def prefixEnd_4355979 : Nat := 4983230072969 + 3 ^ 40 * 4355979 * 2
def baseEnd_4355979 : Nat := 2236710947891317945829723

theorem tailTrace_4355979 : CollatzResearch.WordTrace tailWord_4355979 prefixEnd_4355979 2236710947891317945829723 := by
  unfold tailWord_4355979
  simp only [CollatzResearch.WordTrace]
  refine ⟨158875606286039499830062991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105917070857359666553375327 158875606286039499830062991)
  ·
    refine ⟨238313409429059249745094487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158875606286039499830062991 238313409429059249745094487)
    ·
      refine ⟨357470114143588874617641731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 238313409429059249745094487 357470114143588874617641731)
      ·
        refine ⟨536205171215383311926462597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 357470114143588874617641731 536205171215383311926462597)
        ·
          refine ⟨100538469602884370986211737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 536205171215383311926462597 100538469602884370986211737)
          ·
            refine ⟨75403852202163278239658803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 100538469602884370986211737 75403852202163278239658803)
            ·
              refine ⟨113105778303244917359488205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75403852202163278239658803 113105778303244917359488205)
              ·
                refine ⟨42414666863716844009808077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 113105778303244917359488205 42414666863716844009808077)
                ·
                  refine ⟨15905500073893816503678029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 42414666863716844009808077 15905500073893816503678029)
                  ·
                    refine ⟨5964562527710181188879261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15905500073893816503678029 5964562527710181188879261)
                    ·
                      refine ⟨2236710947891317945829723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5964562527710181188879261 2236710947891317945829723)
                      ·
                        rfl

theorem cell23_4355979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 3, 3, 3, 3].length) (baseStart_4355979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4355979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4355979 prefixEnd_4355979 := by exact prefixLift 4355979
  have htrace : WordTrace (prefixWord ++ tailWord_4355979) baseStart_4355979 baseEnd_4355979 := by
    simpa [prefixWord, tailWord_4355979, baseEnd_4355979] using wordTrace_append hprefix tailTrace_4355979
  have hstable : (prefixWord ++ tailWord_4355979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4355979).length < 2 ^ (prefixWord ++ tailWord_4355979).sum := by decide
  have hdescent : baseEnd_4355979 < baseStart_4355979 := by decide
  rcases family_descends (prefixWord ++ tailWord_4355979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4355986 : List Nat := [3, 2, 3, 2, 1, 3, 9]
def baseStart_4355986 : Nat := 118140960795 + 4355986 * 2 ^ 59
def prefixEnd_4355986 : Nat := 4983230072969 + 3 ^ 40 * 4355986 * 2
def baseEnd_4355986 : Nat := 27613759780937029857311

theorem tailTrace_4355986 : CollatzResearch.WordTrace tailWord_4355986 prefixEnd_4355986 27613759780937029857311 := by
  unfold tailWord_4355986
  simp only [CollatzResearch.WordTrace]
  refine ⟨39718965399253535006391953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105917241064676093350378541 39718965399253535006391953)
  ·
    refine ⟨29789224049440151254793965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39718965399253535006391953 29789224049440151254793965)
    ·
      refine ⟨11170959018540056720547737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29789224049440151254793965 11170959018540056720547737)
      ·
        refine ⟨8378219263905042540410803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11170959018540056720547737 8378219263905042540410803)
        ·
          refine ⟨12567328895857563810616205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8378219263905042540410803 12567328895857563810616205)
          ·
            refine ⟨4712748335946586428981077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12567328895857563810616205 4712748335946586428981077)
            ·
              refine ⟨27613759780937029857311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4712748335946586428981077 27613759780937029857311)
              ·
                rfl

theorem cell23_4355986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 3, 9].length) (baseStart_4355986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4355986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4355986 prefixEnd_4355986 := by exact prefixLift 4355986
  have htrace : WordTrace (prefixWord ++ tailWord_4355986) baseStart_4355986 baseEnd_4355986 := by
    simpa [prefixWord, tailWord_4355986, baseEnd_4355986] using wordTrace_append hprefix tailTrace_4355986
  have hstable : (prefixWord ++ tailWord_4355986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4355986).length < 2 ^ (prefixWord ++ tailWord_4355986).sum := by decide
  have hdescent : baseEnd_4355986 < baseStart_4355986 := by decide
  rcases family_descends (prefixWord ++ tailWord_4355986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4356014 : List Nat := [4, 1, 5, 1, 1, 2, 1, 2, 1, 1, 4]
def baseStart_4356014 : Nat := 118140960795 + 4356014 * 2 ^ 59
def prefixEnd_4356014 : Nat := 4983230072969 + 3 ^ 40 * 4356014 * 2
def baseEnd_4356014 : Nat := 2236728919714225308892063

theorem tailTrace_4356014 : CollatzResearch.WordTrace tailWord_4356014 prefixEnd_4356014 2236728919714225308892063 := by
  unfold tailWord_4356014
  simp only [CollatzResearch.WordTrace]
  refine ⟨19859610355114087600948387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 105917921893941800538391397 19859610355114087600948387)
  ·
    refine ⟨29789415532671131401422581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19859610355114087600948387 29789415532671131401422581)
    ·
      refine ⟨2792757706187918568883367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 29789415532671131401422581 2792757706187918568883367)
      ·
        refine ⟨4189136559281877853325051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2792757706187918568883367 4189136559281877853325051)
        ·
          refine ⟨6283704838922816779987577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4189136559281877853325051 6283704838922816779987577)
          ·
            refine ⟨4712778629192112584990683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6283704838922816779987577 4712778629192112584990683)
            ·
              refine ⟨7069167943788168877486025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4712778629192112584990683 7069167943788168877486025)
              ·
                refine ⟨5301875957841126658114519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7069167943788168877486025 5301875957841126658114519)
                ·
                  refine ⟨7952813936761689987171779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5301875957841126658114519 7952813936761689987171779)
                  ·
                    refine ⟨11929220905142534980757669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7952813936761689987171779 11929220905142534980757669)
                    ·
                      refine ⟨2236728919714225308892063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11929220905142534980757669 2236728919714225308892063)
                      ·
                        rfl

theorem cell23_4356014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 2, 1, 2, 1, 1, 4].length) (baseStart_4356014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4356014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4356014 prefixEnd_4356014 := by exact prefixLift 4356014
  have htrace : WordTrace (prefixWord ++ tailWord_4356014) baseStart_4356014 baseEnd_4356014 := by
    simpa [prefixWord, tailWord_4356014, baseEnd_4356014] using wordTrace_append hprefix tailTrace_4356014
  have hstable : (prefixWord ++ tailWord_4356014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4356014).length < 2 ^ (prefixWord ++ tailWord_4356014).sum := by decide
  have hdescent : baseEnd_4356014 < baseStart_4356014 := by decide
  rcases family_descends (prefixWord ++ tailWord_4356014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4356096 : List Nat := [2, 1, 1, 2, 1, 1, 1, 4, 1, 7, 2]
def baseStart_4356096 : Nat := 118140960795 + 4356096 * 2 ^ 59
def prefixEnd_4356096 : Nat := 4983230072969 + 3 ^ 40 * 4356096 * 2
def baseEnd_4356096 : Nat := 2236771025127893988066685

theorem tailTrace_4356096 : CollatzResearch.WordTrace tailWord_4356096 prefixEnd_4356096 2236771025127893988066685 := by
  unfold tailWord_4356096
  simp only [CollatzResearch.WordTrace]
  refine ⟨79439936813307814406036071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105919915751077085874714761 79439936813307814406036071)
  ·
    refine ⟨119159905219961721609054107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79439936813307814406036071 119159905219961721609054107)
    ·
      refine ⟨178739857829942582413581161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119159905219961721609054107 178739857829942582413581161)
      ·
        refine ⟨134054893372456936810185871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 178739857829942582413581161 134054893372456936810185871)
        ·
          refine ⟨201082340058685405215278807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 134054893372456936810185871 201082340058685405215278807)
          ·
            refine ⟨301623510088028107822918211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 201082340058685405215278807 301623510088028107822918211)
            ·
              refine ⟨452435265132042161734377317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 301623510088028107822918211 452435265132042161734377317)
              ·
                refine ⟨84831612212257905325195747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 452435265132042161734377317 84831612212257905325195747)
                ·
                  refine ⟨127247418318386857987793621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 84831612212257905325195747 127247418318386857987793621)
                  ·
                    refine ⟨2982361366837191984088913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 127247418318386857987793621 2982361366837191984088913)
                    ·
                      refine ⟨2236771025127893988066685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2982361366837191984088913 2236771025127893988066685)
                      ·
                        rfl

theorem cell23_4356096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 4, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 4, 1, 7, 2].length) (baseStart_4356096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4356096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4356096 prefixEnd_4356096 := by exact prefixLift 4356096
  have htrace : WordTrace (prefixWord ++ tailWord_4356096) baseStart_4356096 baseEnd_4356096 := by
    simpa [prefixWord, tailWord_4356096, baseEnd_4356096] using wordTrace_append hprefix tailTrace_4356096
  have hstable : (prefixWord ++ tailWord_4356096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4356096).length < 2 ^ (prefixWord ++ tailWord_4356096).sum := by decide
  have hdescent : baseEnd_4356096 < baseStart_4356096 := by decide
  rcases family_descends (prefixWord ++ tailWord_4356096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4356099 : List Nat := [1, 1, 1, 3, 2, 1, 1, 3, 3, 2, 5]
def baseStart_4356099 : Nat := 118140960795 + 4356099 * 2 ^ 59
def prefixEnd_4356099 : Nat := 4983230072969 + 3 ^ 40 * 4356099 * 2
def baseEnd_4356099 : Nat := 2236772565569857476329171

theorem tailTrace_4356099 : CollatzResearch.WordTrace tailWord_4356099 prefixEnd_4356099 2236772565569857476329171 := by
  unfold tailWord_4356099
  simp only [CollatzResearch.WordTrace]
  refine ⟨158879983045604760324431351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105919988697069840216287567 158879983045604760324431351)
  ·
    refine ⟨238319974568407140486647027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158879983045604760324431351 238319974568407140486647027)
    ·
      refine ⟨357479961852610710729970541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 238319974568407140486647027 357479961852610710729970541)
      ·
        refine ⟨134054985694729016523738953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 357479961852610710729970541 134054985694729016523738953)
        ·
          refine ⟨100541239271046762392804215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 134054985694729016523738953 100541239271046762392804215)
          ·
            refine ⟨150811858906570143589206323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100541239271046762392804215 150811858906570143589206323)
            ·
              refine ⟨226217788359855215383809485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 150811858906570143589206323 226217788359855215383809485)
              ·
                refine ⟨84831670634945705768928557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 226217788359855215383809485 84831670634945705768928557)
                ·
                  refine ⟨31811876488104639663348209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 84831670634945705768928557 31811876488104639663348209)
                  ·
                    refine ⟨23858907366078479747511157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 31811876488104639663348209 23858907366078479747511157)
                    ·
                      refine ⟨2236772565569857476329171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23858907366078479747511157 2236772565569857476329171)
                      ·
                        rfl

theorem cell23_4356099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 3, 3, 2, 5].length) (baseStart_4356099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4356099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4356099 prefixEnd_4356099 := by exact prefixLift 4356099
  have htrace : WordTrace (prefixWord ++ tailWord_4356099) baseStart_4356099 baseEnd_4356099 := by
    simpa [prefixWord, tailWord_4356099, baseEnd_4356099] using wordTrace_append hprefix tailTrace_4356099
  have hstable : (prefixWord ++ tailWord_4356099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4356099).length < 2 ^ (prefixWord ++ tailWord_4356099).sum := by decide
  have hdescent : baseEnd_4356099 < baseStart_4356099 := by decide
  rcases family_descends (prefixWord ++ tailWord_4356099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4356139 : List Nat := [1, 1, 1, 1, 2, 1, 4, 2, 1, 3, 6]
def baseStart_4356139 : Nat := 118140960795 + 4356139 * 2 ^ 59
def prefixEnd_4356139 : Nat := 4983230072969 + 3 ^ 40 * 4356139 * 2
def baseEnd_4356139 : Nat := 2236793104796037319828987

theorem tailTrace_4356139 : CollatzResearch.WordTrace tailWord_4356139 prefixEnd_4356139 2236793104796037319828987 := by
  unfold tailWord_4356139
  simp only [CollatzResearch.WordTrace]
  refine ⟨158881441965459847155887471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105920961310306564770591647 158881441965459847155887471)
  ·
    refine ⟨238322162948189770733831207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158881441965459847155887471 238322162948189770733831207)
    ·
      refine ⟨357483244422284656100746811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 238322162948189770733831207 357483244422284656100746811)
      ·
        refine ⟨536224866633426984151120217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 357483244422284656100746811 536224866633426984151120217)
        ·
          refine ⟨402168649975070238113340163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 536224866633426984151120217 402168649975070238113340163)
          ·
            refine ⟨603252974962605357170010245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 402168649975070238113340163 603252974962605357170010245)
            ·
              refine ⟨113109932805488504469376921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 603252974962605357170010245 113109932805488504469376921)
              ·
                refine ⟨84832449604116378352032691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 113109932805488504469376921 84832449604116378352032691)
                ·
                  refine ⟨127248674406174567528049037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 84832449604116378352032691 127248674406174567528049037)
                  ·
                    refine ⟨47718252902315462823018389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 127248674406174567528049037 47718252902315462823018389)
                    ·
                      refine ⟨2236793104796037319828987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 47718252902315462823018389 2236793104796037319828987)
                      ·
                        rfl

theorem cell23_4356139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 2, 1, 3, 6].length) (baseStart_4356139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4356139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4356139 prefixEnd_4356139 := by exact prefixLift 4356139
  have htrace : WordTrace (prefixWord ++ tailWord_4356139) baseStart_4356139 baseEnd_4356139 := by
    simpa [prefixWord, tailWord_4356139, baseEnd_4356139] using wordTrace_append hprefix tailTrace_4356139
  have hstable : (prefixWord ++ tailWord_4356139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4356139).length < 2 ^ (prefixWord ++ tailWord_4356139).sum := by decide
  have hdescent : baseEnd_4356139 < baseStart_4356139 := by decide
  rcases family_descends (prefixWord ++ tailWord_4356139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4356183 : List Nat := [1, 1, 3, 2, 2, 1, 6, 1, 6]
def baseStart_4356183 : Nat := 118140960795 + 4356183 * 2 ^ 59
def prefixEnd_4356183 : Nat := 4983230072969 + 3 ^ 40 * 4356183 * 2
def baseEnd_4356183 : Nat := 248535077549426127519865

theorem tailTrace_4356183 : CollatzResearch.WordTrace tailWord_4356183 prefixEnd_4356183 248535077549426127519865 := by
  unfold tailWord_4356183
  simp only [CollatzResearch.WordTrace]
  refine ⟨158883046777300442670489203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105922031184866961780326135 158883046777300442670489203)
  ·
    refine ⟨238324570165950664005733805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158883046777300442670489203 238324570165950664005733805)
    ·
      refine ⟨89371713812231499002150177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 238324570165950664005733805 89371713812231499002150177)
      ·
        refine ⟨67028785359173624251612633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89371713812231499002150177 67028785359173624251612633)
        ·
          refine ⟨50271589019380218188709475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67028785359173624251612633 50271589019380218188709475)
          ·
            refine ⟨75407383529070327283064213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50271589019380218188709475 75407383529070327283064213)
            ·
              refine ⟨3534721102925171591393635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 75407383529070327283064213 3534721102925171591393635)
              ·
                refine ⟨5302081654387757387090453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3534721102925171591393635 5302081654387757387090453)
                ·
                  refine ⟨248535077549426127519865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5302081654387757387090453 248535077549426127519865)
                  ·
                    rfl

theorem cell23_4356183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 6, 1, 6].length) (baseStart_4356183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4356183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4356183 prefixEnd_4356183 := by exact prefixLift 4356183
  have htrace : WordTrace (prefixWord ++ tailWord_4356183) baseStart_4356183 baseEnd_4356183 := by
    simpa [prefixWord, tailWord_4356183, baseEnd_4356183] using wordTrace_append hprefix tailTrace_4356183
  have hstable : (prefixWord ++ tailWord_4356183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4356183).length < 2 ^ (prefixWord ++ tailWord_4356183).sum := by decide
  have hdescent : baseEnd_4356183 < baseStart_4356183 := by decide
  rcases family_descends (prefixWord ++ tailWord_4356183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4356193 : List Nat := [1, 2, 3, 1, 1, 2, 1, 3, 5, 1, 3]
def baseStart_4356193 : Nat := 118140960795 + 4356193 * 2 ^ 59
def prefixEnd_4356193 : Nat := 4983230072969 + 3 ^ 40 * 4356193 * 2
def baseEnd_4356193 : Nat := 2236820832751380108553739

theorem tailTrace_4356193 : CollatzResearch.WordTrace tailWord_4356193 prefixEnd_4356193 2236820832751380108553739 := by
  unfold tailWord_4356193
  simp only [CollatzResearch.WordTrace]
  refine ⟨158883411507264214378353233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105922274338176142918902155 158883411507264214378353233)
  ·
    refine ⟨119162558630448160783764925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 158883411507264214378353233 119162558630448160783764925)
    ·
      refine ⟨44685959486418060293911847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 119162558630448160783764925 44685959486418060293911847)
      ·
        refine ⟨67028939229627090440867771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44685959486418060293911847 67028939229627090440867771)
        ·
          refine ⟨100543408844440635661301657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67028939229627090440867771 100543408844440635661301657)
          ·
            refine ⟨75407556633330476745976243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 100543408844440635661301657 75407556633330476745976243)
            ·
              refine ⟨113111334949995715118964365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75407556633330476745976243 113111334949995715118964365)
              ·
                refine ⟨42416750606248393169611637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 113111334949995715118964365 42416750606248393169611637)
                ·
                  refine ⟨3976570369335786859651091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 42416750606248393169611637 3976570369335786859651091)
                  ·
                    refine ⟨5964855554003680289476637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3976570369335786859651091 5964855554003680289476637)
                    ·
                      refine ⟨2236820832751380108553739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5964855554003680289476637 2236820832751380108553739)
                      ·
                        rfl

theorem cell23_4356193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 3, 5, 1, 3].length) (baseStart_4356193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4356193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4356193 prefixEnd_4356193 := by exact prefixLift 4356193
  have htrace : WordTrace (prefixWord ++ tailWord_4356193) baseStart_4356193 baseEnd_4356193 := by
    simpa [prefixWord, tailWord_4356193, baseEnd_4356193] using wordTrace_append hprefix tailTrace_4356193
  have hstable : (prefixWord ++ tailWord_4356193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4356193).length < 2 ^ (prefixWord ++ tailWord_4356193).sum := by decide
  have hdescent : baseEnd_4356193 < baseStart_4356193 := by decide
  rcases family_descends (prefixWord ++ tailWord_4356193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4356220 : List Nat := [2, 2, 2, 1, 1, 4, 2, 2, 2, 3, 2]
def baseStart_4356220 : Nat := 118140960795 + 4356220 * 2 ^ 59
def prefixEnd_4356220 : Nat := 4983230072969 + 3 ^ 40 * 4356220 * 2
def baseEnd_4356220 : Nat := 2236834696729051502916115

theorem tailTrace_4356220 : CollatzResearch.WordTrace tailWord_4356220 prefixEnd_4356220 2236834696729051502916115 := by
  unfold tailWord_4356220
  simp only [CollatzResearch.WordTrace]
  refine ⟨79442198139083198994793057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105922930852110931993057409 79442198139083198994793057)
  ·
    refine ⟨59581648604312399246094793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79442198139083198994793057 59581648604312399246094793)
    ·
      refine ⟨44686236453234299434571095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59581648604312399246094793 44686236453234299434571095)
      ·
        refine ⟨67029354679851449151856643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44686236453234299434571095 67029354679851449151856643)
        ·
          refine ⟨100544032019777173727784965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67029354679851449151856643 100544032019777173727784965)
          ·
            refine ⟨18852006003708220073959681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 100544032019777173727784965 18852006003708220073959681)
            ·
              refine ⟨14139004502781165055469761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18852006003708220073959681 14139004502781165055469761)
              ·
                refine ⟨10604253377085873791602321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14139004502781165055469761 10604253377085873791602321)
                ·
                  refine ⟨7953190032814405343701741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10604253377085873791602321 7953190032814405343701741)
                  ·
                    refine ⟨2982446262305402003888153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7953190032814405343701741 2982446262305402003888153)
                    ·
                      refine ⟨2236834696729051502916115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2982446262305402003888153 2236834696729051502916115)
                      ·
                        rfl

theorem cell23_4356220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 2, 2, 2, 3, 2].length) (baseStart_4356220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4356220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4356220 prefixEnd_4356220 := by exact prefixLift 4356220
  have htrace : WordTrace (prefixWord ++ tailWord_4356220) baseStart_4356220 baseEnd_4356220 := by
    simpa [prefixWord, tailWord_4356220, baseEnd_4356220] using wordTrace_append hprefix tailTrace_4356220
  have hstable : (prefixWord ++ tailWord_4356220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4356220).length < 2 ^ (prefixWord ++ tailWord_4356220).sum := by decide
  have hdescent : baseEnd_4356220 < baseStart_4356220 := by decide
  rcases family_descends (prefixWord ++ tailWord_4356220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4356227 : List Nat := [1, 1, 1, 3, 3, 4, 1, 4, 1, 1, 3]
def baseStart_4356227 : Nat := 118140960795 + 4356227 * 2 ^ 59
def prefixEnd_4356227 : Nat := 4983230072969 + 3 ^ 40 * 4356227 * 2
def baseEnd_4356227 : Nat := 2236838291093632975528583

theorem tailTrace_4356227 : CollatzResearch.WordTrace tailWord_4356227 prefixEnd_4356227 2236838291093632975528583 := by
  unfold tailWord_4356227
  simp only [CollatzResearch.WordTrace]
  refine ⟨158884651589141038185090935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105923101059427358790060623 158884651589141038185090935)
  ·
    refine ⟨238326977383711557277636403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158884651589141038185090935 238326977383711557277636403)
    ·
      refine ⟨357490466075567335916454605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 238326977383711557277636403 357490466075567335916454605)
      ·
        refine ⟨134058924778337750968670477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 357490466075567335916454605 134058924778337750968670477)
        ·
          refine ⟨50272096791876656613251429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 134058924778337750968670477 50272096791876656613251429)
          ·
            refine ⟨9426018148476873114984643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 50272096791876656613251429 9426018148476873114984643)
            ·
              refine ⟨14139027222715309672476965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9426018148476873114984643 14139027222715309672476965)
              ·
                refine ⟨2651067604259120563589431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14139027222715309672476965 2651067604259120563589431)
                ·
                  refine ⟨3976601406388680845384147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2651067604259120563589431 3976601406388680845384147)
                  ·
                    refine ⟨5964902109583021268076221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3976601406388680845384147 5964902109583021268076221)
                    ·
                      refine ⟨2236838291093632975528583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5964902109583021268076221 2236838291093632975528583)
                      ·
                        rfl

theorem cell23_4356227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 1, 4, 1, 1, 3].length) (baseStart_4356227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4356227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4356227 prefixEnd_4356227 := by exact prefixLift 4356227
  have htrace : WordTrace (prefixWord ++ tailWord_4356227) baseStart_4356227 baseEnd_4356227 := by
    simpa [prefixWord, tailWord_4356227, baseEnd_4356227] using wordTrace_append hprefix tailTrace_4356227
  have hstable : (prefixWord ++ tailWord_4356227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4356227).length < 2 ^ (prefixWord ++ tailWord_4356227).sum := by decide
  have hdescent : baseEnd_4356227 < baseStart_4356227 := by decide
  rcases family_descends (prefixWord ++ tailWord_4356227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4356244 : List Nat := [2, 4, 2, 3, 1, 1, 1, 2, 3, 1, 3]
def baseStart_4356244 : Nat := 118140960795 + 4356244 * 2 ^ 59
def prefixEnd_4356244 : Nat := 4983230072969 + 3 ^ 40 * 4356244 * 2
def baseEnd_4356244 : Nat := 2236847020264759409016005

theorem tailTrace_4356244 : CollatzResearch.WordTrace tailWord_4356244 prefixEnd_4356244 2236847020264759409016005 := by
  unfold tailWord_4356244
  simp only [CollatzResearch.WordTrace]
  refine ⟨79442635815039725044229893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105923514420052966725639857 79442635815039725044229893)
  ·
    refine ⟨14895494215319948445793105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 79442635815039725044229893 14895494215319948445793105)
    ·
      refine ⟨11171620661489961334344829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14895494215319948445793105 11171620661489961334344829)
      ·
        refine ⟨4189357748058735500379311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11171620661489961334344829 4189357748058735500379311)
        ·
          refine ⟨6284036622088103250568967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4189357748058735500379311 6284036622088103250568967)
          ·
            refine ⟨9426054933132154875853451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6284036622088103250568967 9426054933132154875853451)
            ·
              refine ⟨14139082399698232313780177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9426054933132154875853451 14139082399698232313780177)
              ·
                refine ⟨10604311799773674235335133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14139082399698232313780177 10604311799773674235335133)
                ·
                  refine ⟨3976616924915127838250675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10604311799773674235335133 3976616924915127838250675)
                  ·
                    refine ⟨5964925387372691757376013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3976616924915127838250675 5964925387372691757376013)
                    ·
                      refine ⟨2236847020264759409016005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5964925387372691757376013 2236847020264759409016005)
                      ·
                        rfl

theorem cell23_4356244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 1, 2, 3, 1, 3].length) (baseStart_4356244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4356244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4356244 prefixEnd_4356244 := by exact prefixLift 4356244
  have htrace : WordTrace (prefixWord ++ tailWord_4356244) baseStart_4356244 baseEnd_4356244 := by
    simpa [prefixWord, tailWord_4356244, baseEnd_4356244] using wordTrace_append hprefix tailTrace_4356244
  have hstable : (prefixWord ++ tailWord_4356244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4356244).length < 2 ^ (prefixWord ++ tailWord_4356244).sum := by decide
  have hdescent : baseEnd_4356244 < baseStart_4356244 := by decide
  rcases family_descends (prefixWord ++ tailWord_4356244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4356273 : List Nat := [1, 2, 2, 5, 2, 1, 10]
def baseStart_4356273 : Nat := 118140960795 + 4356273 * 2 ^ 59
def prefixEnd_4356273 : Nat := 4983230072969 + 3 ^ 40 * 4356273 * 2
def baseEnd_4356273 : Nat := 27615579150663454266091

theorem tailTrace_4356273 : CollatzResearch.WordTrace tailWord_4356273 prefixEnd_4356273 27615579150663454266091 := by
  unfold tailWord_4356273
  simp only [CollatzResearch.WordTrace]
  refine ⟨158886329346974388041265473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105924219564649592027510315 158886329346974388041265473)
  ·
    refine ⟨119164747010230791030949105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 158886329346974388041265473 119164747010230791030949105)
    ·
      refine ⟨89373560257673093273211829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119164747010230791030949105 89373560257673093273211829)
      ·
        refine ⟨8378771274156852494363609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 89373560257673093273211829 8378771274156852494363609)
        ·
          refine ⟨6284078455617639370772707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8378771274156852494363609 6284078455617639370772707)
          ·
            refine ⟨9426117683426459056159061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6284078455617639370772707 9426117683426459056159061)
            ·
              refine ⟨27615579150663454266091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 9426117683426459056159061 27615579150663454266091)
              ·
                rfl

theorem cell23_4356273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 10].length) (baseStart_4356273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4356273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4356273 prefixEnd_4356273 := by exact prefixLift 4356273
  have htrace : WordTrace (prefixWord ++ tailWord_4356273) baseStart_4356273 baseEnd_4356273 := by
    simpa [prefixWord, tailWord_4356273, baseEnd_4356273] using wordTrace_append hprefix tailTrace_4356273
  have hstable : (prefixWord ++ tailWord_4356273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4356273).length < 2 ^ (prefixWord ++ tailWord_4356273).sum := by decide
  have hdescent : baseEnd_4356273 < baseStart_4356273 := by decide
  rcases family_descends (prefixWord ++ tailWord_4356273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4356277 : List Nat := [1, 3, 3, 4, 1, 1, 1, 1, 4, 4]
def baseStart_4356277 : Nat := 118140960795 + 4356277 * 2 ^ 59
def prefixEnd_4356277 : Nat := 4983230072969 + 3 ^ 40 * 4356277 * 2
def baseEnd_4356277 : Nat := 745621321708785926634451

theorem tailTrace_4356277 : CollatzResearch.WordTrace tailWord_4356277 prefixEnd_4356277 745621321708785926634451 := by
  unfold tailWord_4356277
  simp only [CollatzResearch.WordTrace]
  refine ⟨158886475238959896724411085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105924316825973264482940723 158886475238959896724411085)
  ·
    refine ⟨59582428214609961271654157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 158886475238959896724411085 59582428214609961271654157)
    ·
      refine ⟨22343410580478735476870309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59582428214609961271654157 22343410580478735476870309)
      ·
        refine ⟨4189389483839762901913183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22343410580478735476870309 4189389483839762901913183)
        ·
          refine ⟨6284084225759644352869775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4189389483839762901913183 6284084225759644352869775)
          ·
            refine ⟨9426126338639466529304663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6284084225759644352869775 9426126338639466529304663)
            ·
              refine ⟨14139189507959199793956995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9426126338639466529304663 14139189507959199793956995)
              ·
                refine ⟨21208784261938799690935493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14139189507959199793956995 21208784261938799690935493)
                ·
                  refine ⟨3976647049113524942050405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21208784261938799690935493 3976647049113524942050405)
                  ·
                    refine ⟨745621321708785926634451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3976647049113524942050405 745621321708785926634451)
                    ·
                      rfl

theorem cell23_4356277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 1, 1, 4, 4].length) (baseStart_4356277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4356277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4356277 prefixEnd_4356277 := by exact prefixLift 4356277
  have htrace : WordTrace (prefixWord ++ tailWord_4356277) baseStart_4356277 baseEnd_4356277 := by
    simpa [prefixWord, tailWord_4356277, baseEnd_4356277] using wordTrace_append hprefix tailTrace_4356277
  have hstable : (prefixWord ++ tailWord_4356277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4356277).length < 2 ^ (prefixWord ++ tailWord_4356277).sum := by decide
  have hdescent : baseEnd_4356277 < baseStart_4356277 := by decide
  rcases family_descends (prefixWord ++ tailWord_4356277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4356284 : List Nat := [2, 2, 2, 3, 3, 1, 2, 1, 3, 2, 2]
def baseStart_4356284 : Nat := 118140960795 + 4356284 * 2 ^ 59
def prefixEnd_4356284 : Nat := 4983230072969 + 3 ^ 40 * 4356284 * 2
def baseEnd_4356284 : Nat := 2236867559490939252515821

theorem tailTrace_4356284 : CollatzResearch.WordTrace tailWord_4356284 prefixEnd_4356284 2236867559490939252515821 := by
  unfold tailWord_4356284
  simp only [CollatzResearch.WordTrace]
  refine ⟨79443365274967268459957953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105924487033289691279943937 79443365274967268459957953)
  ·
    refine ⟨59582523956225451344968465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79443365274967268459957953 59582523956225451344968465)
    ·
      refine ⟨44686892967169088508726349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59582523956225451344968465 44686892967169088508726349)
      ·
        refine ⟨16757584862688408190772381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44686892967169088508726349 16757584862688408190772381)
        ·
          refine ⟨6284094323508153071539643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16757584862688408190772381 6284094323508153071539643)
          ·
            refine ⟨9426141485262229607309465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6284094323508153071539643 9426141485262229607309465)
            ·
              refine ⟨7069606113946672205482099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9426141485262229607309465 7069606113946672205482099)
              ·
                refine ⟨10604409170920008308223149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7069606113946672205482099 10604409170920008308223149)
                ·
                  refine ⟨3976653439095003115583681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10604409170920008308223149 3976653439095003115583681)
                  ·
                    refine ⟨2982490079321252336687761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3976653439095003115583681 2982490079321252336687761)
                    ·
                      refine ⟨2236867559490939252515821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2982490079321252336687761 2236867559490939252515821)
                      ·
                        rfl

theorem cell23_4356284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 2, 1, 3, 2, 2].length) (baseStart_4356284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4356284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4356284 prefixEnd_4356284 := by exact prefixLift 4356284
  have htrace : WordTrace (prefixWord ++ tailWord_4356284) baseStart_4356284 baseEnd_4356284 := by
    simpa [prefixWord, tailWord_4356284, baseEnd_4356284] using wordTrace_append hprefix tailTrace_4356284
  have hstable : (prefixWord ++ tailWord_4356284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4356284).length < 2 ^ (prefixWord ++ tailWord_4356284).sum := by decide
  have hdescent : baseEnd_4356284 < baseStart_4356284 := by decide
  rcases family_descends (prefixWord ++ tailWord_4356284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4356317 : List Nat := [1, 4, 3, 2, 1, 1, 1, 2, 4, 1, 3]
def baseStart_4356317 : Nat := 118140960795 + 4356317 * 2 ^ 59
def prefixEnd_4356317 : Nat := 4983230072969 + 3 ^ 40 * 4356317 * 2
def baseEnd_4356317 : Nat := 2236884504352537623403169

theorem tailTrace_4356317 : CollatzResearch.WordTrace tailWord_4356317 prefixEnd_4356317 2236884504352537623403169 := by
  unfold tailWord_4356317
  simp only [CollatzResearch.WordTrace]
  refine ⟨158887934158814983555867205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105925289439209989037244803 158887934158814983555867205)
  ·
    refine ⟨29791487654777809416725101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 158887934158814983555867205 29791487654777809416725101)
    ·
      refine ⟨11171807870541678531271913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29791487654777809416725101 11171807870541678531271913)
      ·
        refine ⟨8378855902906258898453935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11171807870541678531271913 8378855902906258898453935)
        ·
          refine ⟨12568283854359388347680903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8378855902906258898453935 12568283854359388347680903)
          ·
            refine ⟨18852425781539082521521355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12568283854359388347680903 18852425781539082521521355)
            ·
              refine ⟨28278638672308623782282033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18852425781539082521521355 28278638672308623782282033)
              ·
                refine ⟨21208979004231467836711525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28278638672308623782282033 21208979004231467836711525)
                ·
                  refine ⟨3976683563293400219383411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21208979004231467836711525 3976683563293400219383411)
                  ·
                    refine ⟨5965025344940100329075117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3976683563293400219383411 5965025344940100329075117)
                    ·
                      refine ⟨2236884504352537623403169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5965025344940100329075117 2236884504352537623403169)
                      ·
                        rfl

theorem cell23_4356317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 2, 4, 1, 3].length) (baseStart_4356317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4356317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4356317 prefixEnd_4356317 := by exact prefixLift 4356317
  have htrace : WordTrace (prefixWord ++ tailWord_4356317) baseStart_4356317 baseEnd_4356317 := by
    simpa [prefixWord, tailWord_4356317, baseEnd_4356317] using wordTrace_append hprefix tailTrace_4356317
  have hstable : (prefixWord ++ tailWord_4356317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4356317).length < 2 ^ (prefixWord ++ tailWord_4356317).sum := by decide
  have hdescent : baseEnd_4356317 < baseStart_4356317 := by decide
  rcases family_descends (prefixWord ++ tailWord_4356317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4356353 : List Nat := [1, 2, 4, 1, 1, 2, 2, 1, 1, 4, 4]
def baseStart_4356353 : Nat := 118140960795 + 4356353 * 2 ^ 59
def prefixEnd_4356353 : Nat := 4983230072969 + 3 ^ 40 * 4356353 * 2
def baseEnd_4356353 : Nat := 2236902989656099482553003

theorem tailTrace_4356353 : CollatzResearch.WordTrace tailWord_4356353 prefixEnd_4356353 2236902989656099482553003 := by
  unfold tailWord_4356353
  simp only [CollatzResearch.WordTrace]
  refine ⟨158889247186684561704177713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105926164791123041136118475 158889247186684561704177713)
  ·
    refine ⟨119166935390013421278133285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 158889247186684561704177713 119166935390013421278133285)
    ·
      refine ⟨22343800385627516489649991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 119166935390013421278133285 22343800385627516489649991)
      ·
        refine ⟨33515700578441274734474987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22343800385627516489649991 33515700578441274734474987)
        ·
          refine ⟨50273550867661912101712481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33515700578441274734474987 50273550867661912101712481)
          ·
            refine ⟨37705163150746434076284361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50273550867661912101712481 37705163150746434076284361)
            ·
              refine ⟨28278872363059825557213271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37705163150746434076284361 28278872363059825557213271)
              ·
                refine ⟨42418308544589738335819907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28278872363059825557213271 42418308544589738335819907)
                ·
                  refine ⟨63627462816884607503729861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42418308544589738335819907 63627462816884607503729861)
                  ·
                    refine ⟨11930149278165863906949349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 63627462816884607503729861 11930149278165863906949349)
                    ·
                      refine ⟨2236902989656099482553003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11930149278165863906949349 2236902989656099482553003)
                      ·
                        rfl

theorem cell23_4356353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 1, 1, 4, 4].length) (baseStart_4356353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4356353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4356353 prefixEnd_4356353 := by exact prefixLift 4356353
  have htrace : WordTrace (prefixWord ++ tailWord_4356353) baseStart_4356353 baseEnd_4356353 := by
    simpa [prefixWord, tailWord_4356353, baseEnd_4356353] using wordTrace_append hprefix tailTrace_4356353
  have hstable : (prefixWord ++ tailWord_4356353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4356353).length < 2 ^ (prefixWord ++ tailWord_4356353).sum := by decide
  have hdescent : baseEnd_4356353 < baseStart_4356353 := by decide
  rcases family_descends (prefixWord ++ tailWord_4356353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4356380 : List Nat := [2, 2, 3, 1, 1, 1, 1, 7, 5]
def baseStart_4356380 : Nat := 118140960795 + 4356380 * 2 ^ 59
def prefixEnd_4356380 : Nat := 4983230072969 + 3 ^ 40 * 4356380 * 2
def baseEnd_4356380 : Nat := 248546317070418986323931

theorem tailTrace_4356380 : CollatzResearch.WordTrace tailWord_4356380 prefixEnd_4356380 248546317070418986323931 := by
  unfold tailWord_4356380
  simp only [CollatzResearch.WordTrace]
  refine ⟨79445115978793372657705297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105926821305057830210273729 79445115978793372657705297)
  ·
    refine ⟨59583836984095029493278973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79445115978793372657705297 59583836984095029493278973)
    ·
      refine ⟨22343938869035636059979615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59583836984095029493278973 22343938869035636059979615)
      ·
        refine ⟨33515908303553454089969423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22343938869035636059979615 33515908303553454089969423)
        ·
          refine ⟨50273862455330181134954135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33515908303553454089969423 50273862455330181134954135)
          ·
            refine ⟨75410793682995271702431203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50273862455330181134954135 75410793682995271702431203)
            ·
              refine ⟨113116190524492907553646805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75410793682995271702431203 113116190524492907553646805)
              ·
                refine ⟨2651160715417802520788597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 113116190524492907553646805 2651160715417802520788597)
                ·
                  refine ⟨248546317070418986323931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2651160715417802520788597 248546317070418986323931)
                  ·
                    rfl

theorem cell23_4356380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 7, 5].length) (baseStart_4356380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4356380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4356380 prefixEnd_4356380 := by exact prefixLift 4356380
  have htrace : WordTrace (prefixWord ++ tailWord_4356380) baseStart_4356380 baseEnd_4356380 := by
    simpa [prefixWord, tailWord_4356380, baseEnd_4356380] using wordTrace_append hprefix tailTrace_4356380
  have hstable : (prefixWord ++ tailWord_4356380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4356380).length < 2 ^ (prefixWord ++ tailWord_4356380).sum := by decide
  have hdescent : baseEnd_4356380 < baseStart_4356380 := by decide
  rcases family_descends (prefixWord ++ tailWord_4356380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4356403 : List Nat := [1, 1, 1, 2, 5, 1, 1, 3, 1, 2, 5]
def baseStart_4356403 : Nat := 118140960795 + 4356403 * 2 ^ 59
def prefixEnd_4356403 : Nat := 4983230072969 + 3 ^ 40 * 4356403 * 2
def baseEnd_4356403 : Nat := 2236928663688824286927773

theorem tailTrace_4356403 : CollatzResearch.WordTrace tailWord_4356403 prefixEnd_4356403 2236928663688824286927773 := by
  unfold tailWord_4356403
  simp only [CollatzResearch.WordTrace]
  refine ⟨158891070836503420243497863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105927380557668946828998575 158891070836503420243497863)
  ·
    refine ⟨238336606254755130365246795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158891070836503420243497863 238336606254755130365246795)
    ·
      refine ⟨357504909382132695547870193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 238336606254755130365246795 357504909382132695547870193)
      ·
        refine ⟨268128682036599521660902645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 357504909382132695547870193 268128682036599521660902645)
        ·
          refine ⟨25137063940931205155709623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 268128682036599521660902645 25137063940931205155709623)
          ·
            refine ⟨37705595911396807733564435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25137063940931205155709623 37705595911396807733564435)
            ·
              refine ⟨56558393867095211600346653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37705595911396807733564435 56558393867095211600346653)
              ·
                refine ⟨21209397700160704350129995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56558393867095211600346653 21209397700160704350129995)
                ·
                  refine ⟨31814096550241056525194993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21209397700160704350129995 31814096550241056525194993)
                  ·
                    refine ⟨23860572412680792393896245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 31814096550241056525194993 23860572412680792393896245)
                    ·
                      refine ⟨2236928663688824286927773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23860572412680792393896245 2236928663688824286927773)
                      ·
                        rfl

theorem cell23_4356403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 3, 1, 2, 5].length) (baseStart_4356403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4356403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4356403 prefixEnd_4356403 := by exact prefixLift 4356403
  have htrace : WordTrace (prefixWord ++ tailWord_4356403) baseStart_4356403 baseEnd_4356403 := by
    simpa [prefixWord, tailWord_4356403, baseEnd_4356403] using wordTrace_append hprefix tailTrace_4356403
  have hstable : (prefixWord ++ tailWord_4356403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4356403).length < 2 ^ (prefixWord ++ tailWord_4356403).sum := by decide
  have hdescent : baseEnd_4356403 < baseStart_4356403 := by decide
  rcases family_descends (prefixWord ++ tailWord_4356403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4356430 : List Nat := [4, 1, 1, 1, 1, 1, 2, 5, 2, 1, 4]
def baseStart_4356430 : Nat := 118140960795 + 4356430 * 2 ^ 59
def prefixEnd_4356430 : Nat := 4983230072969 + 3 ^ 40 * 4356430 * 2
def baseEnd_4356430 : Nat := 2236942527666495681290149

theorem tailTrace_4356430 : CollatzResearch.WordTrace tailWord_4356430 prefixEnd_4356430 2236942527666495681290149 := by
  unfold tailWord_4356430
  simp only [CollatzResearch.WordTrace]
  refine ⟨19861506950925700481841343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 105928037071603735903153829 19861506950925700481841343)
  ·
    refine ⟨29792260426388550722762015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19861506950925700481841343 29792260426388550722762015)
    ·
      refine ⟨44688390639582826084143023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29792260426388550722762015 44688390639582826084143023)
      ·
        refine ⟨67032585959374239126214535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44688390639582826084143023 67032585959374239126214535)
        ·
          refine ⟨100548878939061358689321803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67032585959374239126214535 100548878939061358689321803)
          ·
            refine ⟨150823318408592038033982705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100548878939061358689321803 150823318408592038033982705)
            ·
              refine ⟨113117488806444028525487029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 150823318408592038033982705 113117488806444028525487029)
              ·
                refine ⟨10604764575604127674264409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 113117488806444028525487029 10604764575604127674264409)
                ·
                  refine ⟨7953573431703095755698307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10604764575604127674264409 7953573431703095755698307)
                  ·
                    refine ⟨11930360147554643633547461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7953573431703095755698307 11930360147554643633547461)
                    ·
                      refine ⟨2236942527666495681290149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11930360147554643633547461 2236942527666495681290149)
                      ·
                        rfl

theorem cell23_4356430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 5, 2, 1, 4].length) (baseStart_4356430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4356430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4356430 prefixEnd_4356430 := by exact prefixLift 4356430
  have htrace : WordTrace (prefixWord ++ tailWord_4356430) baseStart_4356430 baseEnd_4356430 := by
    simpa [prefixWord, tailWord_4356430, baseEnd_4356430] using wordTrace_append hprefix tailTrace_4356430
  have hstable : (prefixWord ++ tailWord_4356430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4356430).length < 2 ^ (prefixWord ++ tailWord_4356430).sum := by decide
  have hdescent : baseEnd_4356430 < baseStart_4356430 := by decide
  rcases family_descends (prefixWord ++ tailWord_4356430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4356457 : List Nat := [1, 2, 1, 1, 1, 3, 3, 6, 1, 4]
def baseStart_4356457 : Nat := 118140960795 + 4356457 * 2 ^ 59
def prefixEnd_4356457 : Nat := 4983230072969 + 3 ^ 40 * 4356457 * 2
def baseEnd_4356457 : Nat := 745652130548055691884175

theorem tailTrace_4356457 : CollatzResearch.WordTrace tailWord_4356457 prefixEnd_4356457 745652130548055691884175 := by
  unfold tailWord_4356457
  simp only [CollatzResearch.WordTrace]
  refine ⟨158893040378307787465963625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105928693585538524977309083 158893040378307787465963625)
  ·
    refine ⟨119169780283730840599472719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 158893040378307787465963625 119169780283730840599472719)
    ·
      refine ⟨178754670425596260899209079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119169780283730840599472719 178754670425596260899209079)
      ·
        refine ⟨268132005638394391348813619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 178754670425596260899209079 268132005638394391348813619)
        ·
          refine ⟨402198008457591587023220429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 268132005638394391348813619 402198008457591587023220429)
          ·
            refine ⟨150824253171596845133707661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 402198008457591587023220429 150824253171596845133707661)
            ·
              refine ⟨56559094939348816925140373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 150824253171596845133707661 56559094939348816925140373)
              ·
                refine ⟨2651207575281975793365955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 56559094939348816925140373 2651207575281975793365955)
                ·
                  refine ⟨3976811362922963690048933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2651207575281975793365955 3976811362922963690048933)
                  ·
                    refine ⟨745652130548055691884175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3976811362922963690048933 745652130548055691884175)
                    ·
                      rfl

theorem cell23_4356457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 6, 1, 4].length) (baseStart_4356457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4356457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4356457 prefixEnd_4356457 := by exact prefixLift 4356457
  have htrace : WordTrace (prefixWord ++ tailWord_4356457) baseStart_4356457 baseEnd_4356457 := by
    simpa [prefixWord, tailWord_4356457, baseEnd_4356457] using wordTrace_append hprefix tailTrace_4356457
  have hstable : (prefixWord ++ tailWord_4356457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4356457).length < 2 ^ (prefixWord ++ tailWord_4356457).sum := by decide
  have hdescent : baseEnd_4356457 < baseStart_4356457 := by decide
  rcases family_descends (prefixWord ++ tailWord_4356457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4356473 : List Nat := [1, 2, 1, 3, 2, 1, 1, 1, 3, 2, 6]
def baseStart_4356473 : Nat := 118140960795 + 4356473 * 2 ^ 59
def prefixEnd_4356473 : Nat := 4983230072969 + 3 ^ 40 * 4356473 * 2
def baseEnd_4356473 : Nat := 2236964607334639013052451

theorem tailTrace_4356473 : CollatzResearch.WordTrace tailWord_4356473 prefixEnd_4356473 2236964607334639013052451 := by
  unfold tailWord_4356473
  simp only [CollatzResearch.WordTrace]
  refine ⟨158893623946249822198546073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105929082630833214799030715 158893623946249822198546073)
  ·
    refine ⟨119170217959687366648909555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 158893623946249822198546073 119170217959687366648909555)
    ·
      refine ⟨178755326939531049973364333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119170217959687366648909555 178755326939531049973364333)
      ·
        refine ⟨67033247602324143740011625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 178755326939531049973364333 67033247602324143740011625)
        ·
          refine ⟨50274935701743107805008719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67033247602324143740011625 50274935701743107805008719)
          ·
            refine ⟨75412403552614661707513079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50274935701743107805008719 75412403552614661707513079)
            ·
              refine ⟨113118605328921992561269619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75412403552614661707513079 113118605328921992561269619)
              ·
                refine ⟨169677907993382988841904429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 113118605328921992561269619 169677907993382988841904429)
                ·
                  refine ⟨63629215497518620815714161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 169677907993382988841904429 63629215497518620815714161)
                  ·
                    refine ⟨47721911623138965611785621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 63629215497518620815714161 47721911623138965611785621)
                    ·
                      refine ⟨2236964607334639013052451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 47721911623138965611785621 2236964607334639013052451)
                      ·
                        rfl

theorem cell23_4356473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 1, 3, 2, 6].length) (baseStart_4356473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4356473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4356473 prefixEnd_4356473 := by exact prefixLift 4356473
  have htrace : WordTrace (prefixWord ++ tailWord_4356473) baseStart_4356473 baseEnd_4356473 := by
    simpa [prefixWord, tailWord_4356473, baseEnd_4356473] using wordTrace_append hprefix tailTrace_4356473
  have hstable : (prefixWord ++ tailWord_4356473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4356473).length < 2 ^ (prefixWord ++ tailWord_4356473).sum := by decide
  have hdescent : baseEnd_4356473 < baseStart_4356473 := by decide
  rcases family_descends (prefixWord ++ tailWord_4356473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4356530 : List Nat := [3, 2, 1, 1, 1, 1, 4, 3, 1, 6]
def baseStart_4356530 : Nat := 118140960795 + 4356530 * 2 ^ 59
def prefixEnd_4356530 : Nat := 4983230072969 + 3 ^ 40 * 4356530 * 2
def baseEnd_4356530 : Nat := 745664625243981763346563

theorem tailTrace_4356530 : CollatzResearch.WordTrace tailWord_4356530 prefixEnd_4356530 745664625243981763346563 := by
  unfold tailWord_4356530
  simp only [CollatzResearch.WordTrace]
  refine ⟨39723925726760830233342761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105930468604695547288914029 39723925726760830233342761)
  ·
    refine ⟨29792944295070622675007071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39723925726760830233342761 29792944295070622675007071)
    ·
      refine ⟨44689416442605934012510607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29792944295070622675007071 44689416442605934012510607)
      ·
        refine ⟨67034124663908901018765911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44689416442605934012510607 67034124663908901018765911)
        ·
          refine ⟨100551186995863351528148867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67034124663908901018765911 100551186995863351528148867)
          ·
            refine ⟨150826780493795027292223301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100551186995863351528148867 150826780493795027292223301)
            ·
              refine ⟨28280021342586567617291869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 150826780493795027292223301 28280021342586567617291869)
              ·
                refine ⟨10605008003469962856484451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28280021342586567617291869 10605008003469962856484451)
                ·
                  refine ⟨15907512005204944284726677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10605008003469962856484451 15907512005204944284726677)
                  ·
                    refine ⟨745664625243981763346563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15907512005204944284726677 745664625243981763346563)
                    ·
                      rfl

theorem cell23_4356530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 3, 1, 6].length) (baseStart_4356530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4356530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4356530 prefixEnd_4356530 := by exact prefixLift 4356530
  have htrace : WordTrace (prefixWord ++ tailWord_4356530) baseStart_4356530 baseEnd_4356530 := by
    simpa [prefixWord, tailWord_4356530, baseEnd_4356530] using wordTrace_append hprefix tailTrace_4356530
  have hstable : (prefixWord ++ tailWord_4356530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4356530).length < 2 ^ (prefixWord ++ tailWord_4356530).sum := by decide
  have hdescent : baseEnd_4356530 < baseStart_4356530 := by decide
  rcases family_descends (prefixWord ++ tailWord_4356530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4356537 : List Nat := [1, 2, 1, 4, 3, 2, 1, 1, 3, 1, 4]
def baseStart_4356537 : Nat := 118140960795 + 4356537 * 2 ^ 59
def prefixEnd_4356537 : Nat := 4983230072969 + 3 ^ 40 * 4356537 * 2
def baseEnd_4356537 : Nat := 2236997470096526762652157

theorem tailTrace_4356537 : CollatzResearch.WordTrace tailWord_4356537 prefixEnd_4356537 2236997470096526762652157 := by
  unfold tailWord_4356537
  simp only [CollatzResearch.WordTrace]
  refine ⟨158895958218017961128875865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105930638812011974085917243 158895958218017961128875865)
  ·
    refine ⟨119171968663513470846656899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 158895958218017961128875865 119171968663513470846656899)
    ·
      refine ⟨178757952995270206269985349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119171968663513470846656899 178757952995270206269985349)
      ·
        refine ⟨33517116186613163675622253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 178757952995270206269985349 33517116186613163675622253)
        ·
          refine ⟨12568918569979936378358345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33517116186613163675622253 12568918569979936378358345)
          ·
            refine ⟨9426688927484952283768759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12568918569979936378358345 9426688927484952283768759)
            ·
              refine ⟨14140033391227428425653139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9426688927484952283768759 14140033391227428425653139)
              ·
                refine ⟨21210050086841142638479709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14140033391227428425653139 21210050086841142638479709)
                ·
                  refine ⟨7953768782565428489429891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21210050086841142638479709 7953768782565428489429891)
                  ·
                    refine ⟨11930653173848142734144837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7953768782565428489429891 11930653173848142734144837)
                    ·
                      refine ⟨2236997470096526762652157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11930653173848142734144837 2236997470096526762652157)
                      ·
                        rfl

theorem cell23_4356537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 1, 1, 3, 1, 4].length) (baseStart_4356537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4356537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4356537 prefixEnd_4356537 := by exact prefixLift 4356537
  have htrace : WordTrace (prefixWord ++ tailWord_4356537) baseStart_4356537 baseEnd_4356537 := by
    simpa [prefixWord, tailWord_4356537, baseEnd_4356537] using wordTrace_append hprefix tailTrace_4356537
  have hstable : (prefixWord ++ tailWord_4356537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4356537).length < 2 ^ (prefixWord ++ tailWord_4356537).sum := by decide
  have hdescent : baseEnd_4356537 < baseStart_4356537 := by decide
  rcases family_descends (prefixWord ++ tailWord_4356537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4356554 : List Nat := [3, 1, 2, 1, 2, 2, 5, 1, 1, 1, 4]
def baseStart_4356554 : Nat := 118140960795 + 4356554 * 2 ^ 59
def prefixEnd_4356554 : Nat := 4983230072969 + 3 ^ 40 * 4356554 * 2
def baseEnd_4356554 : Nat := 2237006199267653196139579

theorem tailTrace_4356554 : CollatzResearch.WordTrace tailWord_4356554 prefixEnd_4356554 2237006199267653196139579 := by
  unfold tailWord_4356554
  simp only [CollatzResearch.WordTrace]
  refine ⟨39724144564739093258061179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105931052172637582021496477 39724144564739093258061179)
  ·
    refine ⟨59586216847108639887091769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39724144564739093258061179 59586216847108639887091769)
    ·
      refine ⟨44689662635331479915318827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59586216847108639887091769 44689662635331479915318827)
      ·
        refine ⟨67034493952997219872978241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44689662635331479915318827 67034493952997219872978241)
        ·
          refine ⟨50275870464747914904733681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67034493952997219872978241 50275870464747914904733681)
          ·
            refine ⟨37706902848560936178550261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50275870464747914904733681 37706902848560936178550261)
            ·
              refine ⟨3535022142052587766739087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 37706902848560936178550261 3535022142052587766739087)
              ·
                refine ⟨5302533213078881650108631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3535022142052587766739087 5302533213078881650108631)
                ·
                  refine ⟨7953799819618322475162947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5302533213078881650108631 7953799819618322475162947)
                  ·
                    refine ⟨11930699729427483712744421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7953799819618322475162947 11930699729427483712744421)
                    ·
                      refine ⟨2237006199267653196139579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11930699729427483712744421 2237006199267653196139579)
                      ·
                        rfl

theorem cell23_4356554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 5, 1, 1, 1, 4].length) (baseStart_4356554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4356554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4356554 prefixEnd_4356554 := by exact prefixLift 4356554
  have htrace : WordTrace (prefixWord ++ tailWord_4356554) baseStart_4356554 baseEnd_4356554 := by
    simpa [prefixWord, tailWord_4356554, baseEnd_4356554] using wordTrace_append hprefix tailTrace_4356554
  have hstable : (prefixWord ++ tailWord_4356554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4356554).length < 2 ^ (prefixWord ++ tailWord_4356554).sum := by decide
  have hdescent : baseEnd_4356554 < baseStart_4356554 := by decide
  rcases family_descends (prefixWord ++ tailWord_4356554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4356564 : List Nat := [2, 4, 1, 2, 2, 1, 1, 4, 2, 4]
def baseStart_4356564 : Nat := 118140960795 + 4356564 * 2 ^ 59
def prefixEnd_4356564 : Nat := 4983230072969 + 3 ^ 40 * 4356564 * 2
def baseEnd_4356564 : Nat := 745670444691399385671511

theorem tailTrace_4356564 : CollatzResearch.WordTrace tailWord_4356564 prefixEnd_4356564 745670444691399385671511 := by
  unfold tailWord_4356564
  simp only [CollatzResearch.WordTrace]
  refine ⟨79448471494460072370054373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105931295325946763160072497 79448471494460072370054373)
  ·
    refine ⟨14896588405211263569385195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 79448471494460072370054373 14896588405211263569385195)
    ·
      refine ⟨22344882607816895354077793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14896588405211263569385195 22344882607816895354077793)
      ·
        refine ⟨16758661955862671515558345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22344882607816895354077793 16758661955862671515558345)
        ·
          refine ⟨12568996466897003636668759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16758661955862671515558345 12568996466897003636668759)
          ·
            refine ⟨18853494700345505455003139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12568996466897003636668759 18853494700345505455003139)
            ·
              refine ⟨28280242050518258182504709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18853494700345505455003139 28280242050518258182504709)
              ·
                refine ⟨5302545384472173409219633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28280242050518258182504709 5302545384472173409219633)
                ·
                  refine ⟨3976909038354130056914725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5302545384472173409219633 3976909038354130056914725)
                  ·
                    refine ⟨745670444691399385671511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3976909038354130056914725 745670444691399385671511)
                    ·
                      rfl

theorem cell23_4356564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 4, 2, 4].length) (baseStart_4356564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4356564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4356564 prefixEnd_4356564 := by exact prefixLift 4356564
  have htrace : WordTrace (prefixWord ++ tailWord_4356564) baseStart_4356564 baseEnd_4356564 := by
    simpa [prefixWord, tailWord_4356564, baseEnd_4356564] using wordTrace_append hprefix tailTrace_4356564
  have hstable : (prefixWord ++ tailWord_4356564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4356564).length < 2 ^ (prefixWord ++ tailWord_4356564).sum := by decide
  have hdescent : baseEnd_4356564 < baseStart_4356564 := by decide
  rcases family_descends (prefixWord ++ tailWord_4356564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4356587 : List Nat := [1, 1, 1, 1, 2, 3, 6, 1, 1, 3, 3]
def baseStart_4356587 : Nat := 118140960795 + 4356587 * 2 ^ 59
def prefixEnd_4356587 : Nat := 4983230072969 + 3 ^ 40 * 4356587 * 2
def baseEnd_4356587 : Nat := 2237023144129251567026927

theorem tailTrace_4356587 : CollatzResearch.WordTrace tailWord_4356587 prefixEnd_4356587 2237023144129251567026927 := by
  unfold tailWord_4356587
  simp only [CollatzResearch.WordTrace]
  refine ⟨158897781867836819668196015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105931854578557879778797343 158897781867836819668196015)
  ·
    refine ⟨238346672801755229502294023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158897781867836819668196015 238346672801755229502294023)
    ·
      refine ⟨357520009202632844253441035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 238346672801755229502294023 357520009202632844253441035)
      ·
        refine ⟨536280013803949266380161553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 357520009202632844253441035 536280013803949266380161553)
        ·
          refine ⟨402210010352961949785121165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 536280013803949266380161553 402210010352961949785121165)
          ·
            refine ⟨150828753882360731169420437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 402210010352961949785121165 150828753882360731169420437)
            ·
              refine ⟨7070097838235659273566583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 150828753882360731169420437 7070097838235659273566583)
              ·
                refine ⟨10605146757353488910349875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7070097838235659273566583 10605146757353488910349875)
                ·
                  refine ⟨15907720136030233365524813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10605146757353488910349875 15907720136030233365524813)
                  ·
                    refine ⟨5965395051011337512071805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15907720136030233365524813 5965395051011337512071805)
                    ·
                      refine ⟨2237023144129251567026927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5965395051011337512071805 2237023144129251567026927)
                      ·
                        rfl

theorem cell23_4356587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 6, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 6, 1, 1, 3, 3].length) (baseStart_4356587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4356587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4356587 prefixEnd_4356587 := by exact prefixLift 4356587
  have htrace : WordTrace (prefixWord ++ tailWord_4356587) baseStart_4356587 baseEnd_4356587 := by
    simpa [prefixWord, tailWord_4356587, baseEnd_4356587] using wordTrace_append hprefix tailTrace_4356587
  have hstable : (prefixWord ++ tailWord_4356587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4356587).length < 2 ^ (prefixWord ++ tailWord_4356587).sum := by decide
  have hdescent : baseEnd_4356587 < baseStart_4356587 := by decide
  rcases family_descends (prefixWord ++ tailWord_4356587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4356594 : List Nat := [3, 2, 1, 4, 2, 1, 3, 7]
def baseStart_4356594 : Nat := 118140960795 + 4356594 * 2 ^ 59
def prefixEnd_4356594 : Nat := 4983230072969 + 3 ^ 40 * 4356594 * 2
def baseEnd_4356594 : Nat := 82852842166438260727385

theorem tailTrace_4356594 : CollatzResearch.WordTrace tailWord_4356594 prefixEnd_4356594 82852842166438260727385 := by
  unfold tailWord_4356594
  simp only [CollatzResearch.WordTrace]
  refine ⟨39724509294702864965925209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105932024785874306575800557 39724509294702864965925209)
  ·
    refine ⟨29793381971027148724443907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39724509294702864965925209 29793381971027148724443907)
    ·
      refine ⟨44690072956540723086665861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29793381971027148724443907 44690072956540723086665861)
      ·
        refine ⟨8379388679351385578749849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 44690072956540723086665861 8379388679351385578749849)
        ·
          refine ⟨6284541509513539184062387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8379388679351385578749849 6284541509513539184062387)
          ·
            refine ⟨9426812264270308776093581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6284541509513539184062387 9426812264270308776093581)
            ·
              refine ⟨3535054599101365791035093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9426812264270308776093581 3535054599101365791035093)
              ·
                refine ⟨82852842166438260727385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3535054599101365791035093 82852842166438260727385)
                ·
                  rfl

theorem cell23_4356594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 3, 7].length) (baseStart_4356594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4356594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4356594 prefixEnd_4356594 := by exact prefixLift 4356594
  have htrace : WordTrace (prefixWord ++ tailWord_4356594) baseStart_4356594 baseEnd_4356594 := by
    simpa [prefixWord, tailWord_4356594, baseEnd_4356594] using wordTrace_append hprefix tailTrace_4356594
  have hstable : (prefixWord ++ tailWord_4356594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4356594).length < 2 ^ (prefixWord ++ tailWord_4356594).sum := by decide
  have hdescent : baseEnd_4356594 < baseStart_4356594 := by decide
  rcases family_descends (prefixWord ++ tailWord_4356594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4356600 : List Nat := [2, 1, 2, 1, 1, 4, 2, 1, 2, 2, 5]
def baseStart_4356600 : Nat := 118140960795 + 4356600 * 2 ^ 59
def prefixEnd_4356600 : Nat := 4983230072969 + 3 ^ 40 * 4356600 * 2
def baseEnd_4356600 : Nat := 2237029819377760016164367

theorem tailTrace_4356600 : CollatzResearch.WordTrace tailWord_4356600 prefixEnd_4356600 2237029819377760016164367 := by
  unfold tailWord_4356600
  simp only [CollatzResearch.WordTrace]
  refine ⟨79449128008394861444209627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105932170677859815258946169 79449128008394861444209627)
  ·
    refine ⟨119173692012592292166314441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79449128008394861444209627 119173692012592292166314441)
    ·
      refine ⟨89380269009444219124735831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119173692012592292166314441 89380269009444219124735831)
      ·
        refine ⟨134070403514166328687103747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89380269009444219124735831 134070403514166328687103747)
        ·
          refine ⟨201105605271249493030655621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 134070403514166328687103747 201105605271249493030655621)
          ·
            refine ⟨37707300988359279943247929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 201105605271249493030655621 37707300988359279943247929)
            ·
              refine ⟨28280475741269459957435947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37707300988359279943247929 28280475741269459957435947)
              ·
                refine ⟨42420713611904189936153921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28280475741269459957435947 42420713611904189936153921)
                ·
                  refine ⟨31815535208928142452115441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42420713611904189936153921 31815535208928142452115441)
                  ·
                    refine ⟨23861651406696106839086581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 31815535208928142452115441 23861651406696106839086581)
                    ·
                      refine ⟨2237029819377760016164367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23861651406696106839086581 2237029819377760016164367)
                      ·
                        rfl

theorem cell23_4356600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 1, 2, 2, 5].length) (baseStart_4356600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4356600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4356600 prefixEnd_4356600 := by exact prefixLift 4356600
  have htrace : WordTrace (prefixWord ++ tailWord_4356600) baseStart_4356600 baseEnd_4356600 := by
    simpa [prefixWord, tailWord_4356600, baseEnd_4356600] using wordTrace_append hprefix tailTrace_4356600
  have hstable : (prefixWord ++ tailWord_4356600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4356600).length < 2 ^ (prefixWord ++ tailWord_4356600).sum := by decide
  have hdescent : baseEnd_4356600 < baseStart_4356600 := by decide
  rcases family_descends (prefixWord ++ tailWord_4356600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4356637 : List Nat := [1, 4, 2, 2, 1, 2, 2, 1, 2, 6]
def baseStart_4356637 : Nat := 118140960795 + 4356637 * 2 ^ 59
def prefixEnd_4356637 : Nat := 4983230072969 + 3 ^ 40 * 4356637 * 2
def baseEnd_4356637 : Nat := 745682939387325457133899

theorem tailTrace_4356637 : CollatzResearch.WordTrace tailWord_4356637 prefixEnd_4356637 745682939387325457133899 := by
  unfold tailWord_4356637
  simp only [CollatzResearch.WordTrace]
  refine ⟨158899605517655678207516165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105933070345103785471677443 158899605517655678207516165)
  ·
    refine ⟨29793676034560439663909281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 158899605517655678207516165 29793676034560439663909281)
    ·
      refine ⟨22345257025920329747931961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29793676034560439663909281 22345257025920329747931961)
      ·
        refine ⟨16758942769440247310948971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22345257025920329747931961 16758942769440247310948971)
        ·
          refine ⟨25138414154160370966423457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16758942769440247310948971 25138414154160370966423457)
          ·
            refine ⟨18853810615620278224817593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25138414154160370966423457 18853810615620278224817593)
            ·
              refine ⟨14140357961715208668613195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18853810615620278224817593 14140357961715208668613195)
              ·
                refine ⟨21210536942572813002919793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14140357961715208668613195 21210536942572813002919793)
                ·
                  refine ⟨15907902706929609752189845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21210536942572813002919793 15907902706929609752189845)
                  ·
                    refine ⟨745682939387325457133899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15907902706929609752189845 745682939387325457133899)
                    ·
                      rfl

theorem cell23_4356637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 2, 1, 2, 6].length) (baseStart_4356637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4356637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4356637 prefixEnd_4356637 := by exact prefixLift 4356637
  have htrace : WordTrace (prefixWord ++ tailWord_4356637) baseStart_4356637 baseEnd_4356637 := by
    simpa [prefixWord, tailWord_4356637, baseEnd_4356637] using wordTrace_append hprefix tailTrace_4356637
  have hstable : (prefixWord ++ tailWord_4356637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4356637).length < 2 ^ (prefixWord ++ tailWord_4356637).sum := by decide
  have hdescent : baseEnd_4356637 < baseStart_4356637 := by decide
  rcases family_descends (prefixWord ++ tailWord_4356637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4356648 : List Nat := [2, 1, 5, 2, 1, 2, 2, 2, 1, 3, 2]
def baseStart_4356648 : Nat := 118140960795 + 4356648 * 2 ^ 59
def prefixEnd_4356648 : Nat := 4983230072969 + 3 ^ 40 * 4356648 * 2
def baseEnd_4356648 : Nat := 2237054466449175828364147

theorem tailTrace_4356648 : CollatzResearch.WordTrace tailWord_4356648 prefixEnd_4356648 2237054466449175828364147 := by
  unfold tailWord_4356648
  simp only [CollatzResearch.WordTrace]
  refine ⟨79450003360307913543083299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105933337813743884724111065 79450003360307913543083299)
  ·
    refine ⟨119175005040461870314624949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79450003360307913543083299 119175005040461870314624949)
    ·
      refine ⟨11172656722543300341996089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 119175005040461870314624949 11172656722543300341996089)
      ·
        refine ⟨8379492541907475256497067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11172656722543300341996089 8379492541907475256497067)
        ·
          refine ⟨12569238812861212884745601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8379492541907475256497067 12569238812861212884745601)
          ·
            refine ⟨9426929109645909663559201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12569238812861212884745601 9426929109645909663559201)
            ·
              refine ⟨7070196832234432247669401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9426929109645909663559201 7070196832234432247669401)
              ·
                refine ⟨5302647624175824185752051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7070196832234432247669401 5302647624175824185752051)
                ·
                  refine ⟨7953971436263736278628077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5302647624175824185752051 7953971436263736278628077)
                  ·
                    refine ⟨2982739288598901104485529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7953971436263736278628077 2982739288598901104485529)
                    ·
                      refine ⟨2237054466449175828364147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2982739288598901104485529 2237054466449175828364147)
                      ·
                        rfl

theorem cell23_4356648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 2, 2, 1, 3, 2].length) (baseStart_4356648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4356648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4356648 prefixEnd_4356648 := by exact prefixLift 4356648
  have htrace : WordTrace (prefixWord ++ tailWord_4356648) baseStart_4356648 baseEnd_4356648 := by
    simpa [prefixWord, tailWord_4356648, baseEnd_4356648] using wordTrace_append hprefix tailTrace_4356648
  have hstable : (prefixWord ++ tailWord_4356648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4356648).length < 2 ^ (prefixWord ++ tailWord_4356648).sum := by decide
  have hdescent : baseEnd_4356648 < baseStart_4356648 := by decide
  rcases family_descends (prefixWord ++ tailWord_4356648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4356714 : List Nat := [3, 1, 3, 2, 1, 1, 4, 1, 2, 5]
def baseStart_4356714 : Nat := 118140960795 + 4356714 * 2 ^ 59
def prefixEnd_4356714 : Nat := 4983230072969 + 3 ^ 40 * 4356714 * 2
def baseEnd_4356714 : Nat := 745696118724124190046281

theorem tailTrace_4356714 : CollatzResearch.WordTrace tailWord_4356714 prefixEnd_4356714 745696118724124190046281 := by
  unfold tailWord_4356714
  simp only [CollatzResearch.WordTrace]
  refine ⟨39725603484594180089517299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105934942625584480238712797 39725603484594180089517299)
  ·
    refine ⟨59588405226891270134275949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39725603484594180089517299 59588405226891270134275949)
    ·
      refine ⟨22345651960084226300353481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59588405226891270134275949 22345651960084226300353481)
      ·
        refine ⟨16759238970063169725265111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22345651960084226300353481 16759238970063169725265111)
        ·
          refine ⟨25138858455094754587897667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16759238970063169725265111 25138858455094754587897667)
          ·
            refine ⟨37708287682642131881846501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25138858455094754587897667 37708287682642131881846501)
            ·
              refine ⟨7070303940495399727846219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37708287682642131881846501 7070303940495399727846219)
              ·
                refine ⟨10605455910743099591769329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7070303940495399727846219 10605455910743099591769329)
                ·
                  refine ⟨7954091933057324693826997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10605455910743099591769329 7954091933057324693826997)
                  ·
                    refine ⟨745696118724124190046281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7954091933057324693826997 745696118724124190046281)
                    ·
                      rfl

theorem cell23_4356714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 4, 1, 2, 5].length) (baseStart_4356714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4356714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4356714 prefixEnd_4356714 := by exact prefixLift 4356714
  have htrace : WordTrace (prefixWord ++ tailWord_4356714) baseStart_4356714 baseEnd_4356714 := by
    simpa [prefixWord, tailWord_4356714, baseEnd_4356714] using wordTrace_append hprefix tailTrace_4356714
  have hstable : (prefixWord ++ tailWord_4356714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4356714).length < 2 ^ (prefixWord ++ tailWord_4356714).sum := by decide
  have hdescent : baseEnd_4356714 < baseStart_4356714 := by decide
  rcases family_descends (prefixWord ++ tailWord_4356714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4356737 : List Nat := [1, 2, 4, 2, 1, 1, 1, 1, 2, 3, 5]
def baseStart_4356737 : Nat := 118140960795 + 4356737 * 2 ^ 59
def prefixEnd_4356737 : Nat := 4983230072969 + 3 ^ 40 * 4356737 * 2
def baseEnd_4356737 : Nat := 2237100166227425980151237

theorem tailTrace_4356737 : CollatzResearch.WordTrace tailWord_4356737 prefixEnd_4356737 2237100166227425980151237 := by
  unfold tailWord_4356737
  simp only [CollatzResearch.WordTrace]
  refine ⟨158903252817293395286156465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105935501878195596857437643 158903252817293395286156465)
  ·
    refine ⟨119177439612970046464617349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 158903252817293395286156465 119177439612970046464617349)
    ·
      refine ⟨22345769927431883712115753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 119177439612970046464617349 22345769927431883712115753)
      ·
        refine ⟨16759327445573912784086815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22345769927431883712115753 16759327445573912784086815)
        ·
          refine ⟨25138991168360869176130223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16759327445573912784086815 25138991168360869176130223)
          ·
            refine ⟨37708486752541303764195335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25138991168360869176130223 37708486752541303764195335)
            ·
              refine ⟨56562730128811955646293003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37708486752541303764195335 56562730128811955646293003)
              ·
                refine ⟨84844095193217933469439505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56562730128811955646293003 84844095193217933469439505)
                ·
                  refine ⟨63633071394913450102079629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 84844095193217933469439505 63633071394913450102079629)
                  ·
                    refine ⟨23862401773092543788279861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 63633071394913450102079629 23862401773092543788279861)
                    ·
                      refine ⟨2237100166227425980151237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23862401773092543788279861 2237100166227425980151237)
                      ·
                        rfl

theorem cell23_4356737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 1, 2, 3, 5].length) (baseStart_4356737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4356737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4356737 prefixEnd_4356737 := by exact prefixLift 4356737
  have htrace : WordTrace (prefixWord ++ tailWord_4356737) baseStart_4356737 baseEnd_4356737 := by
    simpa [prefixWord, tailWord_4356737, baseEnd_4356737] using wordTrace_append hprefix tailTrace_4356737
  have hstable : (prefixWord ++ tailWord_4356737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4356737).length < 2 ^ (prefixWord ++ tailWord_4356737).sum := by decide
  have hdescent : baseEnd_4356737 < baseStart_4356737 := by decide
  rcases family_descends (prefixWord ++ tailWord_4356737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4356768 : List Nat := [2, 1, 1, 4, 5, 1, 1, 1, 2, 1, 4]
def baseStart_4356768 : Nat := 118140960795 + 4356768 * 2 ^ 59
def prefixEnd_4356768 : Nat := 4983230072969 + 3 ^ 40 * 4356768 * 2
def baseEnd_4356768 : Nat := 2237116084127715358863595

theorem tailTrace_4356768 : CollatzResearch.WordTrace tailWord_4356768 prefixEnd_4356768 2237116084127715358863595 := by
  unfold tailWord_4356768
  simp only [CollatzResearch.WordTrace]
  refine ⟨79452191740090543790267479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105936255653454058387023305 79452191740090543790267479)
  ·
    refine ⟨119178287610135815685401219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79452191740090543790267479 119178287610135815685401219)
    ·
      refine ⟨178767431415203723528101829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119178287610135815685401219 178767431415203723528101829)
      ·
        refine ⟨33518893390350698161519093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 178767431415203723528101829 33518893390350698161519093)
        ·
          refine ⟨3142396255345377952642415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 33518893390350698161519093 3142396255345377952642415)
          ·
            refine ⟨4713594383018066928963623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3142396255345377952642415 4713594383018066928963623)
            ·
              refine ⟨7070391574527100393445435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4713594383018066928963623 7070391574527100393445435)
              ·
                refine ⟨10605587361790650590168153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7070391574527100393445435 10605587361790650590168153)
                ·
                  refine ⟨7954190521342987942626115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10605587361790650590168153 7954190521342987942626115)
                  ·
                    refine ⟨11931285782014481913939173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7954190521342987942626115 11931285782014481913939173)
                    ·
                      refine ⟨2237116084127715358863595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11931285782014481913939173 2237116084127715358863595)
                      ·
                        rfl

theorem cell23_4356768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 1, 1, 1, 2, 1, 4].length) (baseStart_4356768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4356768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4356768 prefixEnd_4356768 := by exact prefixLift 4356768
  have htrace : WordTrace (prefixWord ++ tailWord_4356768) baseStart_4356768 baseEnd_4356768 := by
    simpa [prefixWord, tailWord_4356768, baseEnd_4356768] using wordTrace_append hprefix tailTrace_4356768
  have hstable : (prefixWord ++ tailWord_4356768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4356768).length < 2 ^ (prefixWord ++ tailWord_4356768).sum := by decide
  have hdescent : baseEnd_4356768 < baseStart_4356768 := by decide
  rcases family_descends (prefixWord ++ tailWord_4356768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4356784 : List Nat := [2, 1, 1, 1, 2, 1, 3, 1, 7, 1, 3]
def baseStart_4356784 : Nat := 118140960795 + 4356784 * 2 ^ 59
def prefixEnd_4356784 : Nat := 4983230072969 + 3 ^ 40 * 4356784 * 2
def baseEnd_4356784 : Nat := 2237124299818187296263521

theorem tailTrace_4356784 : CollatzResearch.WordTrace tailWord_4356784 prefixEnd_4356784 2237124299818187296263521 := by
  unfold tailWord_4356784
  simp only [CollatzResearch.WordTrace]
  refine ⟨79452483524061561156558703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105936644698748748208744937 79452483524061561156558703)
  ·
    refine ⟨119178725286092341734838055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79452483524061561156558703 119178725286092341734838055)
    ·
      refine ⟨178768087929138512602257083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119178725286092341734838055 178768087929138512602257083)
      ·
        refine ⟨268152131893707768903385625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 178768087929138512602257083 268152131893707768903385625)
        ·
          refine ⟨201114098920280826677539219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 268152131893707768903385625 201114098920280826677539219)
          ·
            refine ⟨301671148380421240016308829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 201114098920280826677539219 301671148380421240016308829)
            ·
              refine ⟨113126680642657965006115811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 301671148380421240016308829 113126680642657965006115811)
              ·
                refine ⟨169690020963986947509173717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 113126680642657965006115811 169690020963986947509173717)
                ·
                  refine ⟨3977109866343444082246259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 169690020963986947509173717 3977109866343444082246259)
                  ·
                    refine ⟨5965664799515166123369389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3977109866343444082246259 5965664799515166123369389)
                    ·
                      refine ⟨2237124299818187296263521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5965664799515166123369389 2237124299818187296263521)
                      ·
                        rfl

theorem cell23_4356784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 1, 7, 1, 3].length) (baseStart_4356784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4356784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4356784 prefixEnd_4356784 := by exact prefixLift 4356784
  have htrace : WordTrace (prefixWord ++ tailWord_4356784) baseStart_4356784 baseEnd_4356784 := by
    simpa [prefixWord, tailWord_4356784, baseEnd_4356784] using wordTrace_append hprefix tailTrace_4356784
  have hstable : (prefixWord ++ tailWord_4356784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4356784).length < 2 ^ (prefixWord ++ tailWord_4356784).sum := by decide
  have hdescent : baseEnd_4356784 < baseStart_4356784 := by decide
  rcases family_descends (prefixWord ++ tailWord_4356784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4356791 : List Nat := [1, 1, 3, 1, 6, 2, 1, 2, 6]
def baseStart_4356791 : Nat := 118140960795 + 4356791 * 2 ^ 59
def prefixEnd_4356791 : Nat := 4983230072969 + 3 ^ 40 * 4356791 * 2
def baseEnd_4356791 : Nat := 248569766020307640986221

theorem tailTrace_4356791 : CollatzResearch.WordTrace tailWord_4356791 prefixEnd_4356791 248569766020307640986221 := by
  unfold tailWord_4356791
  simp only [CollatzResearch.WordTrace]
  refine ⟨158905222359097762508622227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105936814906065175005748151 158905222359097762508622227)
  ·
    refine ⟨238357833538646643762933341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158905222359097762508622227 238357833538646643762933341)
    ·
      refine ⟨89384187576992491411100003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 238357833538646643762933341 89384187576992491411100003)
      ·
        refine ⟨134076281365488737116650005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89384187576992491411100003 134076281365488737116650005)
        ·
          refine ⟨6284825689007284552342969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 134076281365488737116650005 6284825689007284552342969)
          ·
            refine ⟨4713619266755463414257227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6284825689007284552342969 4713619266755463414257227)
            ·
              refine ⟨7070428900133195121385841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4713619266755463414257227 7070428900133195121385841)
              ·
                refine ⟨5302821675099896341039381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7070428900133195121385841 5302821675099896341039381)
                ·
                  refine ⟨248569766020307640986221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5302821675099896341039381 248569766020307640986221)
                  ·
                    rfl

theorem cell23_4356791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 2, 1, 2, 6].length) (baseStart_4356791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4356791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4356791 prefixEnd_4356791 := by exact prefixLift 4356791
  have htrace : WordTrace (prefixWord ++ tailWord_4356791) baseStart_4356791 baseEnd_4356791 := by
    simpa [prefixWord, tailWord_4356791, baseEnd_4356791] using wordTrace_append hprefix tailTrace_4356791
  have hstable : (prefixWord ++ tailWord_4356791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4356791).length < 2 ^ (prefixWord ++ tailWord_4356791).sum := by decide
  have hdescent : baseEnd_4356791 < baseStart_4356791 := by decide
  rcases family_descends (prefixWord ++ tailWord_4356791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4356807 : List Nat := [1, 1, 4, 1, 1, 1, 2, 1, 2, 5, 4]
def baseStart_4356807 : Nat := 118140960795 + 4356807 * 2 ^ 59
def prefixEnd_4356807 : Nat := 4983230072969 + 3 ^ 40 * 4356807 * 2
def baseEnd_4356807 : Nat := 2237136109873240706275915

theorem tailTrace_4356807 : CollatzResearch.WordTrace tailWord_4356807 prefixEnd_4356807 2237136109873240706275915 := by
  unfold tailWord_4356807
  simp only [CollatzResearch.WordTrace]
  refine ⟨158905805927039797241204675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105937203951359864827469783 158905805927039797241204675)
  ·
    refine ⟨238358708890559695861807013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158905805927039797241204675 238358708890559695861807013)
    ·
      refine ⟨44692257916979942974088815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 238358708890559695861807013 44692257916979942974088815)
      ·
        refine ⟨67038386875469914461133223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44692257916979942974088815 67038386875469914461133223)
        ·
          refine ⟨100557580313204871691699835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67038386875469914461133223 100557580313204871691699835)
          ·
            refine ⟨150836370469807307537549753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100557580313204871691699835 150836370469807307537549753)
            ·
              refine ⟨113127277852355480653162315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 150836370469807307537549753 113127277852355480653162315)
              ·
                refine ⟨169690916778533220979743473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 113127277852355480653162315 169690916778533220979743473)
                ·
                  refine ⟨127268187583899915734807605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 169690916778533220979743473 127268187583899915734807605)
                  ·
                    refine ⟨11931392585990617100138213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 127268187583899915734807605 11931392585990617100138213)
                    ·
                      refine ⟨2237136109873240706275915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11931392585990617100138213 2237136109873240706275915)
                      ·
                        rfl

theorem cell23_4356807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 1, 2, 5, 4].length) (baseStart_4356807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4356807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4356807 prefixEnd_4356807 := by exact prefixLift 4356807
  have htrace : WordTrace (prefixWord ++ tailWord_4356807) baseStart_4356807 baseEnd_4356807 := by
    simpa [prefixWord, tailWord_4356807, baseEnd_4356807] using wordTrace_append hprefix tailTrace_4356807
  have hstable : (prefixWord ++ tailWord_4356807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4356807).length < 2 ^ (prefixWord ++ tailWord_4356807).sum := by decide
  have hdescent : baseEnd_4356807 < baseStart_4356807 := by decide
  rcases family_descends (prefixWord ++ tailWord_4356807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4356828 : List Nat := [2, 2, 5, 1, 1, 1, 2, 1, 1, 5, 2]
def baseStart_4356828 : Nat := 118140960795 + 4356828 * 2 ^ 59
def prefixEnd_4356828 : Nat := 4983230072969 + 3 ^ 40 * 4356828 * 2
def baseEnd_4356828 : Nat := 2237146892966985124113319

theorem tailTrace_4356828 : CollatzResearch.WordTrace tailWord_4356828 prefixEnd_4356828 2237146892966985124113319 := by
  unfold tailWord_4356828
  simp only [CollatzResearch.WordTrace]
  refine ⟨79453285929981858913859569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105937714573309145218479425 79453285929981858913859569)
  ·
    refine ⟨59589964447486394185394677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79453285929981858913859569 59589964447486394185394677)
    ·
      refine ⟨5586559166951849454880751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 59589964447486394185394677 5586559166951849454880751)
      ·
        refine ⟨8379838750427774182321127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5586559166951849454880751 8379838750427774182321127)
        ·
          refine ⟨12569758125641661273481691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8379838750427774182321127 12569758125641661273481691)
          ·
            refine ⟨18854637188462491910222537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12569758125641661273481691 18854637188462491910222537)
            ·
              refine ⟨14140977891346868932666903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18854637188462491910222537 14140977891346868932666903)
              ·
                refine ⟨21211466837020303399000355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14140977891346868932666903 21211466837020303399000355)
                ·
                  refine ⟨31817200255530455098500533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21211466837020303399000355 31817200255530455098500533)
                  ·
                    refine ⟨2982862523955980165484425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 31817200255530455098500533 2982862523955980165484425)
                    ·
                      refine ⟨2237146892966985124113319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2982862523955980165484425 2237146892966985124113319)
                      ·
                        rfl

theorem cell23_4356828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 2, 1, 1, 5, 2].length) (baseStart_4356828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4356828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4356828 prefixEnd_4356828 := by exact prefixLift 4356828
  have htrace : WordTrace (prefixWord ++ tailWord_4356828) baseStart_4356828 baseEnd_4356828 := by
    simpa [prefixWord, tailWord_4356828, baseEnd_4356828] using wordTrace_append hprefix tailTrace_4356828
  have hstable : (prefixWord ++ tailWord_4356828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4356828).length < 2 ^ (prefixWord ++ tailWord_4356828).sum := by decide
  have hdescent : baseEnd_4356828 < baseStart_4356828 := by decide
  rcases family_descends (prefixWord ++ tailWord_4356828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4356835 : List Nat := [1, 1, 1, 7, 1, 1, 3, 3, 1, 1, 3]
def baseStart_4356835 : Nat := 118140960795 + 4356835 * 2 ^ 59
def prefixEnd_4356835 : Nat := 4983230072969 + 3 ^ 40 * 4356835 * 2
def baseEnd_4356835 : Nat := 2237150487331566596725787

theorem tailTrace_4356835 : CollatzResearch.WordTrace tailWord_4356835 prefixEnd_4356835 2237150487331566596725787 := by
  unfold tailWord_4356835
  simp only [CollatzResearch.WordTrace]
  refine ⟨158906827170938358023223959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105937884780625572015482639 158906827170938358023223959)
  ·
    refine ⟨238360240756407537034835939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158906827170938358023223959 238360240756407537034835939)
    ·
      refine ⟨357540361134611305552253909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 238360240756407537034835939 357540361134611305552253909)
      ·
        refine ⟨8379852214092452473880951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 357540361134611305552253909 8379852214092452473880951)
        ·
          refine ⟨12569778321138678710821427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8379852214092452473880951 12569778321138678710821427)
          ·
            refine ⟨18854667481708018066232141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12569778321138678710821427 18854667481708018066232141)
            ·
              refine ⟨7070500305640506774837053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18854667481708018066232141 7070500305640506774837053)
              ·
                refine ⟨2651437614615190040563895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7070500305640506774837053 2651437614615190040563895)
                ·
                  refine ⟨3977156421922785060845843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2651437614615190040563895 3977156421922785060845843)
                  ·
                    refine ⟨5965734632884177591268765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3977156421922785060845843 5965734632884177591268765)
                    ·
                      refine ⟨2237150487331566596725787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5965734632884177591268765 2237150487331566596725787)
                      ·
                        rfl

theorem cell23_4356835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 3, 3, 1, 1, 3].length) (baseStart_4356835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4356835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4356835 prefixEnd_4356835 := by exact prefixLift 4356835
  have htrace : WordTrace (prefixWord ++ tailWord_4356835) baseStart_4356835 baseEnd_4356835 := by
    simpa [prefixWord, tailWord_4356835, baseEnd_4356835] using wordTrace_append hprefix tailTrace_4356835
  have hstable : (prefixWord ++ tailWord_4356835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4356835).length < 2 ^ (prefixWord ++ tailWord_4356835).sum := by decide
  have hdescent : baseEnd_4356835 < baseStart_4356835 := by decide
  rcases family_descends (prefixWord ++ tailWord_4356835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4356841 : List Nat := [1, 2, 1, 1, 1, 2, 4, 2, 5, 2, 2]
def baseStart_4356841 : Nat := 118140960795 + 4356841 * 2 ^ 59
def prefixEnd_4356841 : Nat := 4983230072969 + 3 ^ 40 * 4356841 * 2
def baseEnd_4356841 : Nat := 2237153568215493573250759

theorem tailTrace_4356841 : CollatzResearch.WordTrace tailWord_4356841 prefixEnd_4356841 2237153568215493573250759 := by
  unfold tailWord_4356841
  simp only [CollatzResearch.WordTrace]
  refine ⟨158907046008916621047942377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105938030672611080698628251 158907046008916621047942377)
  ·
    refine ⟨119180284506687465785956783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 158907046008916621047942377 119180284506687465785956783)
    ·
      refine ⟨178770426760031198678935175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119180284506687465785956783 178770426760031198678935175)
      ·
        refine ⟨268155640140046798018402763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 178770426760031198678935175 268155640140046798018402763)
        ·
          refine ⟨402233460210070197027604145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 268155640140046798018402763 402233460210070197027604145)
          ·
            refine ⟨301675095157552647770703109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 402233460210070197027604145 301675095157552647770703109)
            ·
              refine ⟨56564080342041121457006833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 301675095157552647770703109 56564080342041121457006833)
              ·
                refine ⟨42423060256530841092755125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56564080342041121457006833 42423060256530841092755125)
                ·
                  refine ⟨3977161899049766352445793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 42423060256530841092755125 3977161899049766352445793)
                  ·
                    refine ⟨2982871424287324764334345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3977161899049766352445793 2982871424287324764334345)
                    ·
                      refine ⟨2237153568215493573250759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2982871424287324764334345 2237153568215493573250759)
                      ·
                        rfl

theorem cell23_4356841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 2, 5, 2, 2].length) (baseStart_4356841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4356841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4356841 prefixEnd_4356841 := by exact prefixLift 4356841
  have htrace : WordTrace (prefixWord ++ tailWord_4356841) baseStart_4356841 baseEnd_4356841 := by
    simpa [prefixWord, tailWord_4356841, baseEnd_4356841] using wordTrace_append hprefix tailTrace_4356841
  have hstable : (prefixWord ++ tailWord_4356841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4356841).length < 2 ^ (prefixWord ++ tailWord_4356841).sum := by decide
  have hdescent : baseEnd_4356841 < baseStart_4356841 := by decide
  rcases family_descends (prefixWord ++ tailWord_4356841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4356844 : List Nat := [2, 2, 1, 1, 2, 2, 1, 2, 5, 2, 3]
def baseStart_4356844 : Nat := 118140960795 + 4356844 * 2 ^ 59
def prefixEnd_4356844 : Nat := 4983230072969 + 3 ^ 40 * 4356844 * 2
def baseEnd_4356844 : Nat := 2237155108657457061513245

theorem tailTrace_4356844 : CollatzResearch.WordTrace tailWord_4356844 prefixEnd_4356844 2237155108657457061513245 := by
  unfold tailWord_4356844
  simp only [CollatzResearch.WordTrace]
  refine ⟨79453577713952876280150793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105938103618603835040201057 79453577713952876280150793)
  ·
    refine ⟨59590183285464657210113095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79453577713952876280150793 59590183285464657210113095)
    ·
      refine ⟨89385274928196985815169643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59590183285464657210113095 89385274928196985815169643)
      ·
        refine ⟨134077912392295478722754465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89385274928196985815169643 134077912392295478722754465)
        ·
          refine ⟨100558434294221609042065849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 134077912392295478722754465 100558434294221609042065849)
          ·
            refine ⟨75418825720666206781549387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 100558434294221609042065849 75418825720666206781549387)
            ·
              refine ⟨113128238580999310172324081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75418825720666206781549387 113128238580999310172324081)
              ·
                refine ⟨84846178935749482629243061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 113128238580999310172324081 84846178935749482629243061)
                ·
                  refine ⟨7954329275226513996491537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 84846178935749482629243061 7954329275226513996491537)
                  ·
                    refine ⟨5965746956419885497368653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7954329275226513996491537 5965746956419885497368653)
                    ·
                      refine ⟨2237155108657457061513245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5965746956419885497368653 2237155108657457061513245)
                      ·
                        rfl

theorem cell23_4356844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 2, 3].length) (baseStart_4356844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4356844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4356844 prefixEnd_4356844 := by exact prefixLift 4356844
  have htrace : WordTrace (prefixWord ++ tailWord_4356844) baseStart_4356844 baseEnd_4356844 := by
    simpa [prefixWord, tailWord_4356844, baseEnd_4356844] using wordTrace_append hprefix tailTrace_4356844
  have hstable : (prefixWord ++ tailWord_4356844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4356844).length < 2 ^ (prefixWord ++ tailWord_4356844).sum := by decide
  have hdescent : baseEnd_4356844 < baseStart_4356844 := by decide
  rcases family_descends (prefixWord ++ tailWord_4356844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4356847 : List Nat := [1, 1, 2, 1, 5, 2, 11]
def baseStart_4356847 : Nat := 118140960795 + 4356847 * 2 ^ 59
def prefixEnd_4356847 : Nat := 4983230072969 + 3 ^ 40 * 4356847 * 2
def baseEnd_4356847 : Nat := 27619217890116303083651

theorem tailTrace_4356847 : CollatzResearch.WordTrace tailWord_4356847 prefixEnd_4356847 27619217890116303083651 := by
  unfold tailWord_4356847
  simp only [CollatzResearch.WordTrace]
  refine ⟨158907264846894884072660795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105938176564596589381773863 158907264846894884072660795)
  ·
    refine ⟨238360897270342326108991193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158907264846894884072660795 238360897270342326108991193)
    ·
      refine ⟨178770672952756744581743395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 238360897270342326108991193 178770672952756744581743395)
      ·
        refine ⟨268156009429135116872615093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 178770672952756744581743395 268156009429135116872615093)
        ·
          refine ⟨25139625883981417206807665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 268156009429135116872615093 25139625883981417206807665)
          ·
            refine ⟨18854719412986062905105749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25139625883981417206807665 18854719412986062905105749)
            ·
              refine ⟨27619217890116303083651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 18854719412986062905105749 27619217890116303083651)
              ·
                rfl

theorem cell23_4356847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 11].length) (baseStart_4356847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4356847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4356847 prefixEnd_4356847 := by exact prefixLift 4356847
  have htrace : WordTrace (prefixWord ++ tailWord_4356847) baseStart_4356847 baseEnd_4356847 := by
    simpa [prefixWord, tailWord_4356847, baseEnd_4356847] using wordTrace_append hprefix tailTrace_4356847
  have hstable : (prefixWord ++ tailWord_4356847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4356847).length < 2 ^ (prefixWord ++ tailWord_4356847).sum := by decide
  have hdescent : baseEnd_4356847 < baseStart_4356847 := by decide
  rcases family_descends (prefixWord ++ tailWord_4356847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4356854 : List Nat := [5, 1, 1, 1, 1, 2, 1, 1, 3, 1, 6]
def baseStart_4356854 : Nat := 118140960795 + 4356854 * 2 ^ 59
def prefixEnd_4356854 : Nat := 4983230072969 + 3 ^ 40 * 4356854 * 2
def baseEnd_4356854 : Nat := 2237160243464002022388199

theorem tailTrace_4356854 : CollatzResearch.WordTrace tailWord_4356854 prefixEnd_4356854 2237160243464002022388199 := by
  unfold tailWord_4356854
  simp only [CollatzResearch.WordTrace]
  refine ⟨9931720009866845266760351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 105938346771913016178777077 9931720009866845266760351)
  ·
    refine ⟨14897580014800267900140527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9931720009866845266760351 14897580014800267900140527)
    ·
      refine ⟨22346370022200401850210791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14897580014800267900140527 22346370022200401850210791)
      ·
        refine ⟨33519555033300602775316187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22346370022200401850210791 33519555033300602775316187)
        ·
          refine ⟨50279332549950904162974281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33519555033300602775316187 50279332549950904162974281)
          ·
            refine ⟨37709499412463178122230711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50279332549950904162974281 37709499412463178122230711)
            ·
              refine ⟨56564249118694767183346067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37709499412463178122230711 56564249118694767183346067)
              ·
                refine ⟨84846373678042150775019101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56564249118694767183346067 84846373678042150775019101)
                ·
                  refine ⟨31817390129265806540632163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 84846373678042150775019101 31817390129265806540632163)
                  ·
                    refine ⟨47726085193898709810948245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 31817390129265806540632163 47726085193898709810948245)
                    ·
                      refine ⟨2237160243464002022388199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 47726085193898709810948245 2237160243464002022388199)
                      ·
                        rfl

theorem cell23_4356854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 1, 3, 1, 6].length) (baseStart_4356854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4356854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4356854 prefixEnd_4356854 := by exact prefixLift 4356854
  have htrace : WordTrace (prefixWord ++ tailWord_4356854) baseStart_4356854 baseEnd_4356854 := by
    simpa [prefixWord, tailWord_4356854, baseEnd_4356854] using wordTrace_append hprefix tailTrace_4356854
  have hstable : (prefixWord ++ tailWord_4356854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4356854).length < 2 ^ (prefixWord ++ tailWord_4356854).sum := by decide
  have hdescent : baseEnd_4356854 < baseStart_4356854 := by decide
  rcases family_descends (prefixWord ++ tailWord_4356854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4356858 : List Nat := [3, 1, 1, 1, 1, 3, 5, 1, 3, 2, 2]
def baseStart_4356858 : Nat := 118140960795 + 4356858 * 2 ^ 59
def prefixEnd_4356858 : Nat := 4983230072969 + 3 ^ 40 * 4356858 * 2
def baseEnd_4356858 : Nat := 2237162297386620006738181

theorem tailTrace_4356858 : CollatzResearch.WordTrace tailWord_4356858 prefixEnd_4356858 2237162297386620006738181 := by
  unfold tailWord_4356858
  simp only [CollatzResearch.WordTrace]
  refine ⟨39726916512463758237827807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105938444033236688634207485 39726916512463758237827807)
  ·
    refine ⟨59590374768695637356741711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39726916512463758237827807 59590374768695637356741711)
    ·
      refine ⟨89385562153043456035112567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59590374768695637356741711 89385562153043456035112567)
      ·
        refine ⟨134078343229565184052668851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89385562153043456035112567 134078343229565184052668851)
        ·
          refine ⟨201117514844347776079003277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 134078343229565184052668851 201117514844347776079003277)
          ·
            refine ⟨75419068066630416029626229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 201117514844347776079003277 75419068066630416029626229)
            ·
              refine ⟨7070537631246601502777459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 75419068066630416029626229 7070537631246601502777459)
              ·
                refine ⟨10605806446869902254166189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7070537631246601502777459 10605806446869902254166189)
                ·
                  refine ⟨3977177417576213345312321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10605806446869902254166189 3977177417576213345312321)
                  ·
                    refine ⟨2982883063182160008984241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3977177417576213345312321 2982883063182160008984241)
                    ·
                      refine ⟨2237162297386620006738181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2982883063182160008984241 2237162297386620006738181)
                      ·
                        rfl

theorem cell23_4356858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 5, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 5, 1, 3, 2, 2].length) (baseStart_4356858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4356858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4356858 prefixEnd_4356858 := by exact prefixLift 4356858
  have htrace : WordTrace (prefixWord ++ tailWord_4356858) baseStart_4356858 baseEnd_4356858 := by
    simpa [prefixWord, tailWord_4356858, baseEnd_4356858] using wordTrace_append hprefix tailTrace_4356858
  have hstable : (prefixWord ++ tailWord_4356858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4356858).length < 2 ^ (prefixWord ++ tailWord_4356858).sum := by decide
  have hdescent : baseEnd_4356858 < baseStart_4356858 := by decide
  rcases family_descends (prefixWord ++ tailWord_4356858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4356867 : List Nat := [1, 1, 1, 3, 2, 2, 1, 1, 1, 4, 6]
def baseStart_4356867 : Nat := 118140960795 + 4356867 * 2 ^ 59
def prefixEnd_4356867 : Nat := 4983230072969 + 3 ^ 40 * 4356867 * 2
def baseEnd_4356867 : Nat := 2237166918712510471525639

theorem tailTrace_4356867 : CollatzResearch.WordTrace tailWord_4356867 prefixEnd_4356867 2237166918712510471525639 := by
  unfold tailWord_4356867
  simp only [CollatzResearch.WordTrace]
  refine ⟨158907994306822427488388855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105938662871214951658925903 158907994306822427488388855)
  ·
    refine ⟨238361991460233641232583283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158907994306822427488388855 238361991460233641232583283)
    ·
      refine ⟨357542987190350461848874925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 238361991460233641232583283 357542987190350461848874925)
      ·
        refine ⟨134078620196381423193328097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 357542987190350461848874925 134078620196381423193328097)
        ·
          refine ⟨100558965147286067394996073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 134078620196381423193328097 100558965147286067394996073)
          ·
            refine ⟨75419223860464550546247055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 100558965147286067394996073 75419223860464550546247055)
            ·
              refine ⟨113128835790696825819370583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75419223860464550546247055 113128835790696825819370583)
              ·
                refine ⟨169693253686045238729055875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 113128835790696825819370583 169693253686045238729055875)
                ·
                  refine ⟨254539880529067858093583813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 169693253686045238729055875 254539880529067858093583813)
                  ·
                    refine ⟨47726227599200223392546965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 254539880529067858093583813 47726227599200223392546965)
                    ·
                      refine ⟨2237166918712510471525639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 47726227599200223392546965 2237166918712510471525639)
                      ·
                        rfl

theorem cell23_4356867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 1, 1, 4, 6].length) (baseStart_4356867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4356867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4356867 prefixEnd_4356867 := by exact prefixLift 4356867
  have htrace : WordTrace (prefixWord ++ tailWord_4356867) baseStart_4356867 baseEnd_4356867 := by
    simpa [prefixWord, tailWord_4356867, baseEnd_4356867] using wordTrace_append hprefix tailTrace_4356867
  have hstable : (prefixWord ++ tailWord_4356867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4356867).length < 2 ^ (prefixWord ++ tailWord_4356867).sum := by decide
  have hdescent : baseEnd_4356867 < baseStart_4356867 := by decide
  rcases family_descends (prefixWord ++ tailWord_4356867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4356908 : List Nat := [2, 2, 1, 1, 1, 4, 4, 2, 2, 1, 3]
def baseStart_4356908 : Nat := 118140960795 + 4356908 * 2 ^ 59
def prefixEnd_4356908 : Nat := 4983230072969 + 3 ^ 40 * 4356908 * 2
def baseEnd_4356908 : Nat := 2237187971419344811112951

theorem tailTrace_4356908 : CollatzResearch.WordTrace tailWord_4356908 prefixEnd_4356908 2237187971419344811112951 := by
  unfold tailWord_4356908
  simp only [CollatzResearch.WordTrace]
  refine ⟨79454744849836945745315689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105939659799782594327087585 79454744849836945745315689)
  ·
    refine ⟨59591058637377709308986767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79454744849836945745315689 59591058637377709308986767)
    ·
      refine ⟨89386587956066563963480151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59591058637377709308986767 89386587956066563963480151)
      ·
        refine ⟨134079881934099845945220227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89386587956066563963480151 134079881934099845945220227)
        ·
          refine ⟨201119822901149768917830341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 134079881934099845945220227 201119822901149768917830341)
          ·
            refine ⟨37709966793965581672093189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 201119822901149768917830341 37709966793965581672093189)
            ·
              refine ⟨7070618773868546563517473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37709966793965581672093189 7070618773868546563517473)
              ·
                refine ⟨5302964080401409922638105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7070618773868546563517473 5302964080401409922638105)
                ·
                  refine ⟨3977223060301057441978579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5302964080401409922638105 3977223060301057441978579)
                  ·
                    refine ⟨5965834590451586162967869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3977223060301057441978579 5965834590451586162967869)
                    ·
                      refine ⟨2237187971419344811112951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5965834590451586162967869 2237187971419344811112951)
                      ·
                        rfl

theorem cell23_4356908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 1, 3].length) (baseStart_4356908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4356908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4356908 prefixEnd_4356908 := by exact prefixLift 4356908
  have htrace : WordTrace (prefixWord ++ tailWord_4356908) baseStart_4356908 baseEnd_4356908 := by
    simpa [prefixWord, tailWord_4356908, baseEnd_4356908] using wordTrace_append hprefix tailTrace_4356908
  have hstable : (prefixWord ++ tailWord_4356908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4356908).length < 2 ^ (prefixWord ++ tailWord_4356908).sum := by decide
  have hdescent : baseEnd_4356908 < baseStart_4356908 := by decide
  rcases family_descends (prefixWord ++ tailWord_4356908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4356914 : List Nat := [3, 2, 1, 1, 3, 1, 1, 1, 1, 5, 4]
def baseStart_4356914 : Nat := 118140960795 + 4356914 * 2 ^ 59
def prefixEnd_4356914 : Nat := 4983230072969 + 3 ^ 40 * 4356914 * 2
def baseEnd_4356914 : Nat := 2237191052303271787637923

theorem tailTrace_4356914 : CollatzResearch.WordTrace tailWord_4356914 prefixEnd_4356914 2237191052303271787637923 := by
  unfold tailWord_4356914
  simp only [CollatzResearch.WordTrace]
  refine ⟨39727427134413038628837449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105939805691768103010233197 39727427134413038628837449)
  ·
    refine ⟨29795570350809778971628087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39727427134413038628837449 29795570350809778971628087)
    ·
      refine ⟨44693355526214668457442131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29795570350809778971628087 44693355526214668457442131)
      ·
        refine ⟨67040033289322002686163197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44693355526214668457442131 67040033289322002686163197)
        ·
          refine ⟨25140012483495751007311199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 67040033289322002686163197 25140012483495751007311199)
          ·
            refine ⟨37710018725243626510966799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25140012483495751007311199 37710018725243626510966799)
            ·
              refine ⟨56565028087865439766450199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37710018725243626510966799 56565028087865439766450199)
              ·
                refine ⟨84847542131798159649675299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56565028087865439766450199 84847542131798159649675299)
                ·
                  refine ⟨127271313197697239474512949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 84847542131798159649675299 127271313197697239474512949)
                  ·
                    refine ⟨11931685612284116200735589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 127271313197697239474512949 11931685612284116200735589)
                    ·
                      refine ⟨2237191052303271787637923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11931685612284116200735589 2237191052303271787637923)
                      ·
                        rfl

theorem cell23_4356914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 1, 1, 5, 4].length) (baseStart_4356914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4356914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4356914 prefixEnd_4356914 := by exact prefixLift 4356914
  have htrace : WordTrace (prefixWord ++ tailWord_4356914) baseStart_4356914 baseEnd_4356914 := by
    simpa [prefixWord, tailWord_4356914, baseEnd_4356914] using wordTrace_append hprefix tailTrace_4356914
  have hstable : (prefixWord ++ tailWord_4356914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4356914).length < 2 ^ (prefixWord ++ tailWord_4356914).sum := by decide
  have hdescent : baseEnd_4356914 < baseStart_4356914 := by decide
  rcases family_descends (prefixWord ++ tailWord_4356914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4356965 : List Nat := [1, 3, 1, 3, 1, 1, 5, 2, 2, 2, 2]
def baseStart_4356965 : Nat := 118140960795 + 4356965 * 2 ^ 59
def prefixEnd_4356965 : Nat := 4983230072969 + 3 ^ 40 * 4356965 * 2
def baseEnd_4356965 : Nat := 2237217239816651088100189

theorem tailTrace_4356965 : CollatzResearch.WordTrace tailWord_4356965 prefixEnd_4356965 2237217239816651088100189 := by
  unfold tailWord_4356965
  simp only [CollatzResearch.WordTrace]
  refine ⟨158911568660467390225456349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105941045773644926816970899 158911568660467390225456349)
  ·
    refine ⟨59591838247675271334546131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 158911568660467390225456349 59591838247675271334546131)
    ·
      refine ⟨89387757371512907001819197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59591838247675271334546131 89387757371512907001819197)
      ·
        refine ⟨33520409014317340125682199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 89387757371512907001819197 33520409014317340125682199)
        ·
          refine ⟨50280613521476010188523299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33520409014317340125682199 50280613521476010188523299)
          ·
            refine ⟨75420920282214015282784949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50280613521476010188523299 75420920282214015282784949)
            ·
              refine ⟨7070711276457563932761089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 75420920282214015282784949 7070711276457563932761089)
              ·
                refine ⟨5303033457343172949570817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7070711276457563932761089 5303033457343172949570817)
                ·
                  refine ⟨3977275093007379712178113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5303033457343172949570817 3977275093007379712178113)
                  ·
                    refine ⟨2982956319755534784133585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3977275093007379712178113 2982956319755534784133585)
                    ·
                      refine ⟨2237217239816651088100189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2982956319755534784133585 2237217239816651088100189)
                      ·
                        rfl

theorem cell23_4356965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 5, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 5, 2, 2, 2, 2].length) (baseStart_4356965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4356965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4356965 prefixEnd_4356965 := by exact prefixLift 4356965
  have htrace : WordTrace (prefixWord ++ tailWord_4356965) baseStart_4356965 baseEnd_4356965 := by
    simpa [prefixWord, tailWord_4356965, baseEnd_4356965] using wordTrace_append hprefix tailTrace_4356965
  have hstable : (prefixWord ++ tailWord_4356965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4356965).length < 2 ^ (prefixWord ++ tailWord_4356965).sum := by decide
  have hdescent : baseEnd_4356965 < baseStart_4356965 := by decide
  rcases family_descends (prefixWord ++ tailWord_4356965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4356971 : List Nat := [1, 1, 1, 1, 2, 2, 6, 4, 5]
def baseStart_4356971 : Nat := 118140960795 + 4356971 * 2 ^ 59
def prefixEnd_4356971 : Nat := 4983230072969 + 3 ^ 40 * 4356971 * 2
def baseEnd_4356971 : Nat := 248580035633397562736129

theorem tailTrace_4356971 : CollatzResearch.WordTrace tailWord_4356971 prefixEnd_4356971 248580035633397562736129 := by
  unfold tailWord_4356971
  simp only [CollatzResearch.WordTrace]
  refine ⟨158911787498445653250174767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105941191665630435500116511 158911787498445653250174767)
  ·
    refine ⟨238367681247668479875262151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158911787498445653250174767 238367681247668479875262151)
    ·
      refine ⟨357551521871502719812893227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 238367681247668479875262151 357551521871502719812893227)
      ·
        refine ⟨536327282807254079719339841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 357551521871502719812893227 536327282807254079719339841)
        ·
          refine ⟨402245462105440559789504881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 536327282807254079719339841 402245462105440559789504881)
          ·
            refine ⟨301684096579080419842128661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 402245462105440559789504881 301684096579080419842128661)
            ·
              refine ⟨14141442027144394680099781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 301684096579080419842128661 14141442027144394680099781)
              ·
                refine ⟨2651520380089574002518709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14141442027144394680099781 2651520380089574002518709)
                ·
                  refine ⟨248580035633397562736129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2651520380089574002518709 248580035633397562736129)
                  ·
                    rfl

theorem cell23_4356971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 6, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 6, 4, 5].length) (baseStart_4356971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4356971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4356971 prefixEnd_4356971 := by exact prefixLift 4356971
  have htrace : WordTrace (prefixWord ++ tailWord_4356971) baseStart_4356971 baseEnd_4356971 := by
    simpa [prefixWord, tailWord_4356971, baseEnd_4356971] using wordTrace_append hprefix tailTrace_4356971
  have hstable : (prefixWord ++ tailWord_4356971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4356971).length < 2 ^ (prefixWord ++ tailWord_4356971).sum := by decide
  have hdescent : baseEnd_4356971 < baseStart_4356971 := by decide
  rcases family_descends (prefixWord ++ tailWord_4356971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4356982 : List Nat := [5, 1, 1, 3, 1, 3, 1, 1, 1, 4, 2]
def baseStart_4356982 : Nat := 118140960795 + 4356982 * 2 ^ 59
def prefixEnd_4356982 : Nat := 4983230072969 + 3 ^ 40 * 4356982 * 2
def baseEnd_4356982 : Nat := 2237225968987777521587611

theorem tailTrace_4356982 : CollatzResearch.WordTrace tailWord_4356982 prefixEnd_4356982 2237225968987777521587611 := by
  unfold tailWord_4356982
  simp only [CollatzResearch.WordTrace]
  refine ⟨9932011793837862633051575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 105941459134270534752550133 9932011793837862633051575)
  ·
    refine ⟨14898017690756793949577363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9932011793837862633051575 14898017690756793949577363)
    ·
      refine ⟨22347026536135190924366045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14898017690756793949577363 22347026536135190924366045)
      ·
        refine ⟨8380134951050696596637267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22347026536135190924366045 8380134951050696596637267)
        ·
          refine ⟨12570202426576044894955901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8380134951050696596637267 12570202426576044894955901)
          ·
            refine ⟨4713825909966016835608463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12570202426576044894955901 4713825909966016835608463)
            ·
              refine ⟨7070738864949025253412695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4713825909966016835608463 7070738864949025253412695)
              ·
                refine ⟨10606108297423537880119043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7070738864949025253412695 10606108297423537880119043)
                ·
                  refine ⟨15909162446135306820178565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10606108297423537880119043 15909162446135306820178565)
                  ·
                    refine ⟨2982967958650370028783481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15909162446135306820178565 2982967958650370028783481)
                    ·
                      refine ⟨2237225968987777521587611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2982967958650370028783481 2237225968987777521587611)
                      ·
                        rfl

theorem cell23_4356982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 3, 1, 1, 1, 4, 2].length) (baseStart_4356982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4356982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4356982 prefixEnd_4356982 := by exact prefixLift 4356982
  have htrace : WordTrace (prefixWord ++ tailWord_4356982) baseStart_4356982 baseEnd_4356982 := by
    simpa [prefixWord, tailWord_4356982, baseEnd_4356982] using wordTrace_append hprefix tailTrace_4356982
  have hstable : (prefixWord ++ tailWord_4356982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4356982).length < 2 ^ (prefixWord ++ tailWord_4356982).sum := by decide
  have hdescent : baseEnd_4356982 < baseStart_4356982 := by decide
  rcases family_descends (prefixWord ++ tailWord_4356982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4356984 : List Nat := [2, 1, 2, 1, 1, 1, 1, 3, 6, 5]
def baseStart_4356984 : Nat := 118140960795 + 4356984 * 2 ^ 59
def prefixEnd_4356984 : Nat := 4983230072969 + 3 ^ 40 * 4356984 * 2
def baseEnd_4356984 : Nat := 745742331983028837920867

theorem tailTrace_4356984 : CollatzResearch.WordTrace tailWord_4356984 prefixEnd_4356984 745742331983028837920867 := by
  unfold tailWord_4356984
  simp only [CollatzResearch.WordTrace]
  refine ⟨79456130823699278235199003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105941507764932370980265337 79456130823699278235199003)
  ·
    refine ⟨119184196235548917352798505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79456130823699278235199003 119184196235548917352798505)
    ·
      refine ⟨89388147176661688014598879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119184196235548917352798505 89388147176661688014598879)
      ·
        refine ⟨134082220764992532021898319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89388147176661688014598879 134082220764992532021898319)
        ·
          refine ⟨201123331147488798032847479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 134082220764992532021898319 201123331147488798032847479)
          ·
            refine ⟨301684996721233197049271219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 201123331147488798032847479 301684996721233197049271219)
            ·
              refine ⟨452527495081849795573906829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 301684996721233197049271219 452527495081849795573906829)
              ·
                refine ⟨169697810655693673340215061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 452527495081849795573906829 169697810655693673340215061)
                ·
                  refine ⟨7954584874485640937822581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 169697810655693673340215061 7954584874485640937822581)
                  ·
                    refine ⟨745742331983028837920867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7954584874485640937822581 745742331983028837920867)
                    ·
                      rfl

theorem cell23_4356984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 3, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 3, 6, 5].length) (baseStart_4356984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4356984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4356984 prefixEnd_4356984 := by exact prefixLift 4356984
  have htrace : WordTrace (prefixWord ++ tailWord_4356984) baseStart_4356984 baseEnd_4356984 := by
    simpa [prefixWord, tailWord_4356984, baseEnd_4356984] using wordTrace_append hprefix tailTrace_4356984
  have hstable : (prefixWord ++ tailWord_4356984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4356984).length < 2 ^ (prefixWord ++ tailWord_4356984).sum := by decide
  have hdescent : baseEnd_4356984 < baseStart_4356984 := by decide
  rcases family_descends (prefixWord ++ tailWord_4356984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4356991 : List Nat := [1, 1, 2, 2, 1, 1, 4, 2, 2, 5, 2]
def baseStart_4356991 : Nat := 118140960795 + 4356991 * 2 ^ 59
def prefixEnd_4356991 : Nat := 4983230072969 + 3 ^ 40 * 4356991 * 2
def baseEnd_4356991 : Nat := 2237230590313667986375069

theorem tailTrace_4356991 : CollatzResearch.WordTrace tailWord_4356991 prefixEnd_4356991 2237230590313667986375069 := by
  unfold tailWord_4356991
  simp only [CollatzResearch.WordTrace]
  refine ⟨158912516958373196665902827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105941677972248797777268551 158912516958373196665902827)
  ·
    refine ⟨238368775437559794998854241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158912516958373196665902827 238368775437559794998854241)
    ·
      refine ⟨178776581578169846249140681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 238368775437559794998854241 178776581578169846249140681)
      ·
        refine ⟨134082436183627384686855511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 178776581578169846249140681 134082436183627384686855511)
        ·
          refine ⟨201123654275441077030283267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 134082436183627384686855511 201123654275441077030283267)
          ·
            refine ⟨301685481413161615545424901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 201123654275441077030283267 301685481413161615545424901)
            ·
              refine ⟨56566027764967802914767169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 301685481413161615545424901 56566027764967802914767169)
              ·
                refine ⟨42424520823725852186075377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56566027764967802914767169 42424520823725852186075377)
                ·
                  refine ⟨31818390617794389139556533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42424520823725852186075377 31818390617794389139556533)
                  ·
                    refine ⟨2982974120418223981833425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 31818390617794389139556533 2982974120418223981833425)
                    ·
                      refine ⟨2237230590313667986375069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2982974120418223981833425 2237230590313667986375069)
                      ·
                        rfl

theorem cell23_4356991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 2, 2, 5, 2].length) (baseStart_4356991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4356991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4356991 prefixEnd_4356991 := by exact prefixLift 4356991
  have htrace : WordTrace (prefixWord ++ tailWord_4356991) baseStart_4356991 baseEnd_4356991 := by
    simpa [prefixWord, tailWord_4356991, baseEnd_4356991] using wordTrace_append hprefix tailTrace_4356991
  have hstable : (prefixWord ++ tailWord_4356991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4356991).length < 2 ^ (prefixWord ++ tailWord_4356991).sum := by decide
  have hdescent : baseEnd_4356991 < baseStart_4356991 := by decide
  rcases family_descends (prefixWord ++ tailWord_4356991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4357018 : List Nat := [3, 1, 1, 4, 3, 1, 1, 2, 2, 5]
def baseStart_4357018 : Nat := 118140960795 + 4357018 * 2 ^ 59
def prefixEnd_4357018 : Nat := 4983230072969 + 3 ^ 40 * 4357018 * 2
def baseEnd_4357018 : Nat := 745748151430446460245815

theorem tailTrace_4357018 : CollatzResearch.WordTrace tailWord_4357018 prefixEnd_4357018 745748151430446460245815 := by
  unfold tailWord_4357018
  simp only [CollatzResearch.WordTrace]
  refine ⟨39728375432318845069283927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105942334486183586851423805 39728375432318845069283927)
  ·
    refine ⟨59592563148478267603925891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39728375432318845069283927 59592563148478267603925891)
    ·
      refine ⟨89388844722717401405888837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59592563148478267603925891 89388844722717401405888837)
      ·
        refine ⟨16760408385509512763604157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 89388844722717401405888837 16760408385509512763604157)
        ·
          refine ⟨6285153144566067286351559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16760408385509512763604157 6285153144566067286351559)
          ·
            refine ⟨9427729716849100929527339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6285153144566067286351559 9427729716849100929527339)
            ·
              refine ⟨14141594575273651394291009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9427729716849100929527339 14141594575273651394291009)
              ·
                refine ⟨10606195931455238545718257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14141594575273651394291009 10606195931455238545718257)
                ·
                  refine ⟨7954646948591428909288693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10606195931455238545718257 7954646948591428909288693)
                  ·
                    refine ⟨745748151430446460245815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7954646948591428909288693 745748151430446460245815)
                    ·
                      rfl

theorem cell23_4357018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 1, 2, 2, 5].length) (baseStart_4357018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4357018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4357018 prefixEnd_4357018 := by exact prefixLift 4357018
  have htrace : WordTrace (prefixWord ++ tailWord_4357018) baseStart_4357018 baseEnd_4357018 := by
    simpa [prefixWord, tailWord_4357018, baseEnd_4357018] using wordTrace_append hprefix tailTrace_4357018
  have hstable : (prefixWord ++ tailWord_4357018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4357018).length < 2 ^ (prefixWord ++ tailWord_4357018).sum := by decide
  have hdescent : baseEnd_4357018 < baseStart_4357018 := by decide
  rcases family_descends (prefixWord ++ tailWord_4357018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4357082 : List Nat := [3, 1, 1, 2, 4, 1, 4, 2, 1, 4]
def baseStart_4357082 : Nat := 118140960795 + 4357082 * 2 ^ 59
def prefixEnd_4357082 : Nat := 4983230072969 + 3 ^ 40 * 4357082 * 2
def baseEnd_4357082 : Nat := 745759105684409043445717

theorem tailTrace_4357082 : CollatzResearch.WordTrace tailWord_4357082 prefixEnd_4357082 745759105684409043445717 := by
  unfold tailWord_4357082
  simp only [CollatzResearch.WordTrace]
  refine ⟨39728959000260879801866375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105943890667362346138310333 39728959000260879801866375)
  ·
    refine ⟨59593438500391319702799563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39728959000260879801866375 59593438500391319702799563)
    ·
      refine ⟨89390157750586979554199345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59593438500391319702799563 89390157750586979554199345)
      ·
        refine ⟨67042618312940234665649509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89390157750586979554199345 67042618312940234665649509)
        ·
          refine ⟨12570490933676293999809283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 67042618312940234665649509 12570490933676293999809283)
          ·
            refine ⟨18855736400514440999713925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12570490933676293999809283 18855736400514440999713925)
            ·
              refine ⟨3535450575096457687446361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18855736400514440999713925 3535450575096457687446361)
              ·
                refine ⟨2651587931322343265584771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3535450575096457687446361 2651587931322343265584771)
                ·
                  refine ⟨3977381896983514898377157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2651587931322343265584771 3977381896983514898377157)
                  ·
                    refine ⟨745759105684409043445717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3977381896983514898377157 745759105684409043445717)
                    ·
                      rfl

theorem cell23_4357082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 4, 2, 1, 4].length) (baseStart_4357082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4357082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4357082 prefixEnd_4357082 := by exact prefixLift 4357082
  have htrace : WordTrace (prefixWord ++ tailWord_4357082) baseStart_4357082 baseEnd_4357082 := by
    simpa [prefixWord, tailWord_4357082, baseEnd_4357082] using wordTrace_append hprefix tailTrace_4357082
  have hstable : (prefixWord ++ tailWord_4357082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4357082).length < 2 ^ (prefixWord ++ tailWord_4357082).sum := by decide
  have hdescent : baseEnd_4357082 < baseStart_4357082 := by decide
  rcases family_descends (prefixWord ++ tailWord_4357082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4357091 : List Nat := [1, 1, 1, 6, 1, 1, 1, 1, 5, 5]
def baseStart_4357091 : Nat := 118140960795 + 4357091 * 2 ^ 59
def prefixEnd_4357091 : Nat := 4983230072969 + 3 ^ 40 * 4357091 * 2
def baseEnd_4357091 : Nat := 745760646126372531708203

theorem tailTrace_4357091 : CollatzResearch.WordTrace tailWord_4357091 prefixEnd_4357091 745760646126372531708203 := by
  unfold tailWord_4357091
  simp only [CollatzResearch.WordTrace]
  refine ⟨158916164258010913744543127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105944109505340609163028751 158916164258010913744543127)
  ·
    refine ⟨238374246387016370616814691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158916164258010913744543127 238374246387016370616814691)
    ·
      refine ⟨357561369580524555925222037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 238374246387016370616814691 357561369580524555925222037)
      ·
        refine ⟨16760689199087088558994783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 357561369580524555925222037 16760689199087088558994783)
        ·
          refine ⟨25141033798630632838492175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16760689199087088558994783 25141033798630632838492175)
          ·
            refine ⟨37711550697945949257738263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25141033798630632838492175 37711550697945949257738263)
            ·
              refine ⟨56567326046918923886607395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37711550697945949257738263 56567326046918923886607395)
              ·
                refine ⟨84850989070378385829911093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56567326046918923886607395 84850989070378385829911093)
                ·
                  refine ⟨7954780225347973671554165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 84850989070378385829911093 7954780225347973671554165)
                  ·
                    refine ⟨745760646126372531708203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7954780225347973671554165 745760646126372531708203)
                    ·
                      rfl

theorem cell23_4357091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 1, 5, 5].length) (baseStart_4357091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4357091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4357091 prefixEnd_4357091 := by exact prefixLift 4357091
  have htrace : WordTrace (prefixWord ++ tailWord_4357091) baseStart_4357091 baseEnd_4357091 := by
    simpa [prefixWord, tailWord_4357091, baseEnd_4357091] using wordTrace_append hprefix tailTrace_4357091
  have hstable : (prefixWord ++ tailWord_4357091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4357091).length < 2 ^ (prefixWord ++ tailWord_4357091).sum := by decide
  have hdescent : baseEnd_4357091 < baseStart_4357091 := by decide
  rcases family_descends (prefixWord ++ tailWord_4357091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4357105 : List Nat := [1, 2, 2, 2, 4, 2, 1, 2, 3, 1, 3]
def baseStart_4357105 : Nat := 118140960795 + 4357105 * 2 ^ 59
def prefixEnd_4357105 : Nat := 4983230072969 + 3 ^ 40 * 4357105 * 2
def baseEnd_4357105 : Nat := 2237289127108280540349545

theorem tailTrace_4357105 : CollatzResearch.WordTrace tailWord_4357105 prefixEnd_4357105 2237289127108280540349545 := by
  unfold tailWord_4357105
  simp only [CollatzResearch.WordTrace]
  refine ⟨158916674879960194135552769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105944449919973462757035179 158916674879960194135552769)
  ·
    refine ⟨119187506159970145601664577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 158916674879960194135552769 119187506159970145601664577)
    ·
      refine ⟨89390629619977609201248433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119187506159970145601664577 89390629619977609201248433)
      ·
        refine ⟨67042972214983206900936325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89390629619977609201248433 67042972214983206900936325)
        ·
          refine ⟨12570557290309351293925561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 67042972214983206900936325 12570557290309351293925561)
          ·
            refine ⟨9427917967732013470444171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12570557290309351293925561 9427917967732013470444171)
            ·
              refine ⟨14141876951598020205666257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9427917967732013470444171 14141876951598020205666257)
              ·
                refine ⟨10606407713698515154249693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14141876951598020205666257 10606407713698515154249693)
                ·
                  refine ⟨3977402892636943182843635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10606407713698515154249693 3977402892636943182843635)
                  ·
                    refine ⟨5966104338955414774265453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3977402892636943182843635 5966104338955414774265453)
                    ·
                      refine ⟨2237289127108280540349545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5966104338955414774265453 2237289127108280540349545)
                      ·
                        rfl

theorem cell23_4357105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 1, 2, 3, 1, 3].length) (baseStart_4357105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4357105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4357105 prefixEnd_4357105 := by exact prefixLift 4357105
  have htrace : WordTrace (prefixWord ++ tailWord_4357105) baseStart_4357105 baseEnd_4357105 := by
    simpa [prefixWord, tailWord_4357105, baseEnd_4357105] using wordTrace_append hprefix tailTrace_4357105
  have hstable : (prefixWord ++ tailWord_4357105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4357105).length < 2 ^ (prefixWord ++ tailWord_4357105).sum := by decide
  have hdescent : baseEnd_4357105 < baseStart_4357105 := by decide
  rcases family_descends (prefixWord ++ tailWord_4357105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4357109 : List Nat := [1, 3, 5, 2, 1, 2, 1, 1, 2, 2, 3]
def baseStart_4357109 : Nat := 118140960795 + 4357109 * 2 ^ 59
def prefixEnd_4357109 : Nat := 4983230072969 + 3 ^ 40 * 4357109 * 2
def baseEnd_4357109 : Nat := 2237291181030898524699527

theorem tailTrace_4357109 : CollatzResearch.WordTrace tailWord_4357109 prefixEnd_4357109 2237291181030898524699527 := by
  unfold tailWord_4357109
  simp only [CollatzResearch.WordTrace]
  refine ⟨158916820771945702818698381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105944547181297135212465587 158916820771945702818698381)
  ·
    refine ⟨59593807789479638557011893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 158916820771945702818698381 59593807789479638557011893)
    ·
      refine ⟨5586919480263716114719865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 59593807789479638557011893 5586919480263716114719865)
      ·
        refine ⟨4190189610197787086039899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5586919480263716114719865 4190189610197787086039899)
        ·
          refine ⟨6285284415296680629059849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4190189610197787086039899 6285284415296680629059849)
          ·
            refine ⟨4713963311472510471794887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6285284415296680629059849 4713963311472510471794887)
            ·
              refine ⟨7070944967208765707692331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4713963311472510471794887 7070944967208765707692331)
              ·
                refine ⟨10606417450813148561538497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7070944967208765707692331 10606417450813148561538497)
                ·
                  refine ⟨7954813088109861421153873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10606417450813148561538497 7954813088109861421153873)
                  ·
                    refine ⟨5966109816082396065865405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7954813088109861421153873 5966109816082396065865405)
                    ·
                      refine ⟨2237291181030898524699527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5966109816082396065865405 2237291181030898524699527)
                      ·
                        rfl

theorem cell23_4357109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 2, 1, 1, 2, 2, 3].length) (baseStart_4357109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4357109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4357109 prefixEnd_4357109 := by exact prefixLift 4357109
  have htrace : WordTrace (prefixWord ++ tailWord_4357109) baseStart_4357109 baseEnd_4357109 := by
    simpa [prefixWord, tailWord_4357109, baseEnd_4357109] using wordTrace_append hprefix tailTrace_4357109
  have hstable : (prefixWord ++ tailWord_4357109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4357109).length < 2 ^ (prefixWord ++ tailWord_4357109).sum := by decide
  have hdescent : baseEnd_4357109 < baseStart_4357109 := by decide
  rcases family_descends (prefixWord ++ tailWord_4357109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4357145 : List Nat := [1, 2, 1, 2, 1, 1, 5, 3, 3, 2, 2]
def baseStart_4357145 : Nat := 118140960795 + 4357145 * 2 ^ 59
def prefixEnd_4357145 : Nat := 4983230072969 + 3 ^ 40 * 4357145 * 2
def baseEnd_4357145 : Nat := 2237309666334460383849361

theorem tailTrace_4357145 : CollatzResearch.WordTrace tailWord_4357145 prefixEnd_4357145 2237309666334460383849361 := by
  unfold tailWord_4357145
  simp only [CollatzResearch.WordTrace]
  refine ⟨158918133799815280967008889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105945422533210187311339259 158918133799815280967008889)
  ·
    refine ⟨119188600349861460725256667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 158918133799815280967008889 119188600349861460725256667)
    ·
      refine ⟨178782900524792191087885001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119188600349861460725256667 178782900524792191087885001)
      ·
        refine ⟨134087175393594143315913751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 178782900524792191087885001 134087175393594143315913751)
        ·
          refine ⟨201130763090391214973870627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 134087175393594143315913751 201130763090391214973870627)
          ·
            refine ⟨301696144635586822460805941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 201130763090391214973870627 301696144635586822460805941)
            ·
              refine ⟨28284013559586264605700557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 301696144635586822460805941 28284013559586264605700557)
              ·
                refine ⟨10606505084844849227137709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28284013559586264605700557 10606505084844849227137709)
                ·
                  refine ⟨3977439406816818460176641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10606505084844849227137709 3977439406816818460176641)
                  ·
                    refine ⟨2983079555112613845132481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3977439406816818460176641 2983079555112613845132481)
                    ·
                      refine ⟨2237309666334460383849361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2983079555112613845132481 2237309666334460383849361)
                      ·
                        rfl

theorem cell23_4357145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 3, 3, 2, 2].length) (baseStart_4357145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4357145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4357145 prefixEnd_4357145 := by exact prefixLift 4357145
  have htrace : WordTrace (prefixWord ++ tailWord_4357145) baseStart_4357145 baseEnd_4357145 := by
    simpa [prefixWord, tailWord_4357145, baseEnd_4357145] using wordTrace_append hprefix tailTrace_4357145
  have hstable : (prefixWord ++ tailWord_4357145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4357145).length < 2 ^ (prefixWord ++ tailWord_4357145).sum := by decide
  have hdescent : baseEnd_4357145 < baseStart_4357145 := by decide
  rcases family_descends (prefixWord ++ tailWord_4357145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4357162 : List Nat := [3, 1, 4, 1, 3, 1, 2, 2, 1, 1, 4]
def baseStart_4357162 : Nat := 118140960795 + 4357162 * 2 ^ 59
def prefixEnd_4357162 : Nat := 4983230072969 + 3 ^ 40 * 4357162 * 2
def baseEnd_4357162 : Nat := 2237318395505586817336783

theorem tailTrace_4357162 : CollatzResearch.WordTrace tailWord_4357162 prefixEnd_4357162 2237318395505586817336783 := by
  unfold tailWord_4357162
  simp only [CollatzResearch.WordTrace]
  refine ⟨39729688460188423217594435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105945835893835795246918493 39729688460188423217594435)
  ·
    refine ⟨59594532690282634826391653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39729688460188423217594435 59594532690282634826391653)
    ·
      refine ⟨11173974879427994029948435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 59594532690282634826391653 11173974879427994029948435)
      ·
        refine ⟨16760962319141991044922653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11173974879427994029948435 16760962319141991044922653)
        ·
          refine ⟨6285360869678246641845995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16760962319141991044922653 6285360869678246641845995)
          ·
            refine ⟨9428041304517369962768993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6285360869678246641845995 9428041304517369962768993)
            ·
              refine ⟨7071030978388027472076745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9428041304517369962768993 7071030978388027472076745)
              ·
                refine ⟨5303273233791020604057559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7071030978388027472076745 5303273233791020604057559)
                ·
                  refine ⟨7954909850686530906086339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5303273233791020604057559 7954909850686530906086339)
                  ·
                    refine ⟨11932364776029796359129509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7954909850686530906086339 11932364776029796359129509)
                    ·
                      refine ⟨2237318395505586817336783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11932364776029796359129509 2237318395505586817336783)
                      ·
                        rfl

theorem cell23_4357162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 2, 2, 1, 1, 4].length) (baseStart_4357162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4357162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4357162 prefixEnd_4357162 := by exact prefixLift 4357162
  have htrace : WordTrace (prefixWord ++ tailWord_4357162) baseStart_4357162 baseEnd_4357162 := by
    simpa [prefixWord, tailWord_4357162, baseEnd_4357162] using wordTrace_append hprefix tailTrace_4357162
  have hstable : (prefixWord ++ tailWord_4357162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4357162).length < 2 ^ (prefixWord ++ tailWord_4357162).sum := by decide
  have hdescent : baseEnd_4357162 < baseStart_4357162 := by decide
  rcases family_descends (prefixWord ++ tailWord_4357162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4357178 : List Nat := [3, 1, 1, 1, 3, 1, 2, 4, 1, 3, 3]
def baseStart_4357178 : Nat := 118140960795 + 4357178 * 2 ^ 59
def prefixEnd_4357178 : Nat := 4983230072969 + 3 ^ 40 * 4357178 * 2
def baseEnd_4357178 : Nat := 2237326611196058754736709

theorem tailTrace_4357178 : CollatzResearch.WordTrace tailWord_4357178 prefixEnd_4357178 2237326611196058754736709 := by
  unfold tailWord_4357178
  simp only [CollatzResearch.WordTrace]
  refine ⟨39729834352173931900740047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105946224939130485068640125 39729834352173931900740047)
  ·
    refine ⟨59594751528260897851110071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39729834352173931900740047 59594751528260897851110071)
    ·
      refine ⟨89392127292391346776665107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59594751528260897851110071 89392127292391346776665107)
      ·
        refine ⟨134088190938587020164997661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89392127292391346776665107 134088190938587020164997661)
        ·
          refine ⟨50283071601970132561874123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 134088190938587020164997661 50283071601970132561874123)
          ·
            refine ⟨75424607402955198842811185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50283071601970132561874123 75424607402955198842811185)
            ·
              refine ⟨56568455552216399132108389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75424607402955198842811185 56568455552216399132108389)
              ·
                refine ⟨10606585416040574837270323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 56568455552216399132108389 10606585416040574837270323)
                ·
                  refine ⟨15909878124060862255905485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10606585416040574837270323 15909878124060862255905485)
                  ·
                    refine ⟨5966204296522823345964557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15909878124060862255905485 5966204296522823345964557)
                    ·
                      refine ⟨2237326611196058754736709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5966204296522823345964557 2237326611196058754736709)
                      ·
                        rfl

theorem cell23_4357178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 4, 1, 3, 3].length) (baseStart_4357178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4357178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4357178 prefixEnd_4357178 := by exact prefixLift 4357178
  have htrace : WordTrace (prefixWord ++ tailWord_4357178) baseStart_4357178 baseEnd_4357178 := by
    simpa [prefixWord, tailWord_4357178, baseEnd_4357178] using wordTrace_append hprefix tailTrace_4357178
  have hstable : (prefixWord ++ tailWord_4357178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4357178).length < 2 ^ (prefixWord ++ tailWord_4357178).sum := by decide
  have hdescent : baseEnd_4357178 < baseStart_4357178 := by decide
  rcases family_descends (prefixWord ++ tailWord_4357178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4357182 : List Nat := [4, 2, 1, 3, 1, 1, 2, 3, 1, 2, 3]
def baseStart_4357182 : Nat := 118140960795 + 4357182 * 2 ^ 59
def prefixEnd_4357182 : Nat := 4983230072969 + 3 ^ 40 * 4357182 * 2
def baseEnd_4357182 : Nat := 2237328665118676739086691

theorem tailTrace_4357182 : CollatzResearch.WordTrace tailWord_4357182 prefixEnd_4357182 2237328665118676739086691 := by
  unfold tailWord_4357182
  simp only [CollatzResearch.WordTrace]
  refine ⟨19864935412585154535763225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 105946322200454157524070533 19864935412585154535763225)
  ·
    refine ⟨14898701559438865901822419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19864935412585154535763225 14898701559438865901822419)
    ·
      refine ⟨22348052339158298852733629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14898701559438865901822419 22348052339158298852733629)
      ·
        refine ⟨8380519627184362069775111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22348052339158298852733629 8380519627184362069775111)
        ·
          refine ⟨12570779440776543104662667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8380519627184362069775111 12570779440776543104662667)
          ·
            refine ⟨18856169161164814656994001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12570779440776543104662667 18856169161164814656994001)
            ·
              refine ⟨14142126870873610992745501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18856169161164814656994001 14142126870873610992745501)
              ·
                refine ⟨5303297576577604122279563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14142126870873610992745501 5303297576577604122279563)
                ·
                  refine ⟨7954946364866406183419345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5303297576577604122279563 7954946364866406183419345)
                  ·
                    refine ⟨5966209773649804637564509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7954946364866406183419345 5966209773649804637564509)
                    ·
                      refine ⟨2237328665118676739086691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5966209773649804637564509 2237328665118676739086691)
                      ·
                        rfl

theorem cell23_4357182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 2, 3, 1, 2, 3].length) (baseStart_4357182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4357182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4357182 prefixEnd_4357182 := by exact prefixLift 4357182
  have htrace : WordTrace (prefixWord ++ tailWord_4357182) baseStart_4357182 baseEnd_4357182 := by
    simpa [prefixWord, tailWord_4357182, baseEnd_4357182] using wordTrace_append hprefix tailTrace_4357182
  have hstable : (prefixWord ++ tailWord_4357182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4357182).length < 2 ^ (prefixWord ++ tailWord_4357182).sum := by decide
  have hdescent : baseEnd_4357182 < baseStart_4357182 := by decide
  rcases family_descends (prefixWord ++ tailWord_4357182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4357185 : List Nat := [1, 2, 5, 1, 4, 1, 9]
def baseStart_4357185 : Nat := 118140960795 + 4357185 * 2 ^ 59
def prefixEnd_4357185 : Nat := 4983230072969 + 3 ^ 40 * 4357185 * 2
def baseEnd_4357185 : Nat := 27621360562477039843817

theorem tailTrace_4357185 : CollatzResearch.WordTrace tailWord_4357185 prefixEnd_4357185 27621360562477039843817 := by
  unfold tailWord_4357185
  simp only [CollatzResearch.WordTrace]
  refine ⟨158919592719670367798465009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105946395146446911865643339 158919592719670367798465009)
  ·
    refine ⟨119189694539752775848848757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 158919592719670367798465009 119189694539752775848848757)
    ·
      refine ⟨11174033863101822735829571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 119189694539752775848848757 11174033863101822735829571)
      ·
        refine ⟨16761050794652734103744357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11174033863101822735829571 16761050794652734103744357)
        ·
          refine ⟨3142697023997387644452067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16761050794652734103744357 3142697023997387644452067)
          ·
            refine ⟨4714045535996081466678101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3142697023997387644452067 4714045535996081466678101)
            ·
              refine ⟨27621360562477039843817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4714045535996081466678101 27621360562477039843817)
              ·
                rfl

theorem cell23_4357185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 1, 9].length) (baseStart_4357185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4357185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4357185 prefixEnd_4357185 := by exact prefixLift 4357185
  have htrace : WordTrace (prefixWord ++ tailWord_4357185) baseStart_4357185 baseEnd_4357185 := by
    simpa [prefixWord, tailWord_4357185, baseEnd_4357185] using wordTrace_append hprefix tailTrace_4357185
  have hstable : (prefixWord ++ tailWord_4357185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4357185).length < 2 ^ (prefixWord ++ tailWord_4357185).sum := by decide
  have hdescent : baseEnd_4357185 < baseStart_4357185 := by decide
  rcases family_descends (prefixWord ++ tailWord_4357185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4357205 : List Nat := [1, 3, 2, 2, 1, 2, 2, 2, 3, 3, 2]
def baseStart_4357205 : Nat := 118140960795 + 4357205 * 2 ^ 59
def prefixEnd_4357205 : Nat := 4983230072969 + 3 ^ 40 * 4357205 * 2
def baseEnd_4357205 : Nat := 2237340475173730149099085

theorem tailTrace_4357205 : CollatzResearch.WordTrace tailWord_4357205 prefixEnd_4357205 2237340475173730149099085 := by
  unfold tailWord_4357205
  simp only [CollatzResearch.WordTrace]
  refine ⟨158920322179597911214193069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105946881453065274142795379 158920322179597911214193069)
  ·
    refine ⟨59595120817349216705322401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 158920322179597911214193069 59595120817349216705322401)
    ·
      refine ⟨44696340613011912528991801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59595120817349216705322401 44696340613011912528991801)
      ·
        refine ⟨33522255459758934396743851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44696340613011912528991801 33522255459758934396743851)
        ·
          refine ⟨50283383189638401595115777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33522255459758934396743851 50283383189638401595115777)
          ·
            refine ⟨37712537392228801196336833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50283383189638401595115777 37712537392228801196336833)
            ·
              refine ⟨28284403044171600897252625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37712537392228801196336833 28284403044171600897252625)
              ·
                refine ⟨21213302283128700672939469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28284403044171600897252625 21213302283128700672939469)
                ·
                  refine ⟨7954988356173262752352301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21213302283128700672939469 7954988356173262752352301)
                  ·
                    refine ⟨2983120633564973532132113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7954988356173262752352301 2983120633564973532132113)
                    ·
                      refine ⟨2237340475173730149099085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2983120633564973532132113 2237340475173730149099085)
                      ·
                        rfl

theorem cell23_4357205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 2, 3, 3, 2].length) (baseStart_4357205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4357205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4357205 prefixEnd_4357205 := by exact prefixLift 4357205
  have htrace : WordTrace (prefixWord ++ tailWord_4357205) baseStart_4357205 baseEnd_4357205 := by
    simpa [prefixWord, tailWord_4357205, baseEnd_4357205] using wordTrace_append hprefix tailTrace_4357205
  have hstable : (prefixWord ++ tailWord_4357205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4357205).length < 2 ^ (prefixWord ++ tailWord_4357205).sum := by decide
  have hdescent : baseEnd_4357205 < baseStart_4357205 := by decide
  rcases family_descends (prefixWord ++ tailWord_4357205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4357212 : List Nat := [2, 2, 4, 1, 1, 1, 3, 3, 2, 1, 3]
def baseStart_4357212 : Nat := 118140960795 + 4357212 * 2 ^ 59
def prefixEnd_4357212 : Nat := 4983230072969 + 3 ^ 40 * 4357212 * 2
def baseEnd_4357212 : Nat := 2237344069538311621711553

theorem tailTrace_4357212 : CollatzResearch.WordTrace tailWord_4357212 prefixEnd_4357212 2237344069538311621711553 := by
  unfold tailWord_4357212
  simp only [CollatzResearch.WordTrace]
  refine ⟨79460288745286275704848945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105947051660381700939798593 79460288745286275704848945)
  ·
    refine ⟨59595216558964706778636709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79460288745286275704848945 59595216558964706778636709)
    ·
      refine ⟨11174103104805882520994383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 59595216558964706778636709 11174103104805882520994383)
      ·
        refine ⟨16761154657208823781491575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11174103104805882520994383 16761154657208823781491575)
        ·
          refine ⟨25141731985813235672237363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16761154657208823781491575 25141731985813235672237363)
          ·
            refine ⟨37712597978719853508356045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25141731985813235672237363 37712597978719853508356045)
            ·
              refine ⟨14142224242019945065633517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37712597978719853508356045 14142224242019945065633517)
              ·
                refine ⟨5303334090757479399612569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14142224242019945065633517 5303334090757479399612569)
                ·
                  refine ⟨3977500568068109549709427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5303334090757479399612569 3977500568068109549709427)
                  ·
                    refine ⟨5966250852102164324564141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3977500568068109549709427 5966250852102164324564141)
                    ·
                      refine ⟨2237344069538311621711553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5966250852102164324564141 2237344069538311621711553)
                      ·
                        rfl

theorem cell23_4357212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 3, 3, 2, 1, 3].length) (baseStart_4357212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4357212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4357212 prefixEnd_4357212 := by exact prefixLift 4357212
  have htrace : WordTrace (prefixWord ++ tailWord_4357212) baseStart_4357212 baseEnd_4357212 := by
    simpa [prefixWord, tailWord_4357212, baseEnd_4357212] using wordTrace_append hprefix tailTrace_4357212
  have hstable : (prefixWord ++ tailWord_4357212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4357212).length < 2 ^ (prefixWord ++ tailWord_4357212).sum := by decide
  have hdescent : baseEnd_4357212 < baseStart_4357212 := by decide
  rcases family_descends (prefixWord ++ tailWord_4357212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4357258 : List Nat := [3, 1, 2, 3, 1, 1, 2, 3, 7]
def baseStart_4357258 : Nat := 118140960795 + 4357258 * 2 ^ 59
def prefixEnd_4357258 : Nat := 4983230072969 + 3 ^ 40 * 4357258 * 2
def baseEnd_4357258 : Nat := 248596409960935382415149

theorem tailTrace_4357258 : CollatzResearch.WordTrace tailWord_4357258 prefixEnd_4357258 248596409960935382415149 := by
  unfold tailWord_4357258
  simp only [CollatzResearch.WordTrace]
  refine ⟨39730563812101475316468107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105948170165603934177248285 39730563812101475316468107)
  ·
    refine ⟨59595845718152212974702161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39730563812101475316468107 59595845718152212974702161)
    ·
      refine ⟨44696884288614159731026621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59595845718152212974702161 44696884288614159731026621)
      ·
        refine ⟨16761331608230309899134983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44696884288614159731026621 16761331608230309899134983)
        ·
          refine ⟨25141997412345464848702475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16761331608230309899134983 25141997412345464848702475)
          ·
            refine ⟨37712996118518197273053713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25141997412345464848702475 37712996118518197273053713)
            ·
              refine ⟨28284747088888647954790285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37712996118518197273053713 28284747088888647954790285)
              ·
                refine ⟨10606780158333242983046357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28284747088888647954790285 10606780158333242983046357)
                ·
                  refine ⟨248596409960935382415149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10606780158333242983046357 248596409960935382415149)
                  ·
                    rfl

theorem cell23_4357258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 3, 7].length) (baseStart_4357258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4357258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4357258 prefixEnd_4357258 := by exact prefixLift 4357258
  have htrace : WordTrace (prefixWord ++ tailWord_4357258) baseStart_4357258 baseEnd_4357258 := by
    simpa [prefixWord, tailWord_4357258, baseEnd_4357258] using wordTrace_append hprefix tailTrace_4357258
  have hstable : (prefixWord ++ tailWord_4357258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4357258).length < 2 ^ (prefixWord ++ tailWord_4357258).sum := by decide
  have hdescent : baseEnd_4357258 < baseStart_4357258 := by decide
  rcases family_descends (prefixWord ++ tailWord_4357258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4357335 : List Nat := [1, 1, 3, 2, 1, 2, 4, 2, 3, 4]
def baseStart_4357335 : Nat := 118140960795 + 4357335 * 2 ^ 59
def prefixEnd_4357335 : Nat := 4983230072969 + 3 ^ 40 * 4357335 * 2
def baseEnd_4357335 : Nat := 745802409219604880157829

theorem tailTrace_4357335 : CollatzResearch.WordTrace tailWord_4357335 prefixEnd_4357335 745802409219604880157829 := by
  unfold tailWord_4357335
  simp only [CollatzResearch.WordTrace]
  refine ⟨158925063669126943416425459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105950042446084628944283639 158925063669126943416425459)
  ·
    refine ⟨238387595503690415124638189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158925063669126943416425459 238387595503690415124638189)
    ·
      refine ⟨89395348313883905671739321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 238387595503690415124638189 89395348313883905671739321)
      ·
        refine ⟨67046511235412929253804491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89395348313883905671739321 67046511235412929253804491)
        ·
          refine ⟨100569766853119393880706737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67046511235412929253804491 100569766853119393880706737)
          ·
            refine ⟨75427325139839545410530053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 100569766853119393880706737 75427325139839545410530053)
            ·
              refine ⟨14142623463719914764474385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 75427325139839545410530053 14142623463719914764474385)
              ·
                refine ⟨10606967597789936073355789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14142623463719914764474385 10606967597789936073355789)
                ·
                  refine ⟨3977612849171226027508421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10606967597789936073355789 3977612849171226027508421)
                  ·
                    refine ⟨745802409219604880157829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3977612849171226027508421 745802409219604880157829)
                    ·
                      rfl

theorem cell23_4357335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 4, 2, 3, 4].length) (baseStart_4357335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4357335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4357335 prefixEnd_4357335 := by exact prefixLift 4357335
  have htrace : WordTrace (prefixWord ++ tailWord_4357335) baseStart_4357335 baseEnd_4357335 := by
    simpa [prefixWord, tailWord_4357335, baseEnd_4357335] using wordTrace_append hprefix tailTrace_4357335
  have hstable : (prefixWord ++ tailWord_4357335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4357335).length < 2 ^ (prefixWord ++ tailWord_4357335).sum := by decide
  have hdescent : baseEnd_4357335 < baseStart_4357335 := by decide
  rcases family_descends (prefixWord ++ tailWord_4357335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4357338 : List Nat := [3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 4]
def baseStart_4357338 : Nat := 118140960795 + 4357338 * 2 ^ 59
def prefixEnd_4357338 : Nat := 4983230072969 + 3 ^ 40 * 4357338 * 2
def baseEnd_4357338 : Nat := 2237408768100778128735973

theorem tailTrace_4357338 : CollatzResearch.WordTrace tailWord_4357338 prefixEnd_4357338 2237408768100778128735973 := by
  unfold tailWord_4357338
  simp only [CollatzResearch.WordTrace]
  refine ⟨39731293272029018732196167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105950115392077383285856445 39731293272029018732196167)
  ·
    refine ⟨59596939908043528098294251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39731293272029018732196167 59596939908043528098294251)
    ·
      refine ⟨89395409862065292147441377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59596939908043528098294251 89395409862065292147441377)
      ·
        refine ⟨67046557396548969110581033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89395409862065292147441377 67046557396548969110581033)
        ·
          refine ⟨50284918047411726832935775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67046557396548969110581033 50284918047411726832935775)
          ·
            refine ⟨75427377071117590249403663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50284918047411726832935775 75427377071117590249403663)
            ·
              refine ⟨113141065606676385374105495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75427377071117590249403663 113141065606676385374105495)
              ·
                refine ⟨169711598410014578061158243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 113141065606676385374105495 169711598410014578061158243)
                ·
                  refine ⟨254567397615021867091737365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 169711598410014578061158243 254567397615021867091737365)
                  ·
                    refine ⟨11932846763204150019925189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 254567397615021867091737365 11932846763204150019925189)
                    ·
                      refine ⟨2237408768100778128735973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11932846763204150019925189 2237408768100778128735973)
                      ·
                        rfl

theorem cell23_4357338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 4].length) (baseStart_4357338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4357338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4357338 prefixEnd_4357338 := by exact prefixLift 4357338
  have htrace : WordTrace (prefixWord ++ tailWord_4357338) baseStart_4357338 baseEnd_4357338 := by
    simpa [prefixWord, tailWord_4357338, baseEnd_4357338] using wordTrace_append hprefix tailTrace_4357338
  have hstable : (prefixWord ++ tailWord_4357338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4357338).length < 2 ^ (prefixWord ++ tailWord_4357338).sum := by decide
  have hdescent : baseEnd_4357338 < baseStart_4357338 := by decide
  rcases family_descends (prefixWord ++ tailWord_4357338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4357345 : List Nat := [1, 2, 3, 1, 3, 2, 2, 1, 1, 4, 3]
def baseStart_4357345 : Nat := 118140960795 + 4357345 * 2 ^ 59
def prefixEnd_4357345 : Nat := 4983230072969 + 3 ^ 40 * 4357345 * 2
def baseEnd_4357345 : Nat := 2237412362465359601348441

theorem tailTrace_4357345 : CollatzResearch.WordTrace tailWord_4357345 prefixEnd_4357345 2237412362465359601348441 := by
  unfold tailWord_4357345
  simp only [CollatzResearch.WordTrace]
  refine ⟨158925428399090715124289489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105950285599393810082859659 158925428399090715124289489)
  ·
    refine ⟨119194071299318036343217117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 158925428399090715124289489 119194071299318036343217117)
    ·
      refine ⟨44697776737244263628706419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 119194071299318036343217117 44697776737244263628706419)
      ·
        refine ⟨67046665105866395443059629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44697776737244263628706419 67046665105866395443059629)
        ·
          refine ⟨25142499414699898291147361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 67046665105866395443059629 25142499414699898291147361)
          ·
            refine ⟨18856874561024923718360521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25142499414699898291147361 18856874561024923718360521)
            ·
              refine ⟨14142655920768692788770391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18856874561024923718360521 14142655920768692788770391)
              ·
                refine ⟨21213983881153039183155587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14142655920768692788770391 21213983881153039183155587)
                ·
                  refine ⟨31820975821729558774733381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21213983881153039183155587 31820975821729558774733381)
                  ·
                    refine ⟨5966432966574292270262509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 31820975821729558774733381 5966432966574292270262509)
                    ·
                      refine ⟨2237412362465359601348441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5966432966574292270262509 2237412362465359601348441)
                      ·
                        rfl

theorem cell23_4357345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 2, 1, 1, 4, 3].length) (baseStart_4357345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4357345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4357345 prefixEnd_4357345 := by exact prefixLift 4357345
  have htrace : WordTrace (prefixWord ++ tailWord_4357345) baseStart_4357345 baseEnd_4357345 := by
    simpa [prefixWord, tailWord_4357345, baseEnd_4357345] using wordTrace_append hprefix tailTrace_4357345
  have hstable : (prefixWord ++ tailWord_4357345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4357345).length < 2 ^ (prefixWord ++ tailWord_4357345).sum := by decide
  have hdescent : baseEnd_4357345 < baseStart_4357345 := by decide
  rcases family_descends (prefixWord ++ tailWord_4357345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4357348 : List Nat := [2, 3, 1, 1, 1, 2, 3, 2, 8]
def baseStart_4357348 : Nat := 118140960795 + 4357348 * 2 ^ 59
def prefixEnd_4357348 : Nat := 4983230072969 + 3 ^ 40 * 4357348 * 2
def baseEnd_4357348 : Nat := 248601544767480343290103

theorem tailTrace_4357348 : CollatzResearch.WordTrace tailWord_4357348 prefixEnd_4357348 248601544767480343290103 := by
  unfold tailWord_4357348
  simp only [CollatzResearch.WordTrace]
  refine ⟨79462768909039923318324349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105950358545386564424432465 79462768909039923318324349)
  ·
    refine ⟨29798538340889971244371631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79462768909039923318324349 29798538340889971244371631)
    ·
      refine ⟨44697807511334956866557447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29798538340889971244371631 44697807511334956866557447)
      ·
        refine ⟨67046711267002435299836171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44697807511334956866557447 67046711267002435299836171)
        ·
          refine ⟨100570066900503652949754257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67046711267002435299836171 100570066900503652949754257)
          ·
            refine ⟨75427550175377739712315693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 100570066900503652949754257 75427550175377739712315693)
            ·
              refine ⟨28285331315766652392118385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 75427550175377739712315693 28285331315766652392118385)
              ·
                refine ⟨21213998486824989294088789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28285331315766652392118385 21213998486824989294088789)
                ·
                  refine ⟨248601544767480343290103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 21213998486824989294088789 248601544767480343290103)
                  ·
                    rfl

theorem cell23_4357348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 2, 8].length) (baseStart_4357348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4357348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4357348 prefixEnd_4357348 := by exact prefixLift 4357348
  have htrace : WordTrace (prefixWord ++ tailWord_4357348) baseStart_4357348 baseEnd_4357348 := by
    simpa [prefixWord, tailWord_4357348, baseEnd_4357348] using wordTrace_append hprefix tailTrace_4357348
  have hstable : (prefixWord ++ tailWord_4357348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4357348).length < 2 ^ (prefixWord ++ tailWord_4357348).sum := by decide
  have hdescent : baseEnd_4357348 < baseStart_4357348 := by decide
  rcases family_descends (prefixWord ++ tailWord_4357348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4357369 : List Nat := [1, 2, 1, 3, 1, 1, 7, 2, 1, 4]
def baseStart_4357369 : Nat := 118140960795 + 4357369 * 2 ^ 59
def prefixEnd_4357369 : Nat := 4983230072969 + 3 ^ 40 * 4357369 * 2
def baseEnd_4357369 : Nat := 745808228667022502482777

theorem tailTrace_4357369 : CollatzResearch.WordTrace tailWord_4357369 prefixEnd_4357369 745808228667022502482777 := by
  unfold tailWord_4357369
  simp only [CollatzResearch.WordTrace]
  refine ⟨158926303751003767223163161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105950869167335844815442107 158926303751003767223163161)
  ·
    refine ⟨119194727813252825417372371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 158926303751003767223163161 119194727813252825417372371)
    ·
      refine ⟨178792091719879238126058557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119194727813252825417372371 178792091719879238126058557)
      ·
        refine ⟨67047034394954714297271959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 178792091719879238126058557 67047034394954714297271959)
        ·
          refine ⟨100570551592432071445907939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67047034394954714297271959 100570551592432071445907939)
          ·
            refine ⟨150855827388648107168861909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100570551592432071445907939 150855827388648107168861909)
            ·
              refine ⟨3535683454421440011770201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 150855827388648107168861909 3535683454421440011770201)
              ·
                refine ⟨2651762590816080008827651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3535683454421440011770201 2651762590816080008827651)
                ·
                  refine ⟨3977643886224120013241477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2651762590816080008827651 3977643886224120013241477)
                  ·
                    refine ⟨745808228667022502482777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3977643886224120013241477 745808228667022502482777)
                    ·
                      rfl

theorem cell23_4357369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 7, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 7, 2, 1, 4].length) (baseStart_4357369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4357369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4357369 prefixEnd_4357369 := by exact prefixLift 4357369
  have htrace : WordTrace (prefixWord ++ tailWord_4357369) baseStart_4357369 baseEnd_4357369 := by
    simpa [prefixWord, tailWord_4357369, baseEnd_4357369] using wordTrace_append hprefix tailTrace_4357369
  have hstable : (prefixWord ++ tailWord_4357369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4357369).length < 2 ^ (prefixWord ++ tailWord_4357369).sum := by decide
  have hdescent : baseEnd_4357369 < baseStart_4357369 := by decide
  rcases family_descends (prefixWord ++ tailWord_4357369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4357409 : List Nat := [1, 2, 3, 2, 1, 1, 1, 7, 1, 1, 3]
def baseStart_4357409 : Nat := 118140960795 + 4357409 * 2 ^ 59
def prefixEnd_4357409 : Nat := 4983230072969 + 3 ^ 40 * 4357409 * 2
def baseEnd_4357409 : Nat := 2237445225227247350948147

theorem tailTrace_4357409 : CollatzResearch.WordTrace tailWord_4357409 prefixEnd_4357409 2237445225227247350948147 := by
  unfold tailWord_4357409
  simp only [CollatzResearch.WordTrace]
  refine ⟨158927762670858854054619281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105951841780572569369746187 158927762670858854054619281)
  ·
    refine ⟨119195822003144140540964461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 158927762670858854054619281 119195822003144140540964461)
    ·
      refine ⟨44698433251179052702861673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 119195822003144140540964461 44698433251179052702861673)
      ·
        refine ⟨33523824938384289527146255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44698433251179052702861673 33523824938384289527146255)
        ·
          refine ⟨50285737407576434290719383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33523824938384289527146255 50285737407576434290719383)
          ·
            refine ⟨75428606111364651436079075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50285737407576434290719383 75428606111364651436079075)
            ·
              refine ⟨113142909167046977154118613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75428606111364651436079075 113142909167046977154118613)
              ·
                refine ⟨2651786933602663527049655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 113142909167046977154118613 2651786933602663527049655)
                ·
                  refine ⟨3977680400403995290574483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2651786933602663527049655 3977680400403995290574483)
                  ·
                    refine ⟨5966520600605992935861725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3977680400403995290574483 5966520600605992935861725)
                    ·
                      refine ⟨2237445225227247350948147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5966520600605992935861725 2237445225227247350948147)
                      ·
                        rfl

theorem cell23_4357409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 7, 1, 1, 3].length) (baseStart_4357409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4357409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4357409 prefixEnd_4357409 := by exact prefixLift 4357409
  have htrace : WordTrace (prefixWord ++ tailWord_4357409) baseStart_4357409 baseEnd_4357409 := by
    simpa [prefixWord, tailWord_4357409, baseEnd_4357409] using wordTrace_append hprefix tailTrace_4357409
  have hstable : (prefixWord ++ tailWord_4357409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4357409).length < 2 ^ (prefixWord ++ tailWord_4357409).sum := by decide
  have hdescent : baseEnd_4357409 < baseStart_4357409 := by decide
  rcases family_descends (prefixWord ++ tailWord_4357409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4357426 : List Nat := [3, 2, 1, 1, 4, 2, 1, 4, 1, 1, 3]
def baseStart_4357426 : Nat := 118140960795 + 4357426 * 2 ^ 59
def prefixEnd_4357426 : Nat := 4983230072969 + 3 ^ 40 * 4357426 * 2
def baseEnd_4357426 : Nat := 2237453954398373784435569

theorem tailTrace_4357426 : CollatzResearch.WordTrace tailWord_4357426 prefixEnd_4357426 2237453954398373784435569 := by
  unfold tailWord_4357426
  simp only [CollatzResearch.WordTrace]
  refine ⟨39732095677949316489497033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105952255141198177305325421 39732095677949316489497033)
  ·
    refine ⟨29799071758461987367122775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39732095677949316489497033 29799071758461987367122775)
    ·
      refine ⟨44698607637692981050684163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29799071758461987367122775 44698607637692981050684163)
      ·
        refine ⟨67047911456539471576026245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44698607637692981050684163 67047911456539471576026245)
        ·
          refine ⟨12571483398101150920504921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 67047911456539471576026245 12571483398101150920504921)
          ·
            refine ⟨9428612548575863190378691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12571483398101150920504921 9428612548575863190378691)
            ·
              refine ⟨14142918822863794785568037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9428612548575863190378691 14142918822863794785568037)
              ·
                refine ⟨2651797279286961522294007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14142918822863794785568037 2651797279286961522294007)
                ·
                  refine ⟨3977695918930442283441011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2651797279286961522294007 3977695918930442283441011)
                  ·
                    refine ⟨5966543878395663425161517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3977695918930442283441011 5966543878395663425161517)
                    ·
                      refine ⟨2237453954398373784435569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5966543878395663425161517 2237453954398373784435569)
                      ·
                        rfl

theorem cell23_4357426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 1, 4, 1, 1, 3].length) (baseStart_4357426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4357426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4357426 prefixEnd_4357426 := by exact prefixLift 4357426
  have htrace : WordTrace (prefixWord ++ tailWord_4357426) baseStart_4357426 baseEnd_4357426 := by
    simpa [prefixWord, tailWord_4357426, baseEnd_4357426] using wordTrace_append hprefix tailTrace_4357426
  have hstable : (prefixWord ++ tailWord_4357426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4357426).length < 2 ^ (prefixWord ++ tailWord_4357426).sum := by decide
  have hdescent : baseEnd_4357426 < baseStart_4357426 := by decide
  rcases family_descends (prefixWord ++ tailWord_4357426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4357452 : List Nat := [2, 2, 1, 3, 2, 2, 2, 1, 3, 2, 3]
def baseStart_4357452 : Nat := 118140960795 + 4357452 * 2 ^ 59
def prefixEnd_4357452 : Nat := 4983230072969 + 3 ^ 40 * 4357452 * 2
def baseEnd_4357452 : Nat := 2237467304895390682710449

theorem tailTrace_4357452 : CollatzResearch.WordTrace tailWord_4357452 prefixEnd_4357452 2237467304895390682710449 := by
  unfold tailWord_4357452
  simp only [CollatzResearch.WordTrace]
  refine ⟨79464665504851536199217305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105952887339802048265623073 79464665504851536199217305)
  ·
    refine ⟨59598499128638652149412979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79464665504851536199217305 59598499128638652149412979)
    ·
      refine ⟨89397748692957978224119469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59598499128638652149412979 89397748692957978224119469)
      ·
        refine ⟨33524155759859241834044801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 89397748692957978224119469 33524155759859241834044801)
        ·
          refine ⟨25143116819894431375533601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33524155759859241834044801 25143116819894431375533601)
          ·
            refine ⟨18857337614920823531650201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25143116819894431375533601 18857337614920823531650201)
            ·
              refine ⟨14143003211190617648737651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18857337614920823531650201 14143003211190617648737651)
              ·
                refine ⟨21214504816785926473106477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14143003211190617648737651 21214504816785926473106477)
                ·
                  refine ⟨7955439306294722427414929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21214504816785926473106477 7955439306294722427414929)
                  ·
                    refine ⟨5966579479721041820561197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7955439306294722427414929 5966579479721041820561197)
                    ·
                      refine ⟨2237467304895390682710449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5966579479721041820561197 2237467304895390682710449)
                      ·
                        rfl

theorem cell23_4357452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 2, 1, 3, 2, 3].length) (baseStart_4357452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4357452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4357452 prefixEnd_4357452 := by exact prefixLift 4357452
  have htrace : WordTrace (prefixWord ++ tailWord_4357452) baseStart_4357452 baseEnd_4357452 := by
    simpa [prefixWord, tailWord_4357452, baseEnd_4357452] using wordTrace_append hprefix tailTrace_4357452
  have hstable : (prefixWord ++ tailWord_4357452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4357452).length < 2 ^ (prefixWord ++ tailWord_4357452).sum := by decide
  have hdescent : baseEnd_4357452 < baseStart_4357452 := by decide
  rcases family_descends (prefixWord ++ tailWord_4357452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4357466 : List Nat := [3, 1, 1, 2, 1, 2, 3, 5, 1, 2, 2]
def baseStart_4357466 : Nat := 118140960795 + 4357466 * 2 ^ 59
def prefixEnd_4357466 : Nat := 4983230072969 + 3 ^ 40 * 4357466 * 2
def baseEnd_4357466 : Nat := 2237474493624553627935385

theorem tailTrace_4357466 : CollatzResearch.WordTrace tailWord_4357466 prefixEnd_4357466 2237474493624553627935385 := by
  unfold tailWord_4357466
  simp only [CollatzResearch.WordTrace]
  refine ⟨39732460407913088197361063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105953227754434901859629501 39732460407913088197361063)
  ·
    refine ⟨59598690611869632296041595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39732460407913088197361063 59598690611869632296041595)
    ·
      refine ⟨89398035917804448444062393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59598690611869632296041595 89398035917804448444062393)
      ·
        refine ⟨67048526938353336333046795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89398035917804448444062393 67048526938353336333046795)
        ·
          refine ⟨100572790407530004499570193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67048526938353336333046795 100572790407530004499570193)
          ·
            refine ⟨75429592805647503374677645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 100572790407530004499570193 75429592805647503374677645)
            ·
              refine ⟨28286097302117813765504117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 75429592805647503374677645 28286097302117813765504117)
              ·
                refine ⟨2651821622073545040516011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28286097302117813765504117 2651821622073545040516011)
                ·
                  refine ⟨3977732433110317560774017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2651821622073545040516011 3977732433110317560774017)
                  ·
                    refine ⟨2983299324832738170580513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3977732433110317560774017 2983299324832738170580513)
                    ·
                      refine ⟨2237474493624553627935385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2983299324832738170580513 2237474493624553627935385)
                      ·
                        rfl

theorem cell23_4357466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 5, 1, 2, 2].length) (baseStart_4357466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4357466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4357466 prefixEnd_4357466 := by exact prefixLift 4357466
  have htrace : WordTrace (prefixWord ++ tailWord_4357466) baseStart_4357466 baseEnd_4357466 := by
    simpa [prefixWord, tailWord_4357466, baseEnd_4357466] using wordTrace_append hprefix tailTrace_4357466
  have hstable : (prefixWord ++ tailWord_4357466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4357466).length < 2 ^ (prefixWord ++ tailWord_4357466).sum := by decide
  have hdescent : baseEnd_4357466 < baseStart_4357466 := by decide
  rcases family_descends (prefixWord ++ tailWord_4357466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4357506 : List Nat := [3, 4, 2, 1, 1, 3, 2, 7]
def baseStart_4357506 : Nat := 118140960795 + 4357506 * 2 ^ 59
def prefixEnd_4357506 : Nat := 4983230072969 + 3 ^ 40 * 4357506 * 2
def baseEnd_4357506 : Nat := 82870186401879017460563

theorem tailTrace_4357506 : CollatzResearch.WordTrace tailWord_4357506 prefixEnd_4357506 82870186401879017460563 := by
  unfold tailWord_4357506
  simp only [CollatzResearch.WordTrace]
  refine ⟨39732825137876859905225093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105954200367671626413933581 39732825137876859905225093)
  ·
    refine ⟨7449904713351911232229705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39732825137876859905225093 7449904713351911232229705)
    ·
      refine ⟨5587428535013933424172279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7449904713351911232229705 5587428535013933424172279)
      ·
        refine ⟨8381142802520900136258419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5587428535013933424172279 8381142802520900136258419)
        ·
          refine ⟨12571714203781350204387629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8381142802520900136258419 12571714203781350204387629)
          ·
            refine ⟨4714392826418006326645361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12571714203781350204387629 4714392826418006326645361)
            ·
              refine ⟨3535794619813504744984021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4714392826418006326645361 3535794619813504744984021)
              ·
                refine ⟨82870186401879017460563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3535794619813504744984021 82870186401879017460563)
                ·
                  rfl

theorem cell23_4357506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 3, 2, 7].length) (baseStart_4357506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4357506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4357506 prefixEnd_4357506 := by exact prefixLift 4357506
  have htrace : WordTrace (prefixWord ++ tailWord_4357506) baseStart_4357506 baseEnd_4357506 := by
    simpa [prefixWord, tailWord_4357506, baseEnd_4357506] using wordTrace_append hprefix tailTrace_4357506
  have hstable : (prefixWord ++ tailWord_4357506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4357506).length < 2 ^ (prefixWord ++ tailWord_4357506).sum := by decide
  have hdescent : baseEnd_4357506 < baseStart_4357506 := by decide
  rcases family_descends (prefixWord ++ tailWord_4357506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4357509 : List Nat := [1, 3, 1, 1, 3, 1, 3, 4, 1, 3, 2]
def baseStart_4357509 : Nat := 118140960795 + 4357509 * 2 ^ 59
def prefixEnd_4357509 : Nat := 4983230072969 + 3 ^ 40 * 4357509 * 2
def baseEnd_4357509 : Nat := 2237496573292696959697687

theorem tailTrace_4357509 : CollatzResearch.WordTrace tailWord_4357509 prefixEnd_4357509 2237496573292696959697687 := by
  unfold tailWord_4357509
  simp only [CollatzResearch.WordTrace]
  refine ⟨158931409970496571133259581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105954273313664380755506387 158931409970496571133259581)
  ·
    refine ⟨59599278738936214174972343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 158931409970496571133259581 59599278738936214174972343)
    ·
      refine ⟨89398918108404321262458515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59599278738936214174972343 89398918108404321262458515)
      ·
        refine ⟨134098377162606481893687773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89398918108404321262458515 134098377162606481893687773)
        ·
          refine ⟨50286891435977430710132915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 134098377162606481893687773 50286891435977430710132915)
          ·
            refine ⟨75430337153966146065199373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50286891435977430710132915 75430337153966146065199373)
            ·
              refine ⟨28286376432737304774449765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 75430337153966146065199373 28286376432737304774449765)
              ·
                refine ⟨5303695581138244645209331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28286376432737304774449765 5303695581138244645209331)
                ·
                  refine ⟨7955543371707366967813997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5303695581138244645209331 7955543371707366967813997)
                  ·
                    refine ⟨2983328764390262612930249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7955543371707366967813997 2983328764390262612930249)
                    ·
                      refine ⟨2237496573292696959697687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2983328764390262612930249 2237496573292696959697687)
                      ·
                        rfl

theorem cell23_4357509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 4, 1, 3, 2].length) (baseStart_4357509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4357509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4357509 prefixEnd_4357509 := by exact prefixLift 4357509
  have htrace : WordTrace (prefixWord ++ tailWord_4357509) baseStart_4357509 baseEnd_4357509 := by
    simpa [prefixWord, tailWord_4357509, baseEnd_4357509] using wordTrace_append hprefix tailTrace_4357509
  have hstable : (prefixWord ++ tailWord_4357509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4357509).length < 2 ^ (prefixWord ++ tailWord_4357509).sum := by decide
  have hdescent : baseEnd_4357509 < baseStart_4357509 := by decide
  rcases family_descends (prefixWord ++ tailWord_4357509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4357525 : List Nat := [1, 3, 2, 1, 1, 2, 3, 1, 1, 3, 5]
def baseStart_4357525 : Nat := 118140960795 + 4357525 * 2 ^ 59
def prefixEnd_4357525 : Nat := 4983230072969 + 3 ^ 40 * 4357525 * 2
def baseEnd_4357525 : Nat := 2237504788983168897097613

theorem tailTrace_4357525 : CollatzResearch.WordTrace tailWord_4357525 prefixEnd_4357525 2237504788983168897097613 := by
  unfold tailWord_4357525
  simp only [CollatzResearch.WordTrace]
  refine ⟨158931993538438605865842029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105954662358959070577228019 158931993538438605865842029)
  ·
    refine ⟨59599497576914477199690761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 158931993538438605865842029 59599497576914477199690761)
    ·
      refine ⟨44699623182685857899768071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59599497576914477199690761 44699623182685857899768071)
      ·
        refine ⟨67049434774028786849652107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44699623182685857899768071 67049434774028786849652107)
        ·
          refine ⟨100574152161043180274478161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67049434774028786849652107 100574152161043180274478161)
          ·
            refine ⟨75430614120782385205858621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 100574152161043180274478161 75430614120782385205858621)
            ·
              refine ⟨28286480295293394452196983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 75430614120782385205858621 28286480295293394452196983)
              ·
                refine ⟨42429720442940091678295475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28286480295293394452196983 42429720442940091678295475)
                ·
                  refine ⟨63644580664410137517443213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42429720442940091678295475 63644580664410137517443213)
                  ·
                    refine ⟨23866717749153801569041205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 63644580664410137517443213 23866717749153801569041205)
                    ·
                      refine ⟨2237504788983168897097613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23866717749153801569041205 2237504788983168897097613)
                      ·
                        rfl

theorem cell23_4357525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 1, 1, 3, 5].length) (baseStart_4357525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4357525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4357525 prefixEnd_4357525 := by exact prefixLift 4357525
  have htrace : WordTrace (prefixWord ++ tailWord_4357525) baseStart_4357525 baseEnd_4357525 := by
    simpa [prefixWord, tailWord_4357525, baseEnd_4357525] using wordTrace_append hprefix tailTrace_4357525
  have hstable : (prefixWord ++ tailWord_4357525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4357525).length < 2 ^ (prefixWord ++ tailWord_4357525).sum := by decide
  have hdescent : baseEnd_4357525 < baseStart_4357525 := by decide
  rcases family_descends (prefixWord ++ tailWord_4357525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4357539 : List Nat := [1, 1, 1, 4, 1, 3, 1, 3, 4, 2, 2]
def baseStart_4357539 : Nat := 118140960795 + 4357539 * 2 ^ 59
def prefixEnd_4357539 : Nat := 4983230072969 + 3 ^ 40 * 4357539 * 2
def baseEnd_4357539 : Nat := 2237511977712331842322549

theorem tailTrace_4357539 : CollatzResearch.WordTrace tailWord_4357539 prefixEnd_4357539 2237511977712331842322549 := by
  unfold tailWord_4357539
  simp only [CollatzResearch.WordTrace]
  refine ⟨158932504160387886256851671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105955002773591924171234447 158932504160387886256851671)
  ·
    refine ⟨238398756240581829385277507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158932504160387886256851671 238398756240581829385277507)
    ·
      refine ⟨357598134360872744077916261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 238398756240581829385277507 357598134360872744077916261)
      ·
        refine ⟨67049650192663639514609299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 357598134360872744077916261 67049650192663639514609299)
        ·
          refine ⟨100574475288995459271913949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67049650192663639514609299 100574475288995459271913949)
          ·
            refine ⟨37715428233373297226967731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 100574475288995459271913949 37715428233373297226967731)
            ·
              refine ⟨56573142350059945840451597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37715428233373297226967731 56573142350059945840451597)
              ·
                refine ⟨21214928381272479690169349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56573142350059945840451597 21214928381272479690169349)
                ·
                  refine ⟨3977799071488589941906753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21214928381272479690169349 3977799071488589941906753)
                  ·
                    refine ⟨2983349303616442456430065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3977799071488589941906753 2983349303616442456430065)
                    ·
                      refine ⟨2237511977712331842322549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2983349303616442456430065 2237511977712331842322549)
                      ·
                        rfl

theorem cell23_4357539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 3, 4, 2, 2].length) (baseStart_4357539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4357539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4357539 prefixEnd_4357539 := by exact prefixLift 4357539
  have htrace : WordTrace (prefixWord ++ tailWord_4357539) baseStart_4357539 baseEnd_4357539 := by
    simpa [prefixWord, tailWord_4357539, baseEnd_4357539] using wordTrace_append hprefix tailTrace_4357539
  have hstable : (prefixWord ++ tailWord_4357539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4357539).length < 2 ^ (prefixWord ++ tailWord_4357539).sum := by decide
  have hdescent : baseEnd_4357539 < baseStart_4357539 := by decide
  rcases family_descends (prefixWord ++ tailWord_4357539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4357590 : List Nat := [5, 2, 1, 1, 1, 3, 2, 2, 2, 2, 2]
def baseStart_4357590 : Nat := 118140960795 + 4357590 * 2 ^ 59
def prefixEnd_4357590 : Nat := 4983230072969 + 3 ^ 40 * 4357590 * 2
def baseEnd_4357590 : Nat := 2237538165225711142784815

theorem tailTrace_4357590 : CollatzResearch.WordTrace tailWord_4357590 prefixEnd_4357590 2237538165225711142784815 := by
  unfold tailWord_4357590
  simp only [CollatzResearch.WordTrace]
  refine ⟨9933397767700195122934889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 105956242855468747977972149 9933397767700195122934889)
  ·
    refine ⟨7450048325775146342201167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9933397767700195122934889 7450048325775146342201167)
    ·
      refine ⟨11175072488662719513301751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7450048325775146342201167 11175072488662719513301751)
      ·
        refine ⟨16762608732994079269952627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11175072488662719513301751 16762608732994079269952627)
        ·
          refine ⟨25143913099491118904928941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16762608732994079269952627 25143913099491118904928941)
          ·
            refine ⟨9428967412309169589348353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25143913099491118904928941 9428967412309169589348353)
            ·
              refine ⟨7071725559231877192011265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9428967412309169589348353 7071725559231877192011265)
              ·
                refine ⟨5303794169423907894008449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7071725559231877192011265 5303794169423907894008449)
                ·
                  refine ⟨3977845627067930920506337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5303794169423907894008449 3977845627067930920506337)
                  ·
                    refine ⟨2983384220300948190379753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3977845627067930920506337 2983384220300948190379753)
                    ·
                      refine ⟨2237538165225711142784815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2983384220300948190379753 2237538165225711142784815)
                      ·
                        rfl

theorem cell23_4357590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 2, 2, 2, 2, 2].length) (baseStart_4357590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4357590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4357590 prefixEnd_4357590 := by exact prefixLift 4357590
  have htrace : WordTrace (prefixWord ++ tailWord_4357590) baseStart_4357590 baseEnd_4357590 := by
    simpa [prefixWord, tailWord_4357590, baseEnd_4357590] using wordTrace_append hprefix tailTrace_4357590
  have hstable : (prefixWord ++ tailWord_4357590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4357590).length < 2 ^ (prefixWord ++ tailWord_4357590).sum := by decide
  have hdescent : baseEnd_4357590 < baseStart_4357590 := by decide
  rcases family_descends (prefixWord ++ tailWord_4357590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4357592 : List Nat := [2, 1, 2, 2, 2, 1, 4, 2, 2, 5]
def baseStart_4357592 : Nat := 118140960795 + 4357592 * 2 ^ 59
def prefixEnd_4357592 : Nat := 4983230072969 + 3 ^ 40 * 4357592 * 2
def baseEnd_4357592 : Nat := 745846397395673378319935

theorem tailTrace_4357592 : CollatzResearch.WordTrace tailWord_4357592 prefixEnd_4357592 745846397395673378319935 := by
  unfold tailWord_4357592
  simp only [CollatzResearch.WordTrace]
  refine ⟨79467218614597938154265515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105956291486130584205687353 79467218614597938154265515)
  ·
    refine ⟨119200827921896907231398273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79467218614597938154265515 119200827921896907231398273)
    ·
      refine ⟨89400620941422680423548705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119200827921896907231398273 89400620941422680423548705)
      ·
        refine ⟨67050465706067010317661529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89400620941422680423548705 67050465706067010317661529)
        ·
          refine ⟨50287849279550257738246147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67050465706067010317661529 50287849279550257738246147)
          ·
            refine ⟨75431773919325386607369221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50287849279550257738246147 75431773919325386607369221)
            ·
              refine ⟨14143457609873509988881729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 75431773919325386607369221 14143457609873509988881729)
              ·
                refine ⟨10607593207405132491661297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14143457609873509988881729 10607593207405132491661297)
                ·
                  refine ⟨7955694905553849368745973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10607593207405132491661297 7955694905553849368745973)
                  ·
                    refine ⟨745846397395673378319935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7955694905553849368745973 745846397395673378319935)
                    ·
                      rfl

theorem cell23_4357592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 4, 2, 2, 5].length) (baseStart_4357592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4357592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4357592 prefixEnd_4357592 := by exact prefixLift 4357592
  have htrace : WordTrace (prefixWord ++ tailWord_4357592) baseStart_4357592 baseEnd_4357592 := by
    simpa [prefixWord, tailWord_4357592, baseEnd_4357592] using wordTrace_append hprefix tailTrace_4357592
  have hstable : (prefixWord ++ tailWord_4357592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4357592).length < 2 ^ (prefixWord ++ tailWord_4357592).sum := by decide
  have hdescent : baseEnd_4357592 < baseStart_4357592 := by decide
  rcases family_descends (prefixWord ++ tailWord_4357592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4357629 : List Nat := [1, 4, 1, 1, 1, 4, 3, 1, 2, 1, 4]
def baseStart_4357629 : Nat := 118140960795 + 4357629 * 2 ^ 59
def prefixEnd_4357629 : Nat := 4983230072969 + 3 ^ 40 * 4357629 * 2
def baseEnd_4357629 : Nat := 2237558190971236490197135

theorem tailTrace_4357629 : CollatzResearch.WordTrace tailWord_4357629 prefixEnd_4357629 2237558190971236490197135 := by
  unfold tailWord_4357629
  simp only [CollatzResearch.WordTrace]
  refine ⟨158935786730061831627627941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105957191153374554418418627 158935786730061831627627941)
  ·
    refine ⟨29800460011886593430180239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 158935786730061831627627941 29800460011886593430180239)
    ·
      refine ⟨44700690017829890145270359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29800460011886593430180239 44700690017829890145270359)
      ·
        refine ⟨67051035026744835217905539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44700690017829890145270359 67051035026744835217905539)
        ·
          refine ⟨100576552540117252826858309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67051035026744835217905539 100576552540117252826858309)
          ·
            refine ⟨18858103601271984905035933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 100576552540117252826858309 18858103601271984905035933)
            ·
              refine ⟨7071788850476994339388475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18858103601271984905035933 7071788850476994339388475)
              ·
                refine ⟨10607683275715491509082713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7071788850476994339388475 10607683275715491509082713)
                ·
                  refine ⟨7955762456786618631812035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10607683275715491509082713 7955762456786618631812035)
                  ·
                    refine ⟨11933643685179927947718053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7955762456786618631812035 11933643685179927947718053)
                    ·
                      refine ⟨2237558190971236490197135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11933643685179927947718053 2237558190971236490197135)
                      ·
                        rfl

theorem cell23_4357629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 3, 1, 2, 1, 4].length) (baseStart_4357629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4357629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4357629 prefixEnd_4357629 := by exact prefixLift 4357629
  have htrace : WordTrace (prefixWord ++ tailWord_4357629) baseStart_4357629 baseEnd_4357629 := by
    simpa [prefixWord, tailWord_4357629, baseEnd_4357629] using wordTrace_append hprefix tailTrace_4357629
  have hstable : (prefixWord ++ tailWord_4357629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4357629).length < 2 ^ (prefixWord ++ tailWord_4357629).sum := by decide
  have hdescent : baseEnd_4357629 < baseStart_4357629 := by decide
  rcases family_descends (prefixWord ++ tailWord_4357629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4357642 : List Nat := [3, 1, 2, 2, 2, 2, 1, 1, 2, 1, 6]
def baseStart_4357642 : Nat := 118140960795 + 4357642 * 2 ^ 59
def prefixEnd_4357642 : Nat := 4983230072969 + 3 ^ 40 * 4357642 * 2
def baseEnd_4357642 : Nat := 2237564866219744939334575

theorem tailTrace_4357642 : CollatzResearch.WordTrace tailWord_4357642 prefixEnd_4357642 2237564866219744939334575 := by
  unfold tailWord_4357642
  simp only [CollatzResearch.WordTrace]
  refine ⟨39734065219753683711962795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105957507252676489898567453 39734065219753683711962795)
  ·
    refine ⟨59601097829630525567944193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39734065219753683711962795 59601097829630525567944193)
    ·
      refine ⟨44700823372222894175958145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59601097829630525567944193 44700823372222894175958145)
      ·
        refine ⟨33525617529167170631968609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44700823372222894175958145 33525617529167170631968609)
        ·
          refine ⟨25144213146875377973976457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33525617529167170631968609 25144213146875377973976457)
          ·
            refine ⟨18858159860156533480482343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25144213146875377973976457 18858159860156533480482343)
            ·
              refine ⟨28287239790234800220723515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18858159860156533480482343 28287239790234800220723515)
              ·
                refine ⟨42430859685352200331085273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28287239790234800220723515 42430859685352200331085273)
                ·
                  refine ⟨31823144764014150248313955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42430859685352200331085273 31823144764014150248313955)
                  ·
                    refine ⟨47734717146021225372470933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 31823144764014150248313955 47734717146021225372470933)
                    ·
                      refine ⟨2237564866219744939334575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 47734717146021225372470933 2237564866219744939334575)
                      ·
                        rfl

theorem cell23_4357642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 1, 2, 1, 6].length) (baseStart_4357642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4357642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4357642 prefixEnd_4357642 := by exact prefixLift 4357642
  have htrace : WordTrace (prefixWord ++ tailWord_4357642) baseStart_4357642 baseEnd_4357642 := by
    simpa [prefixWord, tailWord_4357642, baseEnd_4357642] using wordTrace_append hprefix tailTrace_4357642
  have hstable : (prefixWord ++ tailWord_4357642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4357642).length < 2 ^ (prefixWord ++ tailWord_4357642).sum := by decide
  have hdescent : baseEnd_4357642 < baseStart_4357642 := by decide
  rcases family_descends (prefixWord ++ tailWord_4357642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4357656 : List Nat := [2, 1, 2, 3, 4, 1, 2, 1, 3, 4]
def baseStart_4357656 : Nat := 118140960795 + 4357656 * 2 ^ 59
def prefixEnd_4357656 : Nat := 4983230072969 + 3 ^ 40 * 4357656 * 2
def baseEnd_4357656 : Nat := 745857351649635961519837

theorem tailTrace_4357656 : CollatzResearch.WordTrace tailWord_4357656 prefixEnd_4357656 745857351649635961519837 := by
  unfold tailWord_4357656
  simp only [CollatzResearch.WordTrace]
  refine ⟨79468385750482007619430411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105957847667309343492573881 79468385750482007619430411)
  ·
    refine ⟨119202578625723011429145617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79468385750482007619430411 119202578625723011429145617)
    ·
      refine ⟨89401933969292258571859213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119202578625723011429145617 89401933969292258571859213)
      ·
        refine ⟨33525725238484596964447205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 89401933969292258571859213 33525725238484596964447205)
        ·
          refine ⟨6286073482215861930833851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33525725238484596964447205 6286073482215861930833851)
          ·
            refine ⟨9429110223323792896250777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6286073482215861930833851 9429110223323792896250777)
            ·
              refine ⟨7071832667492844672188083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9429110223323792896250777 7071832667492844672188083)
              ·
                refine ⟨10607749001239267008282125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7071832667492844672188083 10607749001239267008282125)
                ·
                  refine ⟨3977905875464725128105797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10607749001239267008282125 3977905875464725128105797)
                  ·
                    refine ⟨745857351649635961519837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3977905875464725128105797 745857351649635961519837)
                    ·
                      rfl

theorem cell23_4357656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 2, 1, 3, 4].length) (baseStart_4357656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4357656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4357656 prefixEnd_4357656 := by exact prefixLift 4357656
  have htrace : WordTrace (prefixWord ++ tailWord_4357656) baseStart_4357656 baseEnd_4357656 := by
    simpa [prefixWord, tailWord_4357656, baseEnd_4357656] using wordTrace_append hprefix tailTrace_4357656
  have hstable : (prefixWord ++ tailWord_4357656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4357656).length < 2 ^ (prefixWord ++ tailWord_4357656).sum := by decide
  have hdescent : baseEnd_4357656 < baseStart_4357656 := by decide
  rcases family_descends (prefixWord ++ tailWord_4357656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4357706 : List Nat := [3, 1, 2, 1, 1, 3, 3, 2, 2, 3, 2]
def baseStart_4357706 : Nat := 118140960795 + 4357706 * 2 ^ 59
def prefixEnd_4357706 : Nat := 4983230072969 + 3 ^ 40 * 4357706 * 2
def baseEnd_4357706 : Nat := 2237597728981632688934281

theorem tailTrace_4357706 : CollatzResearch.WordTrace tailWord_4357706 prefixEnd_4357706 2237597728981632688934281 := by
  unfold tailWord_4357706
  simp only [CollatzResearch.WordTrace]
  refine ⟨39734648787695718444545243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105959063433855249185453981 39734648787695718444545243)
  ·
    refine ⟨59601973181543577666817865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39734648787695718444545243 59601973181543577666817865)
    ·
      refine ⟨44701479886157683250113399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59601973181543577666817865 44701479886157683250113399)
      ·
        refine ⟨67052219829236524875170099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44701479886157683250113399 67052219829236524875170099)
        ·
          refine ⟨100578329743854787312755149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67052219829236524875170099 100578329743854787312755149)
          ·
            refine ⟨37716873653945545242283181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 100578329743854787312755149 37716873653945545242283181)
            ·
              refine ⟨14143827620229579465856193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37716873653945545242283181 14143827620229579465856193)
              ·
                refine ⟨10607870715172184599392145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14143827620229579465856193 10607870715172184599392145)
                ·
                  refine ⟨7955903036379138449544109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10607870715172184599392145 7955903036379138449544109)
                  ·
                    refine ⟨2983463638642176918579041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7955903036379138449544109 2983463638642176918579041)
                    ·
                      refine ⟨2237597728981632688934281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2983463638642176918579041 2237597728981632688934281)
                      ·
                        rfl

theorem cell23_4357706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 3, 2, 2, 3, 2].length) (baseStart_4357706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4357706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4357706 prefixEnd_4357706 := by exact prefixLift 4357706
  have htrace : WordTrace (prefixWord ++ tailWord_4357706) baseStart_4357706 baseEnd_4357706 := by
    simpa [prefixWord, tailWord_4357706, baseEnd_4357706] using wordTrace_append hprefix tailTrace_4357706
  have hstable : (prefixWord ++ tailWord_4357706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4357706).length < 2 ^ (prefixWord ++ tailWord_4357706).sum := by decide
  have hdescent : baseEnd_4357706 < baseStart_4357706 := by decide
  rcases family_descends (prefixWord ++ tailWord_4357706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4357736 : List Nat := [2, 1, 4, 3, 1, 2, 1, 1, 3, 1, 4]
def baseStart_4357736 : Nat := 118140960795 + 4357736 * 2 ^ 59
def prefixEnd_4357736 : Nat := 4983230072969 + 3 ^ 40 * 4357736 * 2
def baseEnd_4357736 : Nat := 2237613133401267571559143

theorem tailTrace_4357736 : CollatzResearch.WordTrace tailWord_4357736 prefixEnd_4357736 2237613133401267571559143 := by
  unfold tailWord_4357736
  simp only [CollatzResearch.WordTrace]
  refine ⟨79469844670337094450886531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105959792893782792601182041 79469844670337094450886531)
  ·
    refine ⟨119204767005505641676329797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79469844670337094450886531 119204767005505641676329797)
    ·
      refine ⟨22350893813532307814311837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 119204767005505641676329797 22350893813532307814311837)
      ·
        refine ⟨8381585180074615430366939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22350893813532307814311837 8381585180074615430366939)
        ·
          refine ⟨12572377770111923145550409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8381585180074615430366939 12572377770111923145550409)
          ·
            refine ⟨9429283327583942359162807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12572377770111923145550409 9429283327583942359162807)
            ·
              refine ⟨14143924991375913538744211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9429283327583942359162807 14143924991375913538744211)
              ·
                refine ⟨21215887487063870308116317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14143924991375913538744211 21215887487063870308116317)
                ·
                  refine ⟨7955957807648951365543619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21215887487063870308116317 7955957807648951365543619)
                  ·
                    refine ⟨11933936711473427048315429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7955957807648951365543619 11933936711473427048315429)
                    ·
                      refine ⟨2237613133401267571559143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11933936711473427048315429 2237613133401267571559143)
                      ·
                        rfl

theorem cell23_4357736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 1, 1, 3, 1, 4].length) (baseStart_4357736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4357736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4357736 prefixEnd_4357736 := by exact prefixLift 4357736
  have htrace : WordTrace (prefixWord ++ tailWord_4357736) baseStart_4357736 baseEnd_4357736 := by
    simpa [prefixWord, tailWord_4357736, baseEnd_4357736] using wordTrace_append hprefix tailTrace_4357736
  have hstable : (prefixWord ++ tailWord_4357736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4357736).length < 2 ^ (prefixWord ++ tailWord_4357736).sum := by decide
  have hdescent : baseEnd_4357736 < baseStart_4357736 := by decide
  rcases family_descends (prefixWord ++ tailWord_4357736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4357764 : List Nat := [2, 3, 2, 1, 5, 1, 2, 2, 1, 1, 3]
def baseStart_4357764 : Nat := 118140960795 + 4357764 * 2 ^ 59
def prefixEnd_4357764 : Nat := 4983230072969 + 3 ^ 40 * 4357764 * 2
def baseEnd_4357764 : Nat := 2237627510859593462009015

theorem tailTrace_4357764 : CollatzResearch.WordTrace tailWord_4357764 prefixEnd_4357764 2237627510859593462009015 := by
  unfold tailWord_4357764
  simp only [CollatzResearch.WordTrace]
  refine ⟨79470355292286374841896173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105960473723048499789194897 79470355292286374841896173)
  ·
    refine ⟨29801383234607390565711065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79470355292286374841896173 29801383234607390565711065)
    ·
      refine ⟨22351037425955542924283299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29801383234607390565711065 22351037425955542924283299)
      ·
        refine ⟨33526556138933314386424949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22351037425955542924283299 33526556138933314386424949)
        ·
          refine ⟨3143114638024998223727339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 33526556138933314386424949 3143114638024998223727339)
          ·
            refine ⟨4714671957037497335591009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3143114638024998223727339 4714671957037497335591009)
            ·
              refine ⟨3536003967778123001693257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4714671957037497335591009 3536003967778123001693257)
              ·
                refine ⟨2652002975833592251269943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3536003967778123001693257 2652002975833592251269943)
                ·
                  refine ⟨3978004463750388376904915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2652002975833592251269943 3978004463750388376904915)
                  ·
                    refine ⟨5967006695625582565357373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3978004463750388376904915 5967006695625582565357373)
                    ·
                      refine ⟨2237627510859593462009015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5967006695625582565357373 2237627510859593462009015)
                      ·
                        rfl

theorem cell23_4357764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 1, 2, 2, 1, 1, 3].length) (baseStart_4357764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4357764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4357764 prefixEnd_4357764 := by exact prefixLift 4357764
  have htrace : WordTrace (prefixWord ++ tailWord_4357764) baseStart_4357764 baseEnd_4357764 := by
    simpa [prefixWord, tailWord_4357764, baseEnd_4357764] using wordTrace_append hprefix tailTrace_4357764
  have hstable : (prefixWord ++ tailWord_4357764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4357764).length < 2 ^ (prefixWord ++ tailWord_4357764).sum := by decide
  have hdescent : baseEnd_4357764 < baseStart_4357764 := by decide
  rcases family_descends (prefixWord ++ tailWord_4357764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4357772 : List Nat := [2, 2, 1, 2, 1, 1, 3, 1, 1, 9]
def baseStart_4357772 : Nat := 118140960795 + 4357772 * 2 ^ 59
def prefixEnd_4357772 : Nat := 4983230072969 + 3 ^ 40 * 4357772 * 2
def baseEnd_4357772 : Nat := 745877206234943143569659

theorem tailTrace_4357772 : CollatzResearch.WordTrace tailWord_4357772 prefixEnd_4357772 745877206234943143569659 := by
  unfold tailWord_4357772
  simp only [CollatzResearch.WordTrace]
  refine ⟨79470501184271883525041785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105960668245695844700055713 79470501184271883525041785)
  ·
    refine ⟨59602875888203912643781339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79470501184271883525041785 59602875888203912643781339)
    ·
      refine ⟨89404313832305868965672009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59602875888203912643781339 89404313832305868965672009)
      ·
        refine ⟨67053235374229401724254007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89404313832305868965672009 67053235374229401724254007)
        ·
          refine ⟨100579853061344102586381011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67053235374229401724254007 100579853061344102586381011)
          ·
            refine ⟨150869779592016153879571517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100579853061344102586381011 150869779592016153879571517)
            ·
              refine ⟨56576167347006057704839319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 150869779592016153879571517 56576167347006057704839319)
              ·
                refine ⟨84864251020509086557258979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56576167347006057704839319 84864251020509086557258979)
                ·
                  refine ⟨127296376530763629835888469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 84864251020509086557258979 127296376530763629835888469)
                  ·
                    refine ⟨745877206234943143569659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 127296376530763629835888469 745877206234943143569659)
                    ·
                      rfl

theorem cell23_4357772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 1, 9].length) (baseStart_4357772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4357772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4357772 prefixEnd_4357772 := by exact prefixLift 4357772
  have htrace : WordTrace (prefixWord ++ tailWord_4357772) baseStart_4357772 baseEnd_4357772 := by
    simpa [prefixWord, tailWord_4357772, baseEnd_4357772] using wordTrace_append hprefix tailTrace_4357772
  have hstable : (prefixWord ++ tailWord_4357772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4357772).length < 2 ^ (prefixWord ++ tailWord_4357772).sum := by decide
  have hdescent : baseEnd_4357772 < baseStart_4357772 := by decide
  rcases family_descends (prefixWord ++ tailWord_4357772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4357779 : List Nat := [1, 1, 1, 2, 1, 2, 2, 1, 1, 9, 2]
def baseStart_4357779 : Nat := 118140960795 + 4357779 * 2 ^ 59
def prefixEnd_4357779 : Nat := 4983230072969 + 3 ^ 40 * 4357779 * 2
def baseEnd_4357779 : Nat := 2237635213069410903321445

theorem tailTrace_4357779 : CollatzResearch.WordTrace tailWord_4357779 prefixEnd_4357779 2237635213069410903321445 := by
  unfold tailWord_4357779
  simp only [CollatzResearch.WordTrace]
  refine ⟨158941257679518407245588391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105960838453012271497058927 158941257679518407245588391)
  ·
    refine ⟨238411886519277610868382587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158941257679518407245588391 238411886519277610868382587)
    ·
      refine ⟨357617829778916416302573881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 238411886519277610868382587 357617829778916416302573881)
      ·
        refine ⟨268213372334187312226930411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 357617829778916416302573881 268213372334187312226930411)
        ·
          refine ⟨402320058501280968340395617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 268213372334187312226930411 402320058501280968340395617)
          ·
            refine ⟨301740043875960726255296713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 402320058501280968340395617 301740043875960726255296713)
            ·
              refine ⟨226305032906970544691472535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 301740043875960726255296713 226305032906970544691472535)
              ·
                refine ⟨339457549360455817037208803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 226305032906970544691472535 339457549360455817037208803)
                ·
                  refine ⟨509186324040683725555813205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 339457549360455817037208803 509186324040683725555813205)
                  ·
                    refine ⟨2983513617425881204428593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 509186324040683725555813205 2983513617425881204428593)
                    ·
                      refine ⟨2237635213069410903321445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2983513617425881204428593 2237635213069410903321445)
                      ·
                        rfl

theorem cell23_4357779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 1, 1, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 1, 1, 9, 2].length) (baseStart_4357779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4357779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4357779 prefixEnd_4357779 := by exact prefixLift 4357779
  have htrace : WordTrace (prefixWord ++ tailWord_4357779) baseStart_4357779 baseEnd_4357779 := by
    simpa [prefixWord, tailWord_4357779, baseEnd_4357779] using wordTrace_append hprefix tailTrace_4357779
  have hstable : (prefixWord ++ tailWord_4357779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4357779).length < 2 ^ (prefixWord ++ tailWord_4357779).sum := by decide
  have hdescent : baseEnd_4357779 < baseStart_4357779 := by decide
  rcases family_descends (prefixWord ++ tailWord_4357779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4357820 : List Nat := [2, 2, 2, 3, 1, 4, 1, 2, 2, 1, 3]
def baseStart_4357820 : Nat := 118140960795 + 4357820 * 2 ^ 59
def prefixEnd_4357820 : Nat := 4983230072969 + 3 ^ 40 * 4357820 * 2
def baseEnd_4357820 : Nat := 2237656265776245242908757

theorem tailTrace_4357820 : CollatzResearch.WordTrace tailWord_4357820 prefixEnd_4357820 2237656265776245242908757 := by
  unfold tailWord_4357820
  simp only [CollatzResearch.WordTrace]
  refine ⟨79471376536184935623915457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105961835381579914165220609 79471376536184935623915457)
  ·
    refine ⟨59603532402138701717936593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79471376536184935623915457 59603532402138701717936593)
    ·
      refine ⟨44702649301604026288452445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59603532402138701717936593 44702649301604026288452445)
      ·
        refine ⟨16763493488101509858169667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44702649301604026288452445 16763493488101509858169667)
        ·
          refine ⟨25145240232152264787254501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16763493488101509858169667 25145240232152264787254501)
          ·
            refine ⟨4714732543528549647610219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25145240232152264787254501 4714732543528549647610219)
            ·
              refine ⟨7072098815292824471415329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4714732543528549647610219 7072098815292824471415329)
              ·
                refine ⟨5304074111469618353561497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7072098815292824471415329 5304074111469618353561497)
                ·
                  refine ⟨3978055583602213765171123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5304074111469618353561497 3978055583602213765171123)
                  ·
                    refine ⟨5967083375403320647756685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3978055583602213765171123 5967083375403320647756685)
                    ·
                      refine ⟨2237656265776245242908757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5967083375403320647756685 2237656265776245242908757)
                      ·
                        rfl

theorem cell23_4357820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 4, 1, 2, 2, 1, 3].length) (baseStart_4357820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4357820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4357820 prefixEnd_4357820 := by exact prefixLift 4357820
  have htrace : WordTrace (prefixWord ++ tailWord_4357820) baseStart_4357820 baseEnd_4357820 := by
    simpa [prefixWord, tailWord_4357820, baseEnd_4357820] using wordTrace_append hprefix tailTrace_4357820
  have hstable : (prefixWord ++ tailWord_4357820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4357820).length < 2 ^ (prefixWord ++ tailWord_4357820).sum := by decide
  have hdescent : baseEnd_4357820 < baseStart_4357820 := by decide
  rcases family_descends (prefixWord ++ tailWord_4357820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4357849 : List Nat := [1, 2, 1, 2, 3, 3, 2, 2, 7]
def baseStart_4357849 : Nat := 118140960795 + 4357849 * 2 ^ 59
def prefixEnd_4357849 : Nat := 4983230072969 + 3 ^ 40 * 4357849 * 2
def baseEnd_4357849 : Nat := 248630128523913958827347

theorem tailTrace_4357849 : CollatzResearch.WordTrace tailWord_4357849 prefixEnd_4357849 248630128523913958827347 := by
  unfold tailWord_4357849
  simp only [CollatzResearch.WordTrace]
  refine ⟨158943810789264809200636601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105962540526176539467091067 158943810789264809200636601)
  ·
    refine ⟨119207858091948606900477451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 158943810789264809200636601 119207858091948606900477451)
    ·
      refine ⟨178811787137922910350716177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119207858091948606900477451 178811787137922910350716177)
      ·
        refine ⟨134108840353442182763037133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 178811787137922910350716177 134108840353442182763037133)
        ·
          refine ⟨50290815132540818536138925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 134108840353442182763037133 50290815132540818536138925)
          ·
            refine ⟨18859055674702806951052097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50290815132540818536138925 18859055674702806951052097)
            ·
              refine ⟨14144291756027105213289073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18859055674702806951052097 14144291756027105213289073)
              ·
                refine ⟨10608218817020328909966805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14144291756027105213289073 10608218817020328909966805)
                ·
                  refine ⟨248630128523913958827347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10608218817020328909966805 248630128523913958827347)
                  ·
                    rfl

theorem cell23_4357849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 2, 2, 7].length) (baseStart_4357849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4357849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4357849 prefixEnd_4357849 := by exact prefixLift 4357849
  have htrace : WordTrace (prefixWord ++ tailWord_4357849) baseStart_4357849 baseEnd_4357849 := by
    simpa [prefixWord, tailWord_4357849, baseEnd_4357849] using wordTrace_append hprefix tailTrace_4357849
  have hstable : (prefixWord ++ tailWord_4357849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4357849).length < 2 ^ (prefixWord ++ tailWord_4357849).sum := by decide
  have hdescent : baseEnd_4357849 < baseStart_4357849 := by decide
  rcases family_descends (prefixWord ++ tailWord_4357849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4357863 : List Nat := [1, 1, 5, 4, 1, 1, 1, 1, 2, 1, 5]
def baseStart_4357863 : Nat := 118140960795 + 4357863 * 2 ^ 59
def prefixEnd_4357863 : Nat := 4983230072969 + 3 ^ 40 * 4357863 * 2
def baseEnd_4357863 : Nat := 2237678345444388574671059

theorem tailTrace_4357863 : CollatzResearch.WordTrace tailWord_4357863 prefixEnd_4357863 2237678345444388574671059 := by
  unfold tailWord_4357863
  simp only [CollatzResearch.WordTrace]
  refine ⟨158944321411214089591646243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105962880940809393061097495 158944321411214089591646243)
  ·
    refine ⟨238416482116821134387469365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158944321411214089591646243 238416482116821134387469365)
    ·
      refine ⟨22351545198451981348825253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 238416482116821134387469365 22351545198451981348825253)
      ·
        refine ⟨4190914724709746502904735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22351545198451981348825253 4190914724709746502904735)
        ·
          refine ⟨6286372087064619754357103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4190914724709746502904735 6286372087064619754357103)
          ·
            refine ⟨9429558130596929631535655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6286372087064619754357103 9429558130596929631535655)
            ·
              refine ⟨14144337195895394447303483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9429558130596929631535655 14144337195895394447303483)
              ·
                refine ⟨21216505793843091670955225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14144337195895394447303483 21216505793843091670955225)
                ·
                  refine ⟨15912379345382318753216419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21216505793843091670955225 15912379345382318753216419)
                  ·
                    refine ⟨23868569018073478129824629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15912379345382318753216419 23868569018073478129824629)
                    ·
                      refine ⟨2237678345444388574671059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23868569018073478129824629 2237678345444388574671059)
                      ·
                        rfl

theorem cell23_4357863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 1, 1, 2, 1, 5].length) (baseStart_4357863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4357863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4357863 prefixEnd_4357863 := by exact prefixLift 4357863
  have htrace : WordTrace (prefixWord ++ tailWord_4357863) baseStart_4357863 baseEnd_4357863 := by
    simpa [prefixWord, tailWord_4357863, baseEnd_4357863] using wordTrace_append hprefix tailTrace_4357863
  have hstable : (prefixWord ++ tailWord_4357863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4357863).length < 2 ^ (prefixWord ++ tailWord_4357863).sum := by decide
  have hdescent : baseEnd_4357863 < baseStart_4357863 := by decide
  rcases family_descends (prefixWord ++ tailWord_4357863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4357879 : List Nat := [1, 1, 3, 1, 1, 1, 5, 1, 4, 5]
def baseStart_4357879 : Nat := 118140960795 + 4357879 * 2 ^ 59
def prefixEnd_4357879 : Nat := 4983230072969 + 3 ^ 40 * 4357879 * 2
def baseEnd_4357879 : Nat := 745895520378286837356995

theorem tailTrace_4357879 : CollatzResearch.WordTrace tailWord_4357879 prefixEnd_4357879 745895520378286837356995 := by
  unfold tailWord_4357879
  simp only [CollatzResearch.WordTrace]
  refine ⟨158944904979156124324228691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105963269986104082882819127 158944904979156124324228691)
  ·
    refine ⟨238417357468734186486343037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158944904979156124324228691 238417357468734186486343037)
    ·
      refine ⟨89406509050775319932378639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 238417357468734186486343037 89406509050775319932378639)
      ·
        refine ⟨134109763576162979898567959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89406509050775319932378639 134109763576162979898567959)
        ·
          refine ⟨201164645364244469847851939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 134109763576162979898567959 201164645364244469847851939)
          ·
            refine ⟨301746968046366704771777909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 201164645364244469847851939 301746968046366704771777909)
            ·
              refine ⟨28288778254346878572354179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 301746968046366704771777909 28288778254346878572354179)
              ·
                refine ⟨42433167381520317858531269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28288778254346878572354179 42433167381520317858531269)
                ·
                  refine ⟨7956218884035059598474613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 42433167381520317858531269 7956218884035059598474613)
                  ·
                    refine ⟨745895520378286837356995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7956218884035059598474613 745895520378286837356995)
                    ·
                      rfl

theorem cell23_4357879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 1, 4, 5].length) (baseStart_4357879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4357879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4357879 prefixEnd_4357879 := by exact prefixLift 4357879
  have htrace : WordTrace (prefixWord ++ tailWord_4357879) baseStart_4357879 baseEnd_4357879 := by
    simpa [prefixWord, tailWord_4357879, baseEnd_4357879] using wordTrace_append hprefix tailTrace_4357879
  have hstable : (prefixWord ++ tailWord_4357879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4357879).length < 2 ^ (prefixWord ++ tailWord_4357879).sum := by decide
  have hdescent : baseEnd_4357879 < baseStart_4357879 := by decide
  rcases family_descends (prefixWord ++ tailWord_4357879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4357889 : List Nat := [1, 2, 4, 1, 1, 1, 3, 1, 1, 1, 7]
def baseStart_4357889 : Nat := 118140960795 + 4357889 * 2 ^ 59
def prefixEnd_4357889 : Nat := 4983230072969 + 3 ^ 40 * 4357889 * 2
def baseEnd_4357889 : Nat := 2237691695941405472945939

theorem tailTrace_4357889 : CollatzResearch.WordTrace tailWord_4357889 prefixEnd_4357889 2237691695941405472945939 := by
  unfold tailWord_4357889
  simp only [CollatzResearch.WordTrace]
  refine ⟨158945269709119896032092721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105963513139413264021395147 158945269709119896032092721)
  ·
    refine ⟨119208952281839922024069541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 158945269709119896032092721 119208952281839922024069541)
    ·
      refine ⟨22351678552844985379513039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 119208952281839922024069541 22351678552844985379513039)
      ·
        refine ⟨33527517829267478069269559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22351678552844985379513039 33527517829267478069269559)
        ·
          refine ⟨50291276743901217103904339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33527517829267478069269559 50291276743901217103904339)
          ·
            refine ⟨75436915115851825655856509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50291276743901217103904339 75436915115851825655856509)
            ·
              refine ⟨28288843168444434620946191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 75436915115851825655856509 28288843168444434620946191)
              ·
                refine ⟨42433264752666651931419287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28288843168444434620946191 42433264752666651931419287)
                ·
                  refine ⟨63649897128999977897128931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42433264752666651931419287 63649897128999977897128931)
                  ·
                    refine ⟨95474845693499966845693397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 63649897128999977897128931 95474845693499966845693397)
                    ·
                      refine ⟨2237691695941405472945939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 95474845693499966845693397 2237691695941405472945939)
                      ·
                        rfl

theorem cell23_4357889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 1, 1, 1, 7].length) (baseStart_4357889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4357889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4357889 prefixEnd_4357889 := by exact prefixLift 4357889
  have htrace : WordTrace (prefixWord ++ tailWord_4357889) baseStart_4357889 baseEnd_4357889 := by
    simpa [prefixWord, tailWord_4357889, baseEnd_4357889] using wordTrace_append hprefix tailTrace_4357889
  have hstable : (prefixWord ++ tailWord_4357889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4357889).length < 2 ^ (prefixWord ++ tailWord_4357889).sum := by decide
  have hdescent : baseEnd_4357889 < baseStart_4357889 := by decide
  rcases family_descends (prefixWord ++ tailWord_4357889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4357899 : List Nat := [1, 1, 1, 1, 5, 1, 2, 1, 3, 3, 4]
def baseStart_4357899 : Nat := 118140960795 + 4357899 * 2 ^ 59
def prefixEnd_4357899 : Nat := 4983230072969 + 3 ^ 40 * 4357899 * 2
def baseEnd_4357899 : Nat := 2237696830747950433820893

theorem tailTrace_4357899 : CollatzResearch.WordTrace tailWord_4357899 prefixEnd_4357899 2237696830747950433820893 := by
  unfold tailWord_4357899
  simp only [CollatzResearch.WordTrace]
  refine ⟨158945634439083667739956751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105963756292722445159971167 158945634439083667739956751)
  ·
    refine ⟨238418451658625501609935127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158945634439083667739956751 238418451658625501609935127)
    ·
      refine ⟨357627677487938252414902691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 238418451658625501609935127 357627677487938252414902691)
      ·
        refine ⟨536441516231907378622354037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 357627677487938252414902691 536441516231907378622354037)
        ·
          refine ⟨50291392146741316745845691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 536441516231907378622354037 50291392146741316745845691)
          ·
            refine ⟨75437088220111975118768537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50291392146741316745845691 75437088220111975118768537)
            ·
              refine ⟨56577816165083981339076403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75437088220111975118768537 56577816165083981339076403)
              ·
                refine ⟨84866724247625972008614605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56577816165083981339076403 84866724247625972008614605)
                ·
                  refine ⟨31825021592859739503230477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 84866724247625972008614605 31825021592859739503230477)
                  ·
                    refine ⟨11934383097322402313711429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 31825021592859739503230477 11934383097322402313711429)
                    ·
                      refine ⟨2237696830747950433820893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11934383097322402313711429 2237696830747950433820893)
                      ·
                        rfl

theorem cell23_4357899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 1, 3, 3, 4].length) (baseStart_4357899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4357899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4357899 prefixEnd_4357899 := by exact prefixLift 4357899
  have htrace : WordTrace (prefixWord ++ tailWord_4357899) baseStart_4357899 baseEnd_4357899 := by
    simpa [prefixWord, tailWord_4357899, baseEnd_4357899] using wordTrace_append hprefix tailTrace_4357899
  have hstable : (prefixWord ++ tailWord_4357899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4357899).length < 2 ^ (prefixWord ++ tailWord_4357899).sum := by decide
  have hdescent : baseEnd_4357899 < baseStart_4357899 := by decide
  rcases family_descends (prefixWord ++ tailWord_4357899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
